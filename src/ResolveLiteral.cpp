#include "../h/Action.h"
#include "../h/Token.h"
#include "../h/ErrorHandler.h"
#include "../h/Namespace.h"

extern Namespace globalNamespace;

Action resolveIntLiteral(Token token, Type type)
{
	string in=token->getText();

	int val=0;

	for (auto i=in.begin(); i!=in.end(); ++i)
	{
		if (*i<'0' || *i>'9')
		{
			error.log(string() + "bad character '" + *i + "' found in number '" + in + "'", SOURCE_ERROR, token);
			return nullptr;
		}

		val=val*10+(*i-'0');
	}

	if (type==Bool)
	{
		bool out=(val!=0);
		return constGetAction(&out, type, token->getText(), globalNamespace);
	}
	else
	{
		int out=val;
		return constGetAction(&out, type, token->getText(), globalNamespace);
	}
}

Action resolveDubLiteral(Token token)
{
	string in=token->getText();

	double val=0;
	int pointPos=0;

	for (auto i=in.begin(); i!=in.end(); ++i)
	{
		if (*i=='.' || *i=='_')
		{
			if (pointPos==0)
			{
				pointPos=10;
			}
			else
			{
				error.log(string() + "multiple decimal points found in number '" + in + "'", SOURCE_ERROR, token);
				return voidAction;
			}
		}
		else if (*i>='0' && *i<='9')
		{
			if (pointPos)
			{
				val+=(double)(*i-'0')/pointPos;
				pointPos*=10;
			}
			else
			{
				val=val*10+(*i-'0');
			}
		}
		else
		{
			error.log(string() + "bad character '" + *i + "' found in number '" + in + "'", SOURCE_ERROR, token);
			return voidAction;
		}
	}

	double out=val;
	return constGetAction(&out, Inombolo, token->getText(), globalNamespace);
}

string pncnStr2CppStr(void* obj);
void* cppStr2PncnStr(string cpp);

Action resolveStringLiteral(Token token)
{
	string text=token->getText();

	//this nonesens is required because my lexer is shit and includes the first quote but not the last one
	//instead of hardcoding that in, I figured I'd make it flexable so I don't break everthing when I fix the lexer

	while (text.size()>0 && text[0]=='"')
		text=text.substr(1, string::npos);

	while (text.size()>0 && text[text.size()-1]=='"')
		text=text.substr(0, text.size()-1);

	void* obj=cppStr2PncnStr(text);

	return constGetAction(obj, Amabala, "\""+text+"\"", globalNamespace);
}

Action resolveLiteral(Token token)
{
	if (token->getType()==TokenData::STRING_LITERAL)
	{
		return resolveStringLiteral(token);
	}

	if (token->getType()!=TokenData::LITERAL)
	{
		throw NdexcodeError(FUNC+" called on token that is not a literal", INTERNAL_ERROR, token);
	}

	string in=token->getText();

	if (in.empty())
		return nullptr;

	//bool floatingPoint=false;

	Type type=Unknown;

	if (in.empty())
	{
		error.log("tried to make literal with empty string", INTERNAL_ERROR, token);
	}

	if ((in[0]>='0' && in[0]<='9') || in[0]=='.')
	{
		type=Inani;

		for (auto i=in.begin(); i!=in.end(); ++i)
		{
			if (*i=='.' || *i=='_')
			{
				type=Inombolo;
				break;
			}
		}

		if (in.back()=='d' || in.back()=='f')
		{
			type=Inombolo;
			in.pop_back();
		}
		else if (in.back()=='i')
		{
			type=Inani;
			in.pop_back();
		}
		else if (in.back()=='b')
		{
			type=Bool;
			in.pop_back();
		}
	}

	if (type==Inani)
	{
		return resolveIntLiteral(token, type);
	}
	else if (type==Inombolo) //floating point
	{
		return resolveDubLiteral(token);
	}
	else
	{
		throw NdexcodeError("tried to make literal with invalid type of " + type->getString(), INTERNAL_ERROR, token);
	}
}


