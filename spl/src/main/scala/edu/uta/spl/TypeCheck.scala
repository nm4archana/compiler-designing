

package edu.uta.spl

abstract class TypeChecker {
  var trace_typecheck = false

  /** symbol table to store SPL declarations */
  var st = new SymbolTable

  /** Type declaration **/

  def expandType ( tp: Type ): Type
  def typecheck ( e: Expr ): Type
  def typecheck ( e: Lvalue ): Type
  def typecheck ( e: Stmt, expected_type: Type )
  def typecheck ( e: Definition )
  def typecheck ( e: Program )
}


class TypeCheck extends TypeChecker {

  /** typechecking error */
  def error ( msg: String ): Type = {
    System.err.println("*** Typechecking Error: "+msg)
    System.err.println("*** Symbol Table: "+st)
    System.exit(1)
    null
  }

  /** if tp is a named type, expand it */
  def expandType ( tp: Type ): Type =
    tp match {
      case NamedType(nm)
        => st.lookup(nm) match {
          case Some(TypeDeclaration(t))
              => expandType(t)
          case _ => error("Undeclared type: "+tp)
        }
      case _ => tp
  }

  /** returns true if the types tp1 and tp2 are equal under structural equivalence */
  def typeEquivalence ( tp1: Type, tp2: Type ): Boolean =
    if (tp1 == tp2 || tp1.isInstanceOf[AnyType] || tp2.isInstanceOf[AnyType])
      true
    else expandType(tp1) match {
      case ArrayType(t1)
        => expandType(tp2) match {
              case ArrayType(t2)
                => typeEquivalence(t1,t2)
              case _ => false
           }
      case RecordType(fs1)
        => expandType(tp2) match {
              case RecordType(fs2)
                => fs1.length == fs2.length &&
                   (fs1 zip fs2).map{ case (Bind(v1,t1),Bind(v2,t2))
                                        => v1==v2 && typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case TupleType(ts1)
        => expandType(tp2) match {
              case TupleType(ts2)
                => ts1.length == ts2.length &&
                   (ts1 zip ts2).map{ case (t1,t2) => typeEquivalence(t1,t2) }
                                .reduce(_&&_)
              case _ => false
           }
      case _
        => tp2 match {
             case NamedType(n) => typeEquivalence(tp1,expandType(tp2))
             case _ => false
           }
    }

  /* tracing level */
  var level: Int = -1

  /** trace typechecking */
  def trace[T] ( e: Any, result: => T ): T = {
    if (trace_typecheck) {
       level += 1
       println(" "*(3*level)+"** "+e)
    }
    val res = result
    if (trace_typecheck) {
       print(" "*(3*level))
       if (e.isInstanceOf[Stmt] || e.isInstanceOf[Definition])
          println("->")
       else println("-> "+res)
       level -= 1
    }
    res
  }

  /** typecheck an expression AST */
  def typecheck ( e: Expr ): Type =
    trace(e,e match {
      case BinOpExp(op,l,r)
        => val ltp = typecheck(l)
           val rtp = typecheck(r)
           if (!typeEquivalence(ltp,rtp))
              error("Incompatible types in binary operation: "+e)
           else if (op.equals("and") || op.equals("or"))
                   if (typeEquivalence(ltp,BooleanType()))
                      ltp
                   else error("AND/OR operation can only be applied to booleans: "+e)
           else if (op.equals("eq") || op.equals("neq"))
                   BooleanType()
           else if (!typeEquivalence(ltp,IntType()) && !typeEquivalence(ltp,FloatType()))
                   error("Binary arithmetic operations can only be applied to integer or real numbers: "+e)
           else if (op.equals("gt") || op.equals("lt") || op.equals("geq") || op.equals("leq"))
                   BooleanType()

           else ltp

      /* PUT YOUR CODE HERE */
      
      case IntConst(n)
      => IntType()

      case FloatConst(n)
      => FloatType()

      case StringConst(n)
      => StringType()

      case BooleanConst(n)
      => BooleanType()

     case LvalExp(l)
     => typecheck(l)

     case NullExp()
     => AnyType()

     case UnOpExp(op,opr)
     => val tp = typecheck(opr)
            if (op.equals("minus") && !typeEquivalence(tp,IntType()) && !typeEquivalence(tp,FloatType()))
               error("Unary MINUS operation can only be applied to integer or real numbers: "+e)
            else if (op.equals("not") && !typeEquivalence(tp,BooleanType()))
               error("Unary NOT operation can only be applied to booleans "+e)
            else
               tp
     
     case CallExp(name,aList)
        =>
        st.lookup(name) match {
          case Some(FuncDeclaration(t,pList,_,_,_)) 
             => if (aList.length != pList.length)
                    error("Formal parameters length does not match actual parameters length")
  
                    t

          case Some(_) => error(name + "is not a function")
          case None => error("Undefined function: "+name)
     }


    case ArrayGen(len,e)
     => val tp = typecheck(len)
        if(!typeEquivalence(tp,IntType()))
           error("The length initialization of array must be an integer "+len)
           typecheck(e)


    
      case TupleExp(e)
      => 
      var type_list: List[Type] = List()
      for( a <- e)
      {
        type_list = type_list :+ typecheck(a)

      }
      TupleType(type_list)
      

      case RecordExp(e)
      =>
      var type_list: List[Bind[Type]] = List()
      for(Bind(e1,e2) <- e)
      {
        //typecheck(e2)
        type_list = type_list :+ Bind(e1,typecheck(e2))
      }
      RecordType(type_list)

          
      case ArrayExp(e)
      => 
      var l = List[Type]()
      for( a <- e)
      {
       a match { 
        case(e) => {
         // typecheck(a)
          l =  l :+ typecheck(a)
        }
      }
    }
      ArrayType(l.head) 
 
      
      
      case _ => throw new Error("Wrong expression: "+e)
    } 


    )

  /** typecheck an Lvalue AST */
  def typecheck ( e: Lvalue ): Type =
    trace(e,e match {

      case Var(name)
        => st.lookup(name) match {
              case Some(VarDeclaration(t,_,_)) => t
              case Some(_) => error(name+" is not a variable")
              case None => error("Undefined variable: "+name)
        }

      /* PUT YOUR CODE HERE */

      case ArrayDeref(a1,i)
       => var tp1 = typecheck(i)
          if(!typeEquivalence(tp1,IntType()))
           error("Array Index should be an Integer" + i)
            var atp = typecheck(a1)
              expandType(atp) match 
              {
                 case ArrayType(s) => expandType(s)
                 case _ => atp
              }
                

       case RecordDeref(e1,a)
      => var atp = typecheck(e1)
             atp match {
         case RecordType(l) => 

          var type_list: List[Type] = List()

          for(Bind(a1,a2) <- l) {
                     type_list =  type_list :+ expandType(a2)
                    }
                  
               type_list.head  

           case _  => atp 
                  
       }
     

    case TupleDeref(a1,i)
       => 
            val atp = typecheck(a1)
              expandType(atp) match 
              {
                 case TupleType(s) => expandType(atp)
                 case _ => atp
              }
            
      case _ => throw new Error("Wrong lvalue: "+e)
    } )


  /** typecheck a statement AST using the expected type of the return value from the current function */
  def typecheck ( e: Stmt, expected_type: Type ) {
    trace(e,e match {

      case AssignSt(d,s)
        => if (!typeEquivalence(typecheck(d),typecheck(s)))
              error("Incompatible types in assignment: "+ ",  "+d+",  "+s)

      /* PUT YOUR CODE HERE */

        case CallSt(name,aList)
        =>  st.lookup(name) match {
          case Some(FuncDeclaration(t,pList,_,_,_)) 
             => if (aList.length != pList.length)
                    error("Formal parameters length does not match actual parameters length")

              t

          case Some(_) => error(name + "is not a Call Statemnt")
          case None => error("Undefined Statement: "+name)
        }

      case ReadSt(lList)
      => lList.foreach(typecheck(_))


       case PrintSt(le)
       =>  le.foreach(typecheck(_))


     case IfSt(c,th,el)
        => val tp = typecheck(c)
       if (!typeEquivalence(tp,BooleanType ()))
          error("IF condition does not return a boolean "+c)
          if(el!=null)
          typecheck(th, AnyType())
              

       case WhileSt(c,b)
        => if (!typeEquivalence(typecheck(c),BooleanType()))
              error("WHILE condition does not return a boolean "+c)
           typecheck(b, AnyType())

       case LoopSt(b)
       => typecheck(b, AnyType())

       case ForSt(v,i,s,inc,b)
       => st.begin_scope()
        st.insert(v, VarDeclaration(IntType(),0,0))
        val tp1 = typecheck(i)
        if(!typeEquivalence(tp1,IntType()))
           error("The starting value for FOR loop should be an Integer" + i)
        val tp2 = typecheck(s)
         if(!typeEquivalence(tp2,IntType()))
           error("The ending value for FOR loop should be an Integer" + s)
         typecheck(inc) 
         typecheck(b, AnyType()) 
         st.end_scope()

      case ExitSt()
       =>
       
      case ReturnValueSt(e)
       => typecheck(e)

       case ReturnSt()
       => 

       case BlockSt(ld,ls)
       =>  st.begin_scope()

           for(a <- ld)
           {
           typecheck(a)
           }
           for(b <- ls)
           {
           typecheck(b,AnyType())
         }
           st.end_scope()

      case _ => throw new Error("Wrong statement: "+e)
    } )
  }

  /** typecheck a definition */
  def typecheck ( e: Definition ) {
    trace(e,e match {
      case FuncDef(f,ps,ot,b)
        => st.insert(f,FuncDeclaration(ot,ps,"",0,0))
           st.begin_scope()
           ps.foreach{ case Bind(v,tp) => st.insert(v,VarDeclaration(tp,0,0)) }
           typecheck(b,ot)
           st.end_scope()

      /* PUT YOUR CODE HERE */

      case VarDef(name,ot,e)
               =>
                st.begin_scope()
               var tp = typecheck(e)
               st.insert(name,VarDeclaration(tp,0,0)) 

      case TypeDef(name,ot)
        =>  st.begin_scope()
            st.insert(name,TypeDeclaration(ot))




      case _ => throw new Error("Wrong statement: "+e)
 
    } )
  }

  /** typecheck the main program */
  def typecheck ( e: Program ) {
    typecheck(e.body,NoType())
  }
}
