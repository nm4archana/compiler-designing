/****************************************************************************************************
 *
 * File: MIPS.scala
 * Generation of MIPS code from IR code
 *
 ****************************************************************************************************/

package edu.uta.spl

/** representation of a MIPS register */
case class Register ( reg: String ) {
    override def toString: String = reg
}


/** a pool of available registers */
class RegisterPool {

  val all_registers
        = List( "$t0", "$t1", "$t2", "$t3", "$t4", "$t5", "$t6", "$t7", "$t8", "$t9",
                "$s0", "$s1", "$s2", "$s3", "$s4", "$s5", "$s6", "$s7" )

  var available_registers: List[Register] = all_registers.map(Register)

  /** is register reg temporary? */
  def is_temporary ( reg: Register ): Boolean =
    reg match {
      case Register(n) => all_registers.contains(n)
    }

  /** return the next available temporary register */
  def get (): Register =
    available_registers match {
      case reg::rs
        => available_registers = rs
           reg
      case _ => throw new Error("*** Run out of registers")
    }

  /** recycle (put back into the register pool) the register reg (if is temporary) */
  def recycle ( reg: Register ) {
    if (available_registers.contains(reg))
       throw new Error("*** Register has already been recycled: "+reg)
    if (is_temporary(reg))
       available_registers = reg::available_registers
  }

  /** return the list of all temporary registers currently in use */
  def used (): List[Register] = {
    for ( reg <- all_registers if !available_registers.contains(Register(reg)) )
        yield Register(reg)
  }
}


abstract class MipsGenerator {
  def clear ()
  def emit ( e: IRstmt )
  def initialCode ()
}


class Mips extends MipsGenerator {
 
  /** emit a MIPS label */
  def mips_label ( s: String ) {
    SPL.out.println(s + ":")
  }

  /** emit MIPS code with no operands */
  def mips ( op: String ) {
    SPL.out.println("        " + op)
  }

  /** emit MIPS code with operands */
  def mips ( op: String, args: String ) {
    SPL.out.print("        " + op)
    for ( i <- op.length to 10)
        SPL.out.print(" ")
    SPL.out.println(args)
  }

  /** a pool of temporary registers */
  var rpool = new RegisterPool

  /** clear the register pool */
  def clear {
    rpool = new RegisterPool
  }

  var name_counter = 0

  /** generate a new  label name */
  def new_label (): String = {
    name_counter += 1
    "L_" + name_counter
  }

  /** generate MIPS code from the IR expression e and return the register that will hold the result */
  def emit ( e: IRexp ): Register = {
     // println(e)
    e match {

      case Mem(Binop("PLUS",Reg(r),IntValue(n)))
        => val reg = rpool.get()
           mips("lw",reg + ", " + n + "($" + r + ")")
           reg
       
              case IntValue(v) => 
              {
                  val r_v = rpool.get()
                  mips("li" , r_v + ", " + v)
                  r_v    
              }


      case Binop("AND",x,y)
        => val label = new_label()
           val left = emit(x)
           val reg = left

           mips("beq",left+", 0, "+label)
           val right = emit(y)
           mips("move",left+", "+right)
           mips_label(label)
           rpool.recycle(right)
           reg


      case Binop("PLUS",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("addu", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg

      case Binop("MINUS",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("subu", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg

      case Binop("TIMES",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("mul", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg


       case Binop("DIV",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("div", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg
    
     case Binop("MOD",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("rem", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg


     case Binop("EQ",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("seq", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg

    case Binop("LT",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("slt", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg


    case Binop("LEQ",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("sle", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg

    case Binop("GT",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("sgt", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg

    case Binop("GEQ",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("sge", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg

     case Binop("NEQ",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("sne", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg


     case Binop("OR",x,y)
        => 
           val left = emit(x)
           val right = emit(y)
           val reg = left
          
           mips("or", left + ", " + left + ", "+ right)
           rpool.recycle(right)
           reg


    case Unop("NOT",x)
    => 
      val left = emit(x)
      val reg = left
      mips("seq", left + ", " + left + ", "+ "0")
      reg

    case Unop("MINUS",x)
    => 
      val left = emit(x)
      val reg = left
      mips("neg", left + ", " + left)
      reg


        case Allocate(m) => 
        {
               val in_t = rpool.get()
               val t = emit(m)
  
                mips("li", in_t+", 4")
                mips("mul", t+", "+t+", "+in_t)
                mips("move", in_t+", $gp")
                mips("addu", "$gp, $gp, "+t)   
                rpool.recycle(t)
                in_t
    
      }

          case Mem(a) => 
          {
                val r_p = rpool.get()    
                val r_a = emit(a)    
     
              mips("lw", r_p+", ("+r_a+")")
              rpool.recycle(r_a)  
              r_p
          }

      case Call(f,sl,args)
        => { val used_regs = rpool.used()
           val size = (used_regs.length+args.length)*4
           /* allocate space for used temporary registers */
           if (size > 0)
              mips("subu","$sp, $sp, "+size)
           /* push the used temporary registers */
           var i = size
           for (r <- used_regs) {
               mips("sw",r + ", " + i + "($sp)")
               i -= 4
           }
           /* push arguments */
           i = args.length*4
           for (a <- args) {
              val reg = emit(a)
              mips("sw",reg + ", " + i + "($sp)")
              rpool.recycle(reg)
              i -= 4
           }
           /* set $v0 to be the static link */
           val sreg = emit(sl)
           mips("move","$v0, " + sreg)
           rpool.recycle(sreg)
           mips("jal",f)
           i = size
           /* pop the used temporary registers */
           for (r <- used_regs) {
              mips("lw",r + ", " + i + "($sp)")
              i -= 4
           }
           /* deallocate stack from args and used temporary registers */
           if (size > 0)
              mips("addu","$sp, $sp, "+size)
           val res = rpool.get()
           mips("move",res + ", $a0")
           /* You shouldn't just return $a0 */
           res
}
      /* PUT YOUR CODE HERE */
    
      case Reg(n) => 
      {
          val res = rpool.get()
          mips("move", res +", $"+n)
          res  
      }



      case _ => throw new Error("*** Unknown IR: "+e)
    }
  }

  /** generate MIPS code from the IR statement e */
  def emit ( e: IRstmt ) {
    // println(e)
    e match {

      case Move(Mem(Binop("PLUS",Reg(r),IntValue(n))),u)
        => val src = emit(u)
           mips("sw",src + ", " + n + "($" + r + ")")
           rpool.recycle(src)

     
    case Label(v) => 
    {
       mips_label(v)
    }


    case CJump(condition, exit_label)
     =>
        val rc = emit(condition)  
        mips("beq" , rc + ", 1, " + exit_label)


    case Jump(continue_label)
     =>
        mips("j" , continue_label)


    case Move(d, s) => 
    {    

      d match {

          case Mem(v) =>
          val rd = emit(v)
          val rs = emit(s)
          
          mips("sw", rs +", " + "(" + rd + ")")   
          rpool.recycle(rd)
           rpool.recycle(rs)

          case Reg(v) =>
            val rs = emit(s)
             mips("move", "$"+v+", "+rs)
            rpool.recycle(rs)

          case _ =>
          val rs = emit(s)
          val rd = emit(d)
          mips("move", rd + ", " + rs)   
          rpool.recycle(rd)
          rpool.recycle(rs)

      }
        
    }


    case Return() => 
    {
      mips("jr", "$ra")
    }

    
    case SystemCall("WRITE_STRING",a) 
    => 
    {
        a match 
        {
        case StringValue(str) =>
        {
          
             val l = new_label()
             val r = rpool.get()
                 
             mips(".data")
             mips(".align", "2")
                 
             mips_label(l)

             mips(".asciiz","\"" + str + "\"")
             mips(".text")
            
             mips("la", r + ", " + l)
             mips("move", "$a0, " + r)
             mips("li", "$v0, 4")        
             mips("syscall")     
            
         }

        case _ => 
        {
           //Do Nothing
        }

        } 
  }
      case SystemCall("WRITE_FLOAT",a) 
        => 
    {
      mips("move", "$a0, " + emit(a))
      mips("li", "$v0, 1")    
      mips("syscall")
    }

      case SystemCall("READ_INT",a) 
        => 
         a match 
        {
          case Mem(a_m) => 
          {
            mips("li", "$v0, 5")
            mips("syscall")
            val rs  = emit(a_m)
            mips("sw", "$v0, (" + rs + ")")    
            rpool.recycle(rs)
         }

          case _ => 
          {
           //Do Nothing
          }
      }

      case SystemCall("WRITE_INT",a) 
      => 

       val r_a = emit(a)

         mips("move", "$a0, " + r_a)
         mips("li", "$v0, 1")    
         mips("syscall")
         rpool.recycle(r_a)

     case SystemCall("WRITE_BOOL",a) 
      => 

       val r_a = emit(a)

         mips("move", "$a0, " + r_a)
         mips("li", "$v0, 1")    
         mips("syscall")
         rpool.recycle(r_a)


    case SystemCall("READ_BOOL",a) 
        => 
         a match 
        {
          case Mem(a) => 
          {
            mips("li", "$v0, 5")
            mips("syscall")
            val rs  = emit(a)
            mips("sw", "$v0, (" + rs + ")")    
            rpool.recycle(rs)
         }

          case _ => 
          {
           //Do Nothing
          }
      }


      case SystemCall("READ_FLOAT",a) 
        => 
         a match 
        {
          case Mem(a) => 
          {
            mips("li", "$v0, 5")
            mips("syscall")
            val rs  = emit(a)
            mips("sw", "$v0, (" + rs + ")")    
            rpool.recycle(rs)
         }

          case _ => 
          {
           //Do Nothing
          }
      }

        case SystemCall("READ_STRING",a) 
           => 

        {
            a match 
            {
             case Mem(a_m) => 
           {
            mips("li", "$v0, 5")
            mips("syscall")
            val rs  = emit(a_m)
            mips("sw", "$v0, (" + rs + ")")    
            rpool.recycle(rs)
          }

        case _ => 
        {
           //Do Nothing
        }
       }

    }
   
      case CallP(f,sl,args)
        => { val used_regs = rpool.used()
           val size = (used_regs.length+args.length)*4
           /* allocate space for used temporary registers */
           if (size > 0)
              mips("subu","$sp, $sp, "+size)
           /* push the used temporary registers */
           var i = size
           for (r <- used_regs) {
               mips("sw",r + ", " + i + "($sp)")
               i -= 4
           }
           /* push arguments */
           i = args.length*4
           for (a <- args) {
              val reg = emit(a)
              mips("sw",reg + ", " + i + "($sp)")
              rpool.recycle(reg)
              i -= 4
           }
           /* set $v0 to be the static link */
           val sreg = emit(sl)
           mips("move","$v0, " + sreg)
           rpool.recycle(sreg)
           mips("jal",f)
           i = size
           /* pop the used temporary registers */
           for (r <- used_regs) {
              mips("lw",r + ", " + i + "($sp)")
              i -= 4
           }
           /* deallocate stack from args and used temporary registers */
           if (size > 0)
              mips("addu","$sp, $sp, "+size)
           val res = rpool.get()
           mips("move",res + ", $a0")
         
}
    
      case _ => throw new Error("*** Unknown IR "+e)
    }
  }

  /** generate initial MIPS code from the program */
  def initialCode () {
    mips(".globl","main")
    mips(".data")
    mips_label("ENDL_")
    mips(".asciiz","\"\\n\"")
    mips(".text")
  }
}
