-- Prove2me | Definitions.Def_LogCostRAM_StructuredExecution
-- name    : LogCostRAM_StructuredExecution
-- status  : Definition
-- author  : @Soh Kumabe
-- created : 2026-11-26T17:08:35.427823+00:00
-- url     : https://prove2.me/theorems/9d278201-4bf7-42ab-9012-03ea17eba497
-- title:
--   Structured execution and binary data on a logarithmic-cost RAM
-- statement:
--   A store consists of a natural-valued memory and a binary output string. Structured commands compose arithmetic instructions, indirect memory accesses, tape reads, conditionals and loops. An execution relates an initial and final store to its primitive step count and enforces a predicate after each data instruction. Taking the predicate to bound all register values by their bit length gives the width invariant used in logarithmic-cost analysis.
--
--   The module defines the finite instruction compiler and data representations used by subroutines, including binary readers, packed bit strings, fixed-width numeric fields, bounded loops and the command that counts reports before visiting them.
-- source:
--   Auxiliary result for the log-cost RAM formalization of Proposition 4 in T. Koana and S. Kumabe, Breaking the 2^n barrier for directed hamiltonicity, STOC 2027 submission 811, PDF pp. 5 and 8–11. https://prove2.me/theorems/aa04b14a-8225-48c8-904c-8725ebdcac66

import Definitions.Def_TargetedSamplers_Machine

set_option autoImplicit false

section StructuredLogCostRAM

/-! Structured, relocatable programs for the Prove2Me log-cost machine. All costs count
the primitive steps of the published instruction list, including jumps. -/

namespace TargetedSamplers.Structured

structure Store where
  mem : ℕ → ℕ
  out : List Bool

def Store.write (s : Store) (d v : ℕ) : Store := {s with mem := Function.update s.mem d v}

def Store.Fits (s : Store) (width : ℕ) : Prop := ∀ a, (s.mem a).size ≤ width

inductive Op
  | const (d c : ℕ)
  | add (d a b : ℕ)
  | sub (d a b : ℕ)
  | load (d a : ℕ)
  | store (a b : ℕ)
  | input (d a : ℕ)
  | coin (d a : ℕ)
  | output (a : ℕ)

def Op.instruction : Op → Instr
  | .const d c => .const d c
  | .add d a b => .add d a b
  | .sub d a b => .monus d a b
  | .load d a => .load d a
  | .store a b => .store a b
  | .input d a => .readInput d a
  | .coin d a => .readCoin d a
  | .output a => .output a

def Op.eval (τ : Tapes) (s : Store) : Op → Store
  | .const d c => s.write d c
  | .add d a b => s.write d (s.mem a + s.mem b)
  | .sub d a b => s.write d (s.mem a - s.mem b)
  | .load d a => s.write d (s.mem (s.mem a))
  | .store a b => s.write (s.mem a) (s.mem b)
  | .input d a => s.write d (bitVal τ.input[s.mem a]?)
  | .coin d a => s.write d (bitVal τ.coins[s.mem a]?)
  | .output a => {s with out := s.out ++ [s.mem a != 0]}

inductive Cmd
  | skip
  | op (p : Op)
  | seq (first second : Cmd)
  | branch (a b : ℕ) (yes no : Cmd)
  | whileGt (a b : ℕ) (body : Cmd)

def Cmd.len : Cmd → ℕ
  | .skip => 0
  | .op _ => 1
  | .seq x y => x.len + y.len
  | .branch _ _ yes no => 1 + no.len + 1 + yes.len
  | .whileGt _ _ body => 1 + body.len + 1

def jump (target : ℕ) : Instr := .jle 0 0 target

def Cmd.compile (pc : ℕ) : Cmd → Program
  | .skip => []
  | .op p => [p.instruction]
  | .seq x y => x.compile pc ++ y.compile (pc + x.len)
  | .branch a b yes no =>
    let startYes := pc + 1 + no.len + 1
    [.jle a b startYes] ++ (no.compile (pc+1) ++ ([jump (startYes+yes.len)] ++ yes.compile startYes))
  | .whileGt a b body =>
    [.jle a b (pc+1+body.len+1)] ++ (body.compile (pc+1) ++ [jump pc])

/-- The predicate on stores is required after each primitive data instruction. It can express
a bit-width bound and is independent of branch counters and instruction addresses. -/
inductive Exec (τ : Tapes) (inv : Store → Prop) : Cmd → Store → Store → ℕ → Prop
  | skip (s) : Exec τ inv .skip s s 0
  | op (s p) : inv (p.eval τ s) → Exec τ inv (.op p) s (p.eval τ s) 1
  | seq {x y s m t u v} : Exec τ inv x s m u → Exec τ inv y m t v → Exec τ inv (.seq x y) s t (u+v)
  | yes {a b y n s t k} : s.mem a ≤ s.mem b → Exec τ inv y s t k →
      Exec τ inv (.branch a b y n) s t (1+k)
  | no {a b y n s t k} : ¬s.mem a ≤ s.mem b → Exec τ inv n s t k →
      Exec τ inv (.branch a b y n) s t (1+k+1)
  | done {a b body s} : s.mem a ≤ s.mem b → Exec τ inv (.whileGt a b body) s s 1
  | again {a b body s m t k j} : ¬s.mem a ≤ s.mem b → Exec τ inv body s m k →
      Exec τ inv (.whileGt a b body) m t j → Exec τ inv (.whileGt a b body) s t (1+k+1+j)

end TargetedSamplers.Structured

end StructuredLogCostRAM

section StructuredLogCostRun

namespace TargetedSamplers.Structured

def Cmd.program (c : Cmd) : Program := c.compile 0 ++ [.halt]

end TargetedSamplers.Structured

end StructuredLogCostRun

section StructuredLogCostFragments

namespace TargetedSamplers.Structured

/-- A loop-free fragment. Branches can contain arbitrary straight-line fragments. -/
inductive Fragment
  | skip
  | op (o : Op)
  | seq (x y : Fragment)
  | branch (a b : ℕ) (yes no : Fragment)

def Fragment.cmd : Fragment → Cmd
  | .skip => .skip
  | .op o => .op o
  | .seq x y => .seq x.cmd y.cmd
  | .branch a b yes no => .branch a b yes.cmd no.cmd

/-- Sequential execution of a finite table of fragments uses no extra primitive instructions. -/
def sequence : List Fragment → Fragment
  | [] => .skip
  | f :: fs => .seq f (sequence fs)

/-- A statically generated dispatch table for a natural-number tag. The scratch cell holds
the threshold during each comparison and the selected tag on entry to its branch. -/
def dispatch (key scratch : ℕ) : ℕ → List Cmd → Cmd
  | _, [] => .skip
  | base, c :: cs => .seq (.op (.const scratch base))
      (.branch key scratch c (dispatch key scratch (base+1) cs))

end TargetedSamplers.Structured

end StructuredLogCostFragments

section LogCostRAMRanges

namespace TargetedSamplers.Structured

/-- A half-open ascending loop. Its guard is a native conditional jump. -/
def forRange (ptr stop one : ℕ) (body : Cmd) : Cmd :=
  .whileGt stop ptr (.seq body (.op (.add ptr ptr one)))

/-- Number of words reported by the first k trials of a fixed tape. -/
def prefixReports (reports : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | k+1 => prefixReports reports k+reports k

end TargetedSamplers.Structured

end LogCostRAMRanges

section LogCostRAMBinaryRead

namespace TargetedSamplers.Structured.BinaryRead

def oneDigit (r : Fin 7 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.add (r 0) (r 0) (r 6)), .op (.input (r 4) (r 0)),
  .branch (r 4) (r 5) .skip (.op (.add (r 1) (r 1) (r 2))),
  .op (.add (r 2) (r 2) (r 2)), .op (.add (r 0) (r 0) (r 6)), .op (.input (r 3) (r 0))]

def marker : List Bool → ℕ
  | [] => 0
  | _ :: _ => 1

def scan (r : Fin 7 ↪ ℕ) := Cmd.whileGt (r 3) (r 5) (oneDigit r).cmd

def beginField (r : Fin 7 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.const (r 1) 0),.op (.const (r 2) 1),.op (.const (r 5) 0),.op (.const (r 6) 1),
  .op (.input (r 3) (r 0))]

def readField (r : Fin 7 ↪ ℕ) : Cmd := .seq (beginField r).cmd (.seq (scan r) (.op (.add (r 0) (r 0) (r 6))))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMBinaryRead

section LogCostRAMFieldArray

namespace TargetedSamplers.Structured.BinaryRead

def readFields (r : Fin 7 ↪ ℕ) (count dest : ℕ) : Cmd :=
  .whileGt count (r 5) (.seq (readField r) (.seq (.op (.store dest (r 1)))
    (.seq (.op (.add dest dest (r 6))) (.op (.sub count count (r 6))))))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMFieldArray

section LogCostRAMGraphHeader

namespace TargetedSamplers.Structured.BinaryRead

/-- A seven-register reader plus four registers holding n, m, the remaining count,
and the destination cursor. The layout can be moved beyond another routine's registers. -/
def digitRegs (r : Fin 11 ↪ ℕ) : Fin 7 ↪ ℕ where
  toFun i := r ⟨i.val,by have := i.isLt; omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun j : Fin 11 => j.val) (r.injective h))

/-- Keep m and set the number of following words to 3m+2 by four additions. -/
def countEdges (r : Fin 11 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.add (r 8) (r 1) (r 5)),.op (.add (r 9) (r 1) (r 1)),
  .op (.add (r 9) (r 9) (r 1)),.op (.add (r 9) (r 9) (r 6)),.op (.add (r 9) (r 9) (r 6))]

def graphHeader (r : Fin 11 ↪ ℕ) : Cmd :=
  .seq (readField (digitRegs r)) (.seq (.op (.add (r 7) (r 1) (r 5)))
    (.seq (readField (digitRegs r)) (.seq (countEdges r).cmd (readFields (digitRegs r) (r 9) (r 10)))))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMGraphHeader

section LogCostRAMCappedRead

namespace TargetedSamplers.Structured.BinaryRead

/-- The unsuccessful branch marks overflow and clears the loop guard. The place-value
comparison stops a huge canonical numeral before reading its high digits. -/
def cappedScan (r : Fin 7 ↪ ℕ) (limit fail : ℕ) : Cmd :=
  .whileGt (r 3) (r 5) (.branch (r 2) limit (oneDigit r).cmd
    (.seq (.op (.const (r 3) 0)) (.op (.const fail 1))))

/-- A canonical oversized numeral is reported as overflow after reading only the first
cap.size digits and one continuation marker. There is a separate final comparison for a
numeral of the same length whose value is above cap. -/
def readAtMost (r : Fin 7 ↪ ℕ) (limit fail : ℕ) : Cmd :=
  .seq (.op (.const fail 0)) (.seq (beginField r).cmd
    (.seq (cappedScan r limit fail) (.branch (r 1) limit .skip (.op (.const fail 1)))))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMCappedRead

section LogCostRAMSignedRead

namespace TargetedSamplers.Structured.BinaryRead

/-- On a negative sign the magnitude is never touched. For a nonnegative input only
those low digits permitted by the weight bound are visited. -/
def readSigned (r : Fin 7 ↪ ℕ) (limit fail : ℕ) : Cmd :=
  .seq (.op (.const (r 5) 0)) (.seq (.op (.input (r 3) (r 0)))
    (.branch (r 3) (r 5)
      (.seq (.op (.const (r 6) 1)) (.seq (.op (.add (r 0) (r 0) (r 6))) (readAtMost r limit fail)))
      (.op (.const fail 1))))

end TargetedSamplers.Structured.BinaryRead

end LogCostRAMSignedRead

section LogCostRAMStridedMax

namespace TargetedSamplers.Structured

/-- Registers: iteration count, bound, one, address, stride, temporary word, maximum, zero. -/
def maxBody (r : Fin 8 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.load (r 5) (r 3)),.branch (r 6) (r 5) (.op (.add (r 6) (r 5) (r 7))) .skip,
  .op (.add (r 3) (r 3) (r 4))]

def stridedMax (r : Fin 8 ↪ ℕ) : Cmd := forRange (r 0) (r 1) (r 2) (maxBody r).cmd

end TargetedSamplers.Structured

end LogCostRAMStridedMax

section LogCostRAMScale

namespace TargetedSamplers.Structured.Word

/-- For a multiplier that is already a polynomially bounded dimension, one loop suffices.
Registers 0 through 4 hold the countdown, addend, accumulator, zero, and one. -/
def addRepeatedly (r : Fin 5 ↪ ℕ) : Cmd := .whileGt (r 0) (r 3)
  (.seq (.op (.add (r 2) (r 2) (r 1))) (.op (.sub (r 0) (r 0) (r 4))))

end TargetedSamplers.Structured.Word

end LogCostRAMScale

section LogCostRAMCompare

namespace TargetedSamplers.Structured

def ifEqual (l r : ℕ) (yes no : Cmd) : Cmd := .branch l r (.branch r l yes no) no

def whenEqual (tests : List (ℕ × ℕ)) (body : Cmd) : Cmd :=
  match tests with
  | [] => body
  | (a,b)::rest => ifEqual a b (whenEqual rest body) .skip

end TargetedSamplers.Structured

end LogCostRAMCompare

section LogCostRAMTripleParity

namespace TargetedSamplers.Structured.TripleScan

abbrev Record := ℕ × ℕ × ℕ

def RecordsAt (s : Store) (base : ℕ) : List Record → Prop
  | [] => True
  | x::xs => s.mem base = x.1 ∧ s.mem (base+1) = x.2.1 ∧ s.mem (base+2) = x.2.2 ∧
      RecordsAt s (base+3) xs

/-- The data cursor, predicate accumulator and three transient fields are the only clobbers. -/
def untouched (r : Fin 10 ↪ ℕ) (a : ℕ) : Prop := a ≠ r 0 ∧ a ≠ r 6 ∧ a ≠ r 7 ∧ a ≠ r 8 ∧ a ≠ r 9

def readFields (r : Fin 10 ↪ ℕ) : Fragment := sequence [
  .op (.load (r 7) (r 0)),.op (.add (r 0) (r 0) (r 2)),
  .op (.load (r 8) (r 0)),.op (.add (r 0) (r 0) (r 2)),
  .op (.load (r 9) (r 0)),.op (.add (r 0) (r 0) (r 2))]

def tests (r : Fin 10 ↪ ℕ) := [(r 7,r 3),(r 8,r 4),(r 9,r 5)]

def toggle (r : Fin 10 ↪ ℕ) : Cmd := .op (.sub (r 6) (r 2) (r 6))

def loop (r : Fin 10 ↪ ℕ) : Cmd :=
  .whileGt (r 1) (r 0) (.seq (readFields r).cmd (whenEqual (tests r) (toggle r)))

end TargetedSamplers.Structured.TripleScan

end LogCostRAMTripleParity

section LogCostRAMFilter

namespace TargetedSamplers.Structured

/-- Clear the destination once for each forbidden equality. Only the destination is written. -/
def clearEqual (dst : ℕ) : List (ℕ × ℕ) → Cmd
  | [] => .skip
  | (a,b)::xs => .seq (ifEqual a b (.op (.const dst 0)) .skip) (clearEqual dst xs)

end TargetedSamplers.Structured

end LogCostRAMFilter

section LogCostRAMFold

namespace TargetedSamplers.Structured

inductive Reduction
  | sum
  | maximum

/-- Register order: index, exclusive limit, one, accumulator, value returned by the body, zero. -/
def Reduction.combine (op : Reduction) (r : Fin 6 ↪ ℕ) : Cmd :=
  match op with
  | .sum => .op (.add (r 3) (r 3) (r 4))
  | .maximum => .branch (r 3) (r 4) (.op (.add (r 3) (r 4) (r 5))) .skip

def Reduction.reduce (op : Reduction) (r : Fin 6 ↪ ℕ) (initial : ℕ) (body : Cmd) : Cmd :=
  .seq (.op (.const (r 0) 0)) (.seq (.op (.const (r 3) initial))
    (forRange (r 0) (r 1) (r 2) (.seq body (op.combine r))))

end TargetedSamplers.Structured

end LogCostRAMFold

section LogCostRAMDivisionStep

namespace TargetedSamplers.Structured.Word

/-- Registers hold the remaining dividend, divisor, quotient, scaled divisor, its power
of two, the next double, remainder plus one, and the constants zero and one. -/
def doublePair (r : Fin 9 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.add (r 3) (r 3) (r 3)),.op (.add (r 4) (r 4) (r 4)),.op (.add (r 5) (r 3) (r 3))]

def grow (r : Fin 9 ↪ ℕ) := Cmd.whileGt (r 6) (r 5) (doublePair r).cmd

end TargetedSamplers.Structured.Word

end LogCostRAMDivisionStep

section LogCostRAMDivision

namespace TargetedSamplers.Structured.Word

def startRound (r : Fin 9 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.add (r 3) (r 1) (r 7)),.op (.const (r 4) 1),.op (.add (r 5) (r 3) (r 3))]

def finishRound (r : Fin 9 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.sub (r 0) (r 0) (r 3)),.op (.add (r 2) (r 2) (r 4)),.op (.add (r 6) (r 0) (r 8))]

def quotientLoop (r : Fin 9 ↪ ℕ) := Cmd.whileGt (r 6) (r 1)
  (.seq (startRound r).cmd (.seq (grow r) (finishRound r).cmd))

def initDiv (r : Fin 9 ↪ ℕ) : Fragment := TargetedSamplers.Structured.sequence [
  .op (.const (r 7) 0),.op (.const (r 8) 1),.op (.const (r 2) 0),.op (.add (r 6) (r 0) (r 8))]

def divMod (r : Fin 9 ↪ ℕ) : Cmd := .seq (initDiv r).cmd (.branch (r 1) (r 7) .skip (quotientLoop r))

end TargetedSamplers.Structured.Word

end LogCostRAMDivision

section LogCostRAMMultiply

namespace TargetedSamplers.Structured.Word

 def startMultiple (r : Fin 9 ↪ ℕ) : Fragment := Structured.sequence
  [.op (.const (r 3) 1),.op (.add (r 4) (r 1) (r 7)),.op (.const (r 5) 2)]

def multiplyLoop (r : Fin 9 ↪ ℕ) := Cmd.whileGt (r 0) (r 7)
  (.seq (startMultiple r).cmd (.seq (grow r) (finishRound r).cmd))

def multiply (r : Fin 9 ↪ ℕ) := Cmd.seq (initDiv r).cmd (multiplyLoop r)

end TargetedSamplers.Structured.Word

end LogCostRAMMultiply

section LogCostRAMPower

namespace TargetedSamplers.Structured.Word

 def powerMulRegs (r : Fin 13 ↪ ℕ) : Fin 9 ↪ ℕ where
  toFun i := r ⟨i.val,by have := i.isLt; omega⟩
  inj' _ _ h := Fin.ext (congrArg (fun j : Fin 13 => j.val) (r.injective h))

 def initPower (r : Fin 13 ↪ ℕ) : Fragment := Structured.sequence
  [.op (.const (r 11) 0),.op (.const (r 12) 1),.op (.const (r 2) 1)]

 def powerOperands (r : Fin 13 ↪ ℕ) : Fragment := Structured.sequence
  [.op (.add (r 0) (r 9) (r 11)),.op (.add (r 1) (r 2) (r 11))]

def powerLoop (r : Fin 13 ↪ ℕ) := Cmd.whileGt (r 10) (r 11)
  (.seq (powerOperands r).cmd (.seq (multiply (powerMulRegs r)) (.op (.sub (r 10) (r 10) (r 12)))))

def power (r : Fin 13 ↪ ℕ) := Cmd.seq (initPower r).cmd (powerLoop r)

end TargetedSamplers.Structured.Word

end LogCostRAMPower

section LogCostRAMArithmetic

namespace TargetedSamplers.Structured.Word

/-- Arithmetic operations implemented on arbitrary-size words by fixed RAM programs. -/
inductive Arithmetic
  | mul | div | mod | pow
  deriving DecidableEq

def Arithmetic.value : Arithmetic → ℕ → ℕ → ℕ
  | .mul => (· * ·)
  | .div => (· / ·)
  | .mod => (· % ·)
  | .pow => (· ^ ·)

 def Arithmetic.leftReg : Arithmetic → ℕ | .pow => 9 | _ => 0

 def Arithmetic.rightReg : Arithmetic → ℕ | .pow => 10 | _ => 1

 def Arithmetic.outReg : Arithmetic → ℕ | .mod => 0 | _ => 2

 def Arithmetic.native : Arithmetic → Cmd
  | .mul => multiply Fin.valEmbedding
  | .div | .mod => divMod Fin.valEmbedding
  | .pow => power Fin.valEmbedding

/-- Arithmetic registers occupy a contiguous range above the thirteen scratch words
and a zero register. Operands may alias each other or the destination. -/
def cell (i : ℕ) := 14+i

 def loadArgs (p q l r : ℕ) : Fragment := Structured.sequence
  [.op (.const 13 0),.op (.add p (cell l) 13),.op (.add q (cell r) 13)]

def Arithmetic.call (op : Arithmetic) (d l r : ℕ) : Cmd :=
  .seq (loadArgs op.leftReg op.rightReg l r).cmd (.seq op.native (.op (.add (cell d) op.outReg 13)))

end TargetedSamplers.Structured.Word

end LogCostRAMArithmetic

section LogCostRAMArithmeticCircuit

namespace TargetedSamplers.Structured.Word

/-- One right-hand side in a finite sequence of assignments to logical registers. -/
inductive Expression
  | literal (n : ℕ)
  | add (left right : ℕ)
  | sub (left right : ℕ)
  | arithmetic (op : Arithmetic) (left right : ℕ)

structure Assignment where
  dst : ℕ
  rhs : Expression

def Expression.eval (v : ℕ → ℕ) : Expression → ℕ
  | .literal x => x
  | .add l r => v l+v r
  | .sub l r => v l-v r
  | .arithmetic op l r => op.value (v l) (v r)

def Assignment.cmd (a : Assignment) : Cmd :=
  match a.rhs with
  | .literal x => .op (.const (cell a.dst) x)
  | .add l r => .op (.add (cell a.dst) (cell l) (cell r))
  | .sub l r => .op (.sub (cell a.dst) (cell l) (cell r))
  | .arithmetic op l r => op.call a.dst l r

namespace Circuit

def cmd : List Assignment → Cmd
  | [] => .skip
  | a::as => .seq a.cmd (cmd as)

end Circuit

end TargetedSamplers.Structured.Word

end LogCostRAMArithmeticCircuit

section LogCostRAMTabulate

namespace TargetedSamplers.Structured

/-- Tabulate a bounded computation into consecutive RAM words. The current write
address is also the loop cursor and is available to the entry program. -/
def tabulate (ptr stop one value : ℕ) (entry : Cmd) : Cmd :=
  forRange ptr stop one (.seq entry (.op (.store ptr value)))

end TargetedSamplers.Structured

end LogCostRAMTabulate

section PackedBinaryStacks

namespace TargetedSamplers.Structured.BinaryStack

open Word

/-- A leading sentinel at the high end distinguishes the empty stack and a zero top bit. -/
def packed : List Bool → ℕ
  | [] => 1
  | b::bs => Nat.bit b (packed bs)

def push (k : ℕ) (b : Bool) : Cmd :=
  let twice := Cmd.op (.add (cell k) (cell k) (cell k))
  if b then .seq twice (.op (.add (cell k) (cell k) (cell 1))) else twice

end TargetedSamplers.Structured.BinaryStack

end PackedBinaryStacks

section PackedBitWriter

namespace TargetedSamplers.Structured.BinaryStack

open Word

/-- Prepend a fixed bit string to an already packed suffix, most distant bit first. -/
def prepend (dst : ℕ) : List Bool → Cmd
  | [] => .skip
  | a::as => .seq (prepend dst as) (push dst a)

end TargetedSamplers.Structured.BinaryStack

end PackedBitWriter

section SerializedTokenRAM

namespace TargetedSamplers.Structured.BinaryStack

open Word

/-- Cells 8..12 are respectively the packed suffix, read cursor, base, token and dispatch scratch. -/
def tokenStep (words : List (List Bool)) : Cmd :=
  .seq (.op (.sub (cell 9) (cell 9) (cell 1))) (.seq (.op (.load (cell 11) (cell 9)))
    (dispatch (cell 11) (cell 12) 0 (words.map (prepend 8))))

def encodeTokens (words : List (List Bool)) : Cmd := .whileGt (cell 9) (cell 10) (tokenStep words)

end TargetedSamplers.Structured.BinaryStack

end SerializedTokenRAM

section PackedMemoryBits

namespace TargetedSamplers.Structured.BinaryStack

open Word

 def binaryCode : List (List Bool) := [[false],[true]]

 def emptyWord : Fragment := Structured.sequence [
  .op (.const (cell 1) 1),.op (.const (cell 2) 2),.op (.const (cell 5) 0),.op (.const (cell 8) 1)]

def packMemory : Cmd := .seq emptyWord.cmd (encodeTokens binaryCode)

end TargetedSamplers.Structured.BinaryStack

end PackedMemoryBits

section LogCostRAMBankCircuit

namespace TargetedSamplers.Structured.Word.Circuit

def moveExpr (bank : ℕ) : Expression → Expression
  | .literal a => .literal a
  | .add l r => .add (bank+l) (bank+r)
  | .sub l r => .sub (bank+l) (bank+r)
  | .arithmetic op l r => .arithmetic op (bank+l) (bank+r)

def moveAssignment (bank : ℕ) (a : Assignment) : Assignment := ⟨bank+a.dst,moveExpr bank a.rhs⟩

def bankCmd (bank : ℕ) (as : List Assignment) := cmd (as.map (moveAssignment bank))

end TargetedSamplers.Structured.Word.Circuit

end LogCostRAMBankCircuit

section LogCostRAMCoinBlock

namespace TargetedSamplers.Structured.CoinRead

/-- Registers hold a descending cursor, its lower endpoint, one, the read symbol and the accumulator. -/
def digit (r : Fin 5 ↪ ℕ) : Fragment := sequence [
  .op (.sub (r 0) (r 0) (r 2)),.op (.coin (r 3) (r 0)),.op (.add (r 4) (r 4) (r 4)),
  .branch (r 3) (r 2) (.branch (r 2) (r 3) (.op (.add (r 4) (r 4) (r 2))) .skip) .skip]

def loop (r : Fin 5 ↪ ℕ) : Cmd := .whileGt (r 0) (r 1) (digit r).cmd

end TargetedSamplers.Structured.CoinRead

end LogCostRAMCoinBlock

section LogCostRAMCeilLog

namespace TargetedSamplers.Structured

/-- Registers hold the input cardinality, the current power of two, its exponent, and one. -/
def ceilLogLoop (r : Fin 4 ↪ ℕ) : Cmd := .whileGt (r 0) (r 1)
  (.seq (.op (.add (r 1) (r 1) (r 1))) (.op (.add (r 2) (r 2) (r 3))))

def ceilLog (r : Fin 4 ↪ ℕ) : Cmd := .seq
  (Structured.sequence [.op (.const (r 1) 1),.op (.const (r 2) 0),.op (.const (r 3) 1)]).cmd (ceilLogLoop r)

end TargetedSamplers.Structured

end LogCostRAMCeilLog

section LogCostRAMMarkWord

namespace TargetedSamplers.Structured.BinaryStack

/-- The words of length q are the candidate subsets of that instance. -/
def tracksWords (q base : ℕ) (seen : Finset (List Bool)) (s : Store) : Prop :=
  ∀ xs : List Bool, xs.length=q → s.mem (base+packed xs) = if xs ∈ seen then 1 else 0

/-- The registers contain the sparse base, the current packed subset and one.
The fragment returns the old membership flag and inserts the subset. -/
def markWord (r : Fin 5 ↪ ℕ) : Fragment := Structured.sequence [
  .op (.add (r 3) (r 0) (r 1)),.op (.load (r 4) (r 3)),.op (.store (r 3) (r 2))]

end TargetedSamplers.Structured.BinaryStack

end LogCostRAMMarkWord

section LogCostRAMIndexedQuery

namespace TargetedSamplers.Structured

/-- Write the relative array index to a query register before invoking a fixed kernel. -/
def indexedQueries (ptr stop one value src index : ℕ) (kernel : Cmd) : Cmd :=
  tabulate ptr stop one value (.seq (.op (.sub index ptr src)) kernel)

end TargetedSamplers.Structured

end LogCostRAMIndexedQuery

section MultitapeControl

/-! Compile a finite transition table reading a fixed tuple of ternary tape symbols. -/

namespace TargetedSamplers.Structured

def symbolCode : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

structure Reader where
  tag : ℕ
  zero : ℕ
  one : ℕ
  zero_ne : zero ≠ tag
  one_ne : one ≠ tag

/-- At each tape, load its head symbol indirectly and branch on the three possible values.
All branches are built once when the finite program is constructed. -/
def Reader.symbolTree (R : Reader) : {k : ℕ} → (Fin k → ℕ) → ((Fin k → Option Bool) → Cmd) → Cmd
  | 0, _, next => next Fin.elim0
  | k+1, pos, next =>
    let branch (x : Option Bool) := R.symbolTree (k := k) (fun i => pos i.succ) (fun xs => next (Fin.cons x xs))
    .seq (.op (.load R.tag (pos 0)))
      (.branch R.tag R.zero (branch none) (.branch R.tag R.one (branch (some false)) (branch (some true))))

end TargetedSamplers.Structured

end MultitapeControl

section LogCostRAMRankCursor

namespace TargetedSamplers.Structured.RankedPrefix

open BinaryStack

def enterFalse (bank : ℕ) : Fragment := Structured.sequence [
  .op (.sub (bank+6) (bank+6) (bank+15)),.op (.sub (bank+9) (bank+9) (bank+15)),
  .op (.add (bank+18) (bank+18) (bank+18)), .op (.store (bank+9) (bank+15))]

def useTrue (bank : ℕ) : Fragment := Structured.sequence [
  .op (.sub (bank+17) (bank+17) 4),.op (.add (bank+18) (bank+18) (bank+15)),
  .op (.store (bank+9) (bank+16))]

end TargetedSamplers.Structured.RankedPrefix

end LogCostRAMRankCursor

section LogCostRAMReportedCounts

namespace TargetedSamplers.Structured

/-- Count every trial before admitting the enumeration pass. Registers hold the
trial cursor, trial limit, one, the running total and the latest count. -/
def scanCounts (r : Fin 5 ↪ ℕ) (query : Cmd) : Cmd :=
  forRange (r 0) (r 1) (r 2) (.seq query (.op (.add (r 3) (r 3) (r 4))))

end TargetedSamplers.Structured

end LogCostRAMReportedCounts

section LogCostRAMReportedWords

namespace TargetedSamplers.Structured

def applyPrefix {X : Type*} (f : ℕ → X → X) : ℕ → X → X
  | 0,x => x
  | k+1,x => f k (applyPrefix f k x)

/-- The outer counter ranges over trials. The inner counter ranges over just the
solutions found in the current trial and shares the same verified query routine. -/
def scanReportedWords (r : Fin 5 ↪ ℕ) (query visit : Cmd) : Cmd :=
  forRange (r 0) (r 1) (r 2) (.seq query (.seq (.op (.const (r 3) 0)) (forRange (r 3) (r 4) (r 2) visit)))

end TargetedSamplers.Structured

end LogCostRAMReportedWords

section LogCostRAMCappedReports

namespace TargetedSamplers.Structured

/-- Count the reports, compare against the cap, and only then enumerate them.
The total register is available as the rank register during the second pass. -/
def cappedReports (r : Fin 5 ↪ ℕ) (cap zero result : ℕ) (query visit : Cmd) : Cmd :=
  .seq (scanCounts r query) (.branch (r 3) cap
    (.seq (.op (.const (r 0) 0)) (.seq (scanReportedWords r query visit) (.op (.output result))))
    (.op (.output zero)))

end TargetedSamplers.Structured

end LogCostRAMCappedReports

section HamiltonianCappedRun

namespace TargetedSamplers.Structured

def insertAt {α : Type*} [DecidableEq α] [Inhabited α] (xs : List α) (i : ℕ) (seen : Finset α) :=
  insert (xs[i]?.getD default) seen

end TargetedSamplers.Structured

end HamiltonianCappedRun

section NativeNumericFields

namespace TargetedSamplers.NumericFields

/-- Fixed-width fields are stored least significant first, with a final sentinel.
The number of fields is fixed by each call site. -/
def join (radix : ℕ) : List ℕ → ℕ → ℕ
  | [],top => top
  | x::xs,top => x+radix*join radix xs top

def pack (width : ℕ) (xs : List ℕ) := join (2^width) xs 1

end TargetedSamplers.NumericFields

end NativeNumericFields


