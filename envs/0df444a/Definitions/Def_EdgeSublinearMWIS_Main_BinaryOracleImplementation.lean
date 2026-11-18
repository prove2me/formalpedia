-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_BinaryOracleImplementation
-- name    : EdgeSublinearMWIS_Main_BinaryOracleImplementation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T05:55:28.200213+00:00
-- url     : https://prove2.me/theorems/f49b19f3-1cbc-4856-9d1d-e5c75b4f11f3
-- title:
--   Finite binary-hull oracle: word implementation and state predicates
-- statement:
--   This module specifies the finite word implementation used to find a point in a Boolean-vertex convex hull from a transcript of rational separating cuts.
--
--   The input gives a dimension $N$ and a finite list of rational halfspaces. The state stores a current dimension, a rational affine map into the original space, and a rounded rational ellipsoid. Thin phases invoke an integer lattice reduction routine and eliminate one affine coordinate. The fixed query budget is
--   $$Q(N+1)=203(N+1)^5.$$
--   Output is either a rational query vector or a rejection flag.
--
--   The module contains the word arithmetic, parsers, matrix routines, fixed stack routines, state representations, and predicates used to express the invariant. Arithmetic constructor identities needed to form these routines are included. The transcript invariant, rejection soundness, termination argument, and polynomial execution estimates remain separate theorem obligations.
--
--   This interface allows the geometric correctness and execution-bound proofs to share the same implementation definitions.
-- source:
--   Bonnet--Chang, QPTAS for Max Weight Independent Set in Graphs with Strongly Edge-Sublinear Separators, Theorem 2 and Section 5 exact-feasibility step, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf. Rounded rational updates follow the Apache-2.0 source https://github.com/EdouardBonnet/lax-109476/tree/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs (RationalRounding, EllipsoidSequence, EllipsoidStateSize). Integer recovery is the explicit lattice-based implementation supporting EdgeSublinearMWIS.Main.exact_binary_oracle_feasibility.

import Definitions.Def_EdgeSublinearMWIS_Main_RationalEllipsoids
import Mathlib.Data.Nat.Bits
import Mathlib.Tactic
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_OAIThreeMachineSched02
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedExecution
import Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction
import Definitions.Def_LLLFactor_RedBasis_Setting
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Definitions.Def_LLLFactor_Reduction_Algorithm
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib
import Definitions.Def_EdgeSublinearMWIS_Main_Ellipsoid
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Algebra.Polynomial.Eval.Defs

-- Solutions.RawBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def value : List Bool → ℕ
   | [] => 0
   | b::L => b.toNat+2*value L
 def increment : List Bool → List Bool
   | [] => [true]
   | false::L => true::L
   | true::L => false::increment L

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryAdder
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open RawStack
abbrev State := List Bool × (List Bool × (Bool × List Bool))
 def step (s : State) : State :=
   let a := s.1.headD false
   let b := s.2.1.headD false
   let c := s.2.2.1
   (s.1.tail,(s.2.1.tail,((a && b)||(a && c)||(b && c),(xor (xor a b) c)::s.2.2.2)))
 def word (A B : List Bool) : List Bool :=
   ((step^[A.length+B.length+1]) (A,(B,(false,[])))).2.2.2.reverse

 theorem value_head_tail (A : List Bool) : value A=(A.headD false).toNat+2*value A.tail := by
   cases A <;> rfl

 theorem value_append (A B : List Bool) : value (A++B)=value A+2^A.length*value B := by
   induction A with
   | nil => simp [value]
   | cons a A ih => simp [value,ih,pow_succ]; ring

 theorem full_adder (a b c : Bool) :
    (xor (xor a b) c).toNat+2*((a && b)||(a && c)||(b && c)).toNat=a.toNat+b.toNat+c.toNat := by
   cases a <;> cases b <;> cases c <;> decide

 theorem step_value (s : State) :
    value (step s).2.2.2.reverse+2^(step s).2.2.2.length*(value (step s).1+value (step s).2.1+(step s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat) := by
   rcases s with ⟨A,B,c,R⟩
   have ha := value_head_tail A
   have hb := value_head_tail B
   have hf := full_adder (A.headD false) (B.headD false) c
   simp only [step,List.reverse_cons,value_append,List.length_reverse,List.length_cons,pow_succ,value,List.length_nil,Nat.mul_zero,Nat.add_zero]
   rw [ha,hb]
   have hfm := congrArg (fun z : ℕ => 2^R.length*z) hf
   nlinarith only [hfm]

 theorem iter_value (s : State) (t : ℕ) :
    value ((step^[t]) s).2.2.2.reverse+2^((step^[t]) s).2.2.2.length*(value ((step^[t]) s).1+value ((step^[t]) s).2.1+((step^[t]) s).2.2.1.toNat)=
      value s.2.2.2.reverse+2^s.2.2.2.length*(value s.1+value s.2.1+s.2.2.1.toNat) := by
   induction t with
   | zero => rfl
   | succ t ih => rw [Function.iterate_succ_apply']; exact (step_value ((step^[t]) s)).trans ih

 theorem iter_lists (s : State) (t : ℕ) :
    ((step^[t]) s).1=s.1.drop t ∧ ((step^[t]) s).2.1=s.2.1.drop t ∧
      ((step^[t]) s).2.2.2.length=s.2.2.2.length+t := by
   induction t with
   | zero => simp
   | succ t ih =>
     rw [Function.iterate_succ_apply']
     simp only [step,ih.1,ih.2.1,ih.2.2,List.length_cons]
     constructor
     · exact List.tail_drop
     · constructor
       · exact List.tail_drop
       · omega

 theorem word_value (A B : List Bool) : value (word A B)=value A+value B := by
   let t := A.length+B.length
   let s : State := (A,(B,(false,[])))
   have hlist := iter_lists s t
   have hA : ((step^[t]) s).1=[] := by rw [hlist.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hB : ((step^[t]) s).2.1=[] := by rw [hlist.2.1]; exact List.drop_eq_nil_of_le (by dsimp [s,t]; omega)
   have hzero : ((step^[t+1]) s).1=[] ∧ ((step^[t+1]) s).2.1=[] ∧ ((step^[t+1]) s).2.2.1=false := by
     rw [Function.iterate_succ_apply']
     simp [step,hA,hB]
   have hi := iter_value s (t+1)
   rw [hzero.1,hzero.2.1,hzero.2.2] at hi
   simpa only [word,s,t,value,List.reverse_nil,Bool.toNat_false,Nat.add_zero,Nat.mul_zero,List.length_nil,pow_zero,Nat.one_mul,Nat.zero_add] using hi

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrim
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def trim : List Bool → List Bool
   | [] => []
   | b::L => let T := trim L
             if T=[] then if b then [true] else [] else b::T

 theorem trim_value (L : List Bool) : value (trim L)=value L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT : trim L=[]
     · have hv : value L=0 := by rw [← ih,hT]; rfl
       cases b <;> simp [trim,hT,value,hv]
     · simp only [trim,hT,if_false,value,ih]

 theorem trim_lower (L : List Bool) (hL : trim L≠[]) : 2^((trim L).length-1)≤ value (trim L) := by
   induction L with
   | nil => exact False.elim (hL rfl)
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp_all [trim,value]
     · have hh := ih hT
       have hlen : 0<(trim L).length := by
         cases he : trim L with
         | nil => exact False.elim (hT he)
         | cons a T => simp
       have hp : 2^((trim L).length)=2*2^((trim L).length-1) := by
         rw [← Nat.pow_succ']
         congr 1
         omega
       simp only [trim,hT,if_false,List.length_cons,Nat.add_sub_cancel,value]
       rw [hp]
       omega

 def trimStep (x : Bool×List Bool) : List Bool :=
   if x.2=[] then if x.1 then [true] else [] else x.1::x.2

 theorem trim_fold (L : List Bool) : L.reverse.foldl (fun T b => trimStep (b,T)) []=trim L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     rw [List.reverse_cons,List.foldl_append]
     change trimStep (b,L.reverse.foldl (fun T b => trimStep (b,T)) [])=trim (b::L)
     rw [ih]
     rfl

 theorem trim_idem (L : List Bool) : trim (trim L)=trim L := by
   induction L with
   | nil => rfl
   | cons b L ih =>
     by_cases hT : trim L=[]
     · cases b <;> simp [trim,hT]
     · simp only [trim,hT,if_false,ih]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinarySubtract
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinarySubtract
open RawStack
abbrev State := BinaryAdder.State
 def step (s : State) : State :=
   let a := s.1.headD false
   let b := s.2.1.headD false
   let c := s.2.2.1
   (s.1.tail,(s.2.1.tail,((!a && (b || c)) || (b && c),(xor (xor a b) c)::s.2.2.2)))
 def raw (A B : List Bool) : Bool×List Bool :=
   let s := (step^[A.length+B.length+1]) (A,(B,(false,[])))
   (s.2.2.1,s.2.2.2.reverse)
 def difference (A B : List Bool) : List Bool := if (raw A B).1 then [] else trim (raw A B).2
 def less (A B : List Bool) : Bool := (raw A B).1

 def potential (s : State) : ℤ :=
   (value s.2.2.2.reverse:ℤ)+(2:ℤ)^s.2.2.2.length*((value s.1:ℤ)-(value s.2.1:ℤ)-s.2.2.1.toNat)

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.BinaryMultiply
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def multiplyStep (x : Bool×(List Bool×List Bool)) : List Bool×List Bool :=
   (false::x.2.1,if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2)
 def multiply (A B : List Bool) : List Bool :=
   trim (B.foldl (fun s b => multiplyStep (b,s)) (A,[])).2

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryDivision
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def divideStep (x : Bool×(List Bool×(List Bool×List Bool))) : List Bool×(List Bool×List Bool) :=
   let B := x.2.1
   let R := x.1::x.2.2.1
   if BinarySubtract.less R B then (B,(trim R,false::x.2.2.2))
   else (B,(BinarySubtract.difference R B,true::x.2.2.2))
 def divide (A B : List Bool) : List Bool×List Bool :=
   let s := A.reverse.foldl (fun s b => divideStep (b,s)) (B,([],[]))
   (trim s.2.2,trim s.2.1)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EuclidBound
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryEuclid

 def step (s : ℕ×ℕ) : ℕ×ℕ := if s.2=0 then s else (s.2,s.1%s.2)

end EdgeSublinearMWIS.Main.BinaryEuclid
end

-- Solutions.BinaryGcd
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
namespace BinaryGcd

 def step (s : List Bool×List Bool) : List Bool×List Bool :=
   if s.2=[] then s else (s.2,(divide s.1 s.2).2)
 def run (A B : List Bool) : List Bool×List Bool := step^[2*B.length] (trim A,trim B)
 def gcd (A B : List Bool) : List Bool := (run A B).1

 theorem value_positive (A : List Bool) (hA : trim A=A) (hn : A≠[]) : 0< value A := by
   have h := trim_lower A (by simpa only [hA] using hn)
   rw [hA] at h
   exact lt_of_lt_of_le (by positivity : 0<2^(A.length-1)) h

end BinaryGcd
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryCanonical
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 theorem natBits_eq_bits (n : ℕ) : natBits n=n.bits := by
   simp only [natBits,Nat.digits_two_eq_bits,List.map_map]
   have he : ((fun b : ℕ => b==1) ∘ (fun b : Bool => cond b 1 0))=id := by funext b; cases b <;> rfl
   rw [he,List.map_id]

 theorem trim_eq_bits_value (A : List Bool) : trim A=(value A).bits := by
   induction A with
   | nil => exact Nat.zero_bits.symm
   | cons b A ih =>
     by_cases hA : trim A=[]
     · have hv : value A=0 := by rw [← trim_value A,hA]; rfl
       cases b <;> simp [trim,hA,value,hv,Nat.zero_bits,Nat.one_bits]
     · have hp := BinaryGcd.value_positive (trim A) (trim_idem A) hA
       rw [trim_value] at hp
       have hb : Nat.bit b (value A)=b.toNat+2*value A := by cases b <;> simp [Nat.bit]; omega
       simp only [trim,hA,if_false]
       rw [ih,value,← hb,Nat.bits_append_bit (value A) b (by omega)]

 theorem trim_eq_natBits (A : List Bool) : trim A=natBits (value A) := by
   rw [natBits_eq_bits]
   exact trim_eq_bits_value A

 theorem canonical_eq_natBits (A : List Bool) (hA : trim A=A) : A=natBits (value A) := by
   exact hA.symm.trans (trim_eq_natBits A)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryAdderRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

 def headBit : Realizer (fun A : List Bool => A.headD false) where
   transform := Data.head
   charge := fun x => x.size+2
   routine := Routine.select true
   correct A := by cases A <;> rfl

 def tailBits : Realizer (fun A : List Bool => A.tail) where
   transform := Data.tail
   charge := fun x => x.size+2
   routine := Routine.select false
   correct A := by cases A <;> rfl

 def xorBits : Realizer (fun x : Bool×Bool => xor x.1 x.2) :=
   (Realizer.not.choose Realizer.id).congr (fun x => by rcases x with ⟨a,b⟩; cases a <;> cases b <;> rfl)

 def bitA : Realizer (fun s : State => s.1.headD false) := Realizer.fst.comp headBit
 def bitB : Realizer (fun s : State => s.2.1.headD false) := (Realizer.snd.comp Realizer.fst).comp headBit
 def bitC : Realizer (fun s : State => s.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def revOutput : Realizer (fun s : State => s.2.2.2) := (Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def sumBit : Realizer (fun s : State => xor (xor (s.1.headD false) (s.2.1.headD false)) s.2.2.1) :=
   (((bitA.pair bitB).comp xorBits).pair bitC).comp xorBits
 def carryBit : Realizer (fun s : State =>
     (s.1.headD false && s.2.1.headD false)||(s.1.headD false && s.2.2.1)||(s.2.1.headD false && s.2.2.1)) :=
   ((((bitA.pair bitB).comp Realizer.and).pair ((bitA.pair bitC).comp Realizer.and)).comp Realizer.or).pair
     ((bitB.pair bitC).comp Realizer.and) |>.comp Realizer.or

 def stepRealizer : Realizer step :=
   ((Realizer.fst.comp tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp tailBits).pair
       (carryBit.pair ((sumBit.pair revOutput).comp Realizer.cons)))).congr (fun _ => rfl)

 def wordLength : Realizer (fun A : List Bool => A.length) :=
   (Uniform.length (I := Unit) (α := fun _ => Bool)).specialize ()
 def lengthBound : Realizer (fun x : List Bool×List Bool => x.1.length+x.2.length+1) :=
   (((Realizer.fst.comp wordLength).pair (Realizer.snd.comp wordLength)).comp Realizer.add).comp Realizer.succ
 def initialState : Realizer (fun x : List Bool×List Bool => (x.1,(x.2,(false,([] : List Bool))))) :=
   Realizer.fst.pair (Realizer.snd.pair (Realizer.false.pair Realizer.nil))
 def wordRealizer : Realizer (fun x : List Bool×List Bool => word x.1 x.2) :=
   (((lengthBound.pair initialState).comp stepRealizer.iterate).comp revOutput).comp Realizer.reverse

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.NativeCompilerInterface
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.NativeCompiler
 
end EdgeSublinearMWIS.Main.NativeCompiler
end

-- Solutions.RealizerLinear
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def Linear {f : α → β} (R : Realizer f) : Prop :=
   ∃ C : ℕ,0< C ∧ ∀ x,R.time x ≤ C*(volume x+1) ∧ volume (f x) ≤ C*(volume x+1)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.AdderStepBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.WordLengthBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.AdderRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.AdderTotalRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinaryAdder
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.BinaryAdder
end

-- Solutions.BinaryTrimRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nonemptyBits : Realizer (fun L : List Bool => !L.isEmpty) :=
   (Uniform.isCons (I:=Unit) (α:=fun _ => Bool)).specialize ()
 def keepBit : Realizer (fun x : Bool×List Bool => x.1 || !x.2.isEmpty) :=
   (Realizer.fst.pair (Realizer.snd.comp nonemptyBits)).comp Realizer.or
 def trimStepRealizer : Realizer trimStep :=
   ((keepBit.pair Realizer.id).comp (Realizer.cons.choose Realizer.nil)).congr (fun x => by
     rcases x with ⟨b,L⟩
     cases L with
     | nil => cases b <;> rfl
     | cons a L => cases b <;> rfl)
 def trimRealizer : Realizer trim :=
   (((Realizer.reverse : Realizer (fun L : List Bool => L.reverse)).pair Realizer.nil).comp trimStepRealizer.fold).congr (fun L => trim_fold L)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.TrimRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryMultiplyRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 def addThenTrim : Realizer (fun x : List Bool×List Bool => trim (BinaryAdder.word x.2 x.1)) :=
   ((Realizer.snd.pair Realizer.fst).comp BinaryAdder.wordRealizer).comp trimRealizer
 def selectedSum : Realizer (fun x : Bool×(List Bool×List Bool) =>
     if x.1 then trim (BinaryAdder.word x.2.2 x.2.1) else x.2.2) :=
   addThenTrim.choose Realizer.snd
 def shiftedWord : Realizer (fun x : Bool×(List Bool×List Bool) => false::x.2.1) :=
   (Realizer.false.pair (Realizer.snd.comp Realizer.fst)).comp Realizer.cons
 def multiplyStepRealizer : Realizer multiplyStep :=
   (shiftedWord.pair selectedSum).congr (fun _ => rfl)
 def multiplyInitial : Realizer (fun x : List Bool×List Bool => (x.2,(x.1,([] : List Bool)))) :=
   Realizer.snd.pair (Realizer.fst.pair Realizer.nil)
 def multiplyRealizer : Realizer (fun x : List Bool×List Bool => multiply x.1 x.2) :=
   (((multiplyInitial.comp multiplyStepRealizer.fold).comp Realizer.snd).comp trimRealizer).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RealizerPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def PolyBound {f : α → β} (R : Realizer f) : Prop :=
   ∃ C q : ℕ,0< C ∧ ∀ x,R.time x≤ C*(volume x+1)^q ∧ volume (f x)≤ C*(volume x+1)^q

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinaryArithmeticPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterate
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinarySubtractRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def notA : Realizer (fun s : State => !s.1.headD false) := BinaryAdder.bitA.comp Realizer.not
 def borrowBit : Realizer (fun s : State =>
     (!s.1.headD false && (s.2.1.headD false || s.2.2.1))||(s.2.1.headD false && s.2.2.1)) :=
   ((notA.pair ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.or)).comp Realizer.and).pair
     ((BinaryAdder.bitB.pair BinaryAdder.bitC).comp Realizer.and) |>.comp Realizer.or
 def stepRealizer : Realizer step :=
   ((Realizer.fst.comp BinaryAdder.tailBits).pair
     (((Realizer.snd.comp Realizer.fst).comp BinaryAdder.tailBits).pair
       (borrowBit.pair ((BinaryAdder.sumBit.pair BinaryAdder.revOutput).comp Realizer.cons)))).congr (fun _ => rfl)
 def rawRealizer : Realizer (fun x : List Bool×List Bool => raw x.1 x.2) :=
   (((BinaryAdder.lengthBound.pair BinaryAdder.initialState).comp stepRealizer.iterate).comp
     (BinaryAdder.bitC.pair (BinaryAdder.revOutput.comp Realizer.reverse))).congr (fun _ => rfl)
 def lessRealizer : Realizer (fun x : List Bool×List Bool => less x.1 x.2) := rawRealizer.comp Realizer.fst
 def differenceRealizer : Realizer (fun x : List Bool×List Bool => difference x.1 x.2) :=
   (rawRealizer.comp (Realizer.nil.choose RawStack.trimRealizer)).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.SubtractPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.BinarySubtract
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.BinarySubtract
end

-- Solutions.BinaryDivisionRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
abbrev DivisionState := List Bool×(List Bool×List Bool)
abbrev DivisionInput := Bool×DivisionState

 def divisionDen : Realizer (fun x : DivisionInput => x.2.1) := Realizer.snd.comp Realizer.fst
 def divisionOldR : Realizer (fun x : DivisionInput => x.2.2.1) := (Realizer.snd.comp Realizer.snd).comp Realizer.fst
 def divisionOldQ : Realizer (fun x : DivisionInput => x.2.2.2) := (Realizer.snd.comp Realizer.snd).comp Realizer.snd
 def divisionNewR : Realizer (fun x : DivisionInput => x.1::x.2.2.1) :=
   (Realizer.fst.pair divisionOldR).comp Realizer.cons
 def divisionPair : Realizer (fun x : DivisionInput => (x.1::x.2.2.1,x.2.1)) := divisionNewR.pair divisionDen
 def divisionTest : Realizer (fun x : DivisionInput => BinarySubtract.less (x.1::x.2.2.1) x.2.1) :=
   divisionPair.comp BinarySubtract.lessRealizer
 def divisionRemainder : Realizer (fun x : DivisionInput =>
     if BinarySubtract.less (x.1::x.2.2.1) x.2.1 then trim (x.1::x.2.2.1) else BinarySubtract.difference (x.1::x.2.2.1) x.2.1) :=
   (divisionTest.pair divisionPair).comp ((Realizer.fst.comp trimRealizer).choose BinarySubtract.differenceRealizer)
 def divisionQ : Realizer (fun x : DivisionInput => (!BinarySubtract.less (x.1::x.2.2.1) x.2.1)::x.2.2.2) :=
   ((divisionTest.comp Realizer.not).pair divisionOldQ).comp Realizer.cons
 def divideStepRealizer : Realizer divideStep :=
   (divisionDen.pair (divisionRemainder.pair divisionQ)).congr (fun x => by
     rcases x with ⟨b,B,R,Q⟩
     cases h : BinarySubtract.less (b::R) B <;> simp [divideStep,h])
 def divideInitial : Realizer (fun x : List Bool×List Bool => (x.1.reverse,(x.2,(([] : List Bool),([] : List Bool))))) :=
   (Realizer.fst.comp Realizer.reverse).pair (Realizer.snd.pair (Realizer.nil.pair Realizer.nil))
 def divisionFinish : Realizer (fun x : DivisionState => (trim x.2.2,trim x.2.1)) :=
   ((Realizer.snd.comp Realizer.snd).comp trimRealizer).pair ((Realizer.snd.comp Realizer.fst).comp trimRealizer)
 def divideRealizer : Realizer (fun x : List Bool×List Bool => divide x.1 x.2) :=
   ((divideInitial.comp divideStepRealizer.fold).comp divisionFinish).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FoldPrefixBound
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BitFoldEnvelope
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {β : Type} [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.DivisionRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterateBounded
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.BinaryGcdRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack.BinaryGcd
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def stepRealizer : Realizer step :=
   (((Realizer.snd.comp nonemptyBits).pair Realizer.id).comp
     ((Realizer.snd.pair (divideRealizer.comp Realizer.snd)).choose Realizer.id)).congr (fun s => by
       rcases s with ⟨A,B⟩
       cases B <;> simp [step,nonemptyBits])

 def iterationCount : Realizer (fun s : List Bool×List Bool => 2*s.2.length) :=
   ((Realizer.snd.comp BinaryAdder.wordLength).pair (Realizer.snd.comp BinaryAdder.wordLength)).comp Realizer.add
     |>.congr (fun s => by dsimp only [Function.comp_apply]; omega)
 def initialRealizer : Realizer (fun s : List Bool×List Bool => (trim s.1,trim s.2)) :=
   (Realizer.fst.comp trimRealizer).pair (Realizer.snd.comp trimRealizer)
 def runRealizer : Realizer (fun s : List Bool×List Bool => run s.1 s.2) :=
   ((iterationCount.pair initialRealizer).comp stepRealizer.iterate).congr (fun _ => rfl)
 def gcdRealizer : Realizer (fun s : List Bool×List Bool => gcd s.1 s.2) := runRealizer.comp Realizer.fst

end EdgeSublinearMWIS.Main.RawStack.BinaryGcd
end

-- Solutions.BinaryRational
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def normalizeWords (A B : List Bool) : List Bool×List Bool :=
   let D := BinaryGcd.gcd A B
   ((divide A D).1,(divide B D).1)

 def gcdArguments : Realizer (fun x : List Bool×List Bool => (x,BinaryGcd.gcd x.1 x.2)) :=
   Realizer.id.pair BinaryGcd.gcdRealizer
 def normalizeFirst : Realizer (fun x : (List Bool×List Bool)×List Bool => (divide x.1.1 x.2).1) :=
   (((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeSecond : Realizer (fun x : (List Bool×List Bool)×List Bool => (divide x.1.2 x.2).1) :=
   (((Realizer.fst.comp Realizer.snd).pair Realizer.snd).comp divideRealizer).comp Realizer.fst
 def normalizeWordsRealizer : Realizer (fun x : List Bool×List Bool => normalizeWords x.1 x.2) :=
   (gcdArguments.comp (normalizeFirst.pair normalizeSecond)).congr (fun _ => rfl)

 def signedValue (b : Bool) (A : List Bool) : ℤ := if b then -(value A : ℤ) else value A

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryListCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def appendBits : Realizer (fun x : List Bool×List Bool => x.1++x.2) :=
   ((((Realizer.fst.comp Realizer.reverse).pair Realizer.snd).comp Realizer.cons.fold)).congr
     (fun x => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])

 def prependTrue : Realizer (fun L : List Bool => true::L) := ((Realizer.constant true).pair Realizer.id).comp Realizer.cons
 
 def replicateTrue : Realizer (fun n : ℕ => List.replicate n true) :=
   ((Realizer.id.pair Realizer.nil).comp prependTrue.iterate).congr (fun n => by
     change (fun L : List Bool => true::L)^[n] []=List.replicate n true
     induction n with
     | zero => rfl
     | succ n ih => rw [Function.iterate_succ_apply',ih,List.replicate_succ])

 def prefixBits (A : List Bool) : List Bool := List.replicate A.length true++false::A
 def falseCons : Realizer (fun L : List Bool => false::L) := (Realizer.false.pair Realizer.id).comp Realizer.cons
 
 def prefixRealizer : Realizer prefixBits :=
   ((BinaryAdder.wordLength.comp replicateTrue).pair falseCons).comp appendBits

 theorem prefix_natBits (n : ℕ) : prefixBits (natBits n)=encodeNat n := by
   simp only [prefixBits,encodeNat,List.append_assoc,List.singleton_append]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SerializeRational
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev SignedWords := Bool×(List Bool×List Bool)
 def rationalSign (s : SignedWords) : Bool := s.1 && !(trim s.2.1).isEmpty
 def rationalBits (s : SignedWords) : List Bool :=
   let N := normalizeWords s.2.1 s.2.2
   rationalSign s :: (prefixBits N.1++prefixBits N.2)
 def signRealizer : Realizer rationalSign :=
   (Realizer.fst.pair (((Realizer.snd.comp Realizer.fst).comp trimRealizer).comp nonemptyBits)).comp Realizer.and
 def normalizedRealizer : Realizer (fun s : SignedWords => normalizeWords s.2.1 s.2.2) := Realizer.snd.comp normalizeWordsRealizer
 def unsignedBitsRealizer : Realizer (fun s : List Bool×List Bool => prefixBits s.1++prefixBits s.2) :=
   ((Realizer.fst.comp prefixRealizer).pair (Realizer.snd.comp prefixRealizer)).comp appendBits
 def rationalBitsRealizer : Realizer rationalBits :=
   (signRealizer.pair (normalizedRealizer.comp unsignedBitsRealizer)).comp Realizer.cons

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def takeWordStep (s : List Bool×List Bool) : List Bool×List Bool :=
   if s.1.isEmpty then s else (s.1.tail,s.1.headD false::s.2)
 def takeWordStepRealizer : Realizer takeWordStep :=
   (((Realizer.fst.comp nonemptyBits).pair Realizer.id).comp
     (((Realizer.fst.comp BinaryAdder.tailBits).pair
       (((Realizer.fst.comp BinaryAdder.headBit).pair Realizer.snd).comp Realizer.cons)).choose Realizer.id)).congr (fun s => by
       rcases s with ⟨L,R⟩
       cases L <;> rfl)

 theorem takeWordStep_iterate (L R : List Bool) (k : ℕ) :
     takeWordStep^[k] (L,R)=(L.drop k,(L.take k).reverse++R) := by
   induction k generalizing L R with
   | zero => simp
   | succ k ih =>
     rw [Function.iterate_succ_apply]
     cases L with
     | nil => simpa only [takeWordStep,List.isEmpty_nil,if_true,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append] using ih [] R
     | cons a L =>
       change takeWordStep^[k] (L,a::R)=_
       rw [ih,List.drop_succ_cons,List.take_succ_cons,List.reverse_cons]
       simp only [List.append_assoc,List.singleton_append]

 def splitWord (L : List Bool) (k : ℕ) : List Bool×List Bool := (L.take k,L.drop k)
 def splitWordRealizer : Realizer (fun x : List Bool×ℕ => splitWord x.1 x.2) :=
   (((Realizer.snd.pair (Realizer.fst.pair Realizer.nil)).comp takeWordStepRealizer.iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst)).congr (fun x => by
       dsimp only [Function.comp_apply,splitWord]
       rw [takeWordStep_iterate]
       simp)

 def readWord (L : List Bool) : List Bool×List Bool :=
   let k := (L.takeWhile id).length
   splitWord (L.drop (k+1)) k

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ConstantCode
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.LeadingParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def leadingStepRealizer : Realizer Binary.leadingStep := (Uniform.binaryLeadingStep (I:=Unit)).specialize ()

 def leadingRealizer : Realizer (fun L : List Bool => (L.takeWhile id).length) :=
   (((Realizer.id.pair (Realizer.constant (true,0))).comp leadingStepRealizer.fold).comp Realizer.snd).congr
     (fun L => by simpa only [Function.comp_apply,id_eq,Nat.zero_add,ite_true,Binary.leading] using Binary.leading_fold L true 0)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ReadWordCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def skipPrefixRealizer : Realizer (fun L : List Bool => L.drop ((L.takeWhile id).length+1)) :=
   (((Realizer.id.pair (leadingRealizer.comp Realizer.succ)).comp splitWordRealizer).comp Realizer.snd).congr (fun _ => rfl)
 def readWordRealizer : Realizer readWord :=
   ((skipPrefixRealizer.pair leadingRealizer).comp splitWordRealizer).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ReadRational
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readRational (L : List Bool) : SignedWords×List Bool :=
   let A := readWord L.tail
   let B := readWord A.2
   ((L.headD false,(A.1,B.1)),B.2)
 def numeratorRealizer : Realizer (fun L : List Bool => readWord L.tail) := BinaryAdder.tailBits.comp readWordRealizer
 def denominatorRealizer : Realizer (fun L : List Bool => readWord (readWord L.tail).2) :=
   (numeratorRealizer.comp Realizer.snd).comp readWordRealizer
 def readRationalRealizer : Realizer readRational :=
   (BinaryAdder.headBit.pair ((numeratorRealizer.comp Realizer.fst).pair (denominatorRealizer.comp Realizer.fst))).pair
     (denominatorRealizer.comp Realizer.snd)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CappedBinary
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RawStack

 def capStep (x : Bool×(ℕ×ℕ)) : ℕ×ℕ := (min x.2.2 (2*x.2.1+x.1.toNat),x.2.2)

 def cappedValue (A : List Bool) (c : ℕ) : ℕ :=
   (A.reverse.foldl (fun s b => capStep (b,s)) (0,c)).1

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.TreeToTM2
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.TreeToTM2
end

-- Solutions.CappedBinaryRealizer
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def boolNat : Realizer Bool.toNat := Realizer.reinterpret _ (by intro b; cases b <;> rfl)

 def minRealizer : Realizer (fun x : ℕ×ℕ => min x.1 x.2) :=
   ((Realizer.le.pair Realizer.id).comp (Realizer.fst.choose Realizer.snd)).congr (fun x => by simp [min_def])

 def capCurrent : Realizer (fun x : Bool×(ℕ×ℕ) => x.2.1) := Realizer.snd.comp Realizer.fst
 def capLimit : Realizer (fun x : Bool×(ℕ×ℕ) => x.2.2) := Realizer.snd.comp Realizer.snd
 def capNext : Realizer (fun x : Bool×(ℕ×ℕ) => 2*x.2.1+x.1.toNat) :=
   ((((capCurrent.pair capCurrent).comp Realizer.add).pair (Realizer.fst.comp boolNat)).comp Realizer.add).congr
     (fun _ => by dsimp only [Function.comp_apply]; omega)
 def capStepRealizer : Realizer capStep := ((capLimit.pair capNext).comp minRealizer).pair capLimit

 def cappedValueRealizer : Realizer (fun x : List Bool×ℕ => cappedValue x.1 x.2) :=
   (((Realizer.fst.comp Realizer.reverse).pair ((Realizer.constant 0).pair Realizer.snd)).comp capStepRealizer.fold).comp Realizer.fst

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.NaturalBinaryCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nextWord (A : List Bool) : List Bool := trim (BinaryAdder.word A [true])
 def nextWordRealizer : Realizer nextWord :=
   ((Realizer.id.pair (Realizer.constant [true])).comp BinaryAdder.wordRealizer).comp trimRealizer
 
 theorem nextWord_value (A : List Bool) : value (nextWord A)=value A+1 := by
   rw [nextWord,trim_value,BinaryAdder.word_value]
   simp [value]
 theorem nextWord_canonical (A : List Bool) : trim (nextWord A)=nextWord A := trim_idem _

 theorem nextWord_iter_value (n : ℕ) : value (nextWord^[n] [])=n := by
   induction n with
   | zero => rfl
   | succ n ih => rw [Function.iterate_succ_apply',nextWord_value,ih]
 theorem nextWord_iter_canonical (n : ℕ) : trim (nextWord^[n] [])=nextWord^[n] [] := by
   cases n with
   | zero => rfl
   | succ n => rw [Function.iterate_succ_apply']; exact nextWord_canonical _
 def naturalWordRealizer : Realizer natBits :=
   ((Realizer.id.pair Realizer.nil).comp nextWordRealizer.iterate).congr (fun n => by
     change nextWord^[n] []=natBits n
     rw [canonical_eq_natBits _ (nextWord_iter_canonical n),nextWord_iter_value])
 
 def naturalCodeRealizer : Realizer encodeNat := (naturalWordRealizer.comp prefixRealizer).congr prefix_natBits

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EncodingBounds
noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.EncodingBounds

end EdgeSublinearMWIS.Main.EncodingBounds
end

-- Solutions.ReadNatural
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readNatural (L : List Bool) : ℕ×List Bool :=
   let A := readWord L
   (cappedValue A.1 (L.length+1),A.2)
 def parserCap : Realizer (fun L : List Bool => L.length+1) := BinaryAdder.wordLength.comp Realizer.succ
 def readNaturalRealizer : Realizer readNatural :=
   ((((readWordRealizer.comp Realizer.fst).pair parserCap).comp cappedValueRealizer).pair (readWordRealizer.comp Realizer.snd))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalBatch
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev BatchState := List Bool×List SignedWords
 def batchStep (s : BatchState) : BatchState :=
   let A := readRational s.1
   (A.2,A.1::s.2)
 def batchStepRealizer : Realizer batchStep :=
   (((Realizer.fst.comp readRationalRealizer).comp Realizer.snd).pair
     ((((Realizer.fst.comp readRationalRealizer).comp Realizer.fst).pair Realizer.snd).comp Realizer.cons))

 def readMany (n : ℕ) (L : List Bool) : List SignedWords×List Bool :=
   let s := batchStep^[n] (L,[])
   (s.2.reverse,s.1)
 def readManyRealizer : Realizer (fun x : ℕ×List Bool => readMany x.1 x.2) :=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp batchStepRealizer.iterate).comp
     ((Realizer.snd.comp Realizer.reverse).pair Realizer.fst))

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 def codeWords (q : RationalCode) : SignedWords :=
   (decide (q.numerator<0),(natBits q.numerator.natAbs,natBits q.denominator))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialIterateGrowth
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.TriangularCode
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GraphRawCode
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WeightedParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialMap
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def mapEnvironment {f : α×γ → β} (R : Realizer f) :
     Realizer (fun x : List α×γ => x.1.map (fun a => f (a,x.2))) := (R.uniform Unit).map.specialize ()

 def mapList {f : α → β} (R : Realizer f) : Realizer (fun xs : List α => xs.map f) :=
   ((Realizer.id.pair Realizer.unit).comp (mapEnvironment (Realizer.fst.comp R))).congr (fun _ => rfl)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.DirectWeightedProgram
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MultiplyRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MultiplyTotalRuntime
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WeightedHelpers
noncomputable section

open scoped BigOperators
open EdgeSublinearMWIS.Main
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedHelpers

end EdgeSublinearMWIS.Main.WeightedHelpers
end

-- Solutions.WeightedExecutionMath
noncomputable section

open scoped BigOperators Classical
open EdgeSublinearMWIS.Main EdgeSublinearMWIS.Main.WeightedHelpers
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.WeightedExecutionMath

end EdgeSublinearMWIS.Main.WeightedExecutionMath
end

-- Solutions.BinaryFractions
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev FractionWords := List Bool×List Bool
 def fractionValue (s : FractionWords) : ℚ := (value s.1 : ℚ)/(value s.2 : ℚ)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FractionCompare
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def fractionLE (x : FractionWords×FractionWords) : Bool :=
   !BinarySubtract.less (multiply x.2.1 x.1.2) (multiply x.1.1 x.2.2)
 def crossLeft : Realizer (fun x : FractionWords×FractionWords => multiply x.1.1 x.2.2) :=
   ((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.snd)).comp multiplyRealizer
 def crossRight : Realizer (fun x : FractionWords×FractionWords => multiply x.2.1 x.1.2) :=
   ((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.snd)).comp multiplyRealizer
 def fractionLERealizer : Realizer fractionLE :=
   (((crossRight.pair crossLeft).comp BinarySubtract.lessRealizer).comp Realizer.not)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialFoldSelect
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.FractionMaximum
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FractionDivision
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ScaleRoundingWords
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RawRounding
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RawRoundingCorrect
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HalfAccuracyCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordValueCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def valueStep (x : Bool×ℕ) : ℕ := 2*x.2+x.1.toNat
 def valueStepRealizer : Realizer valueStep :=
   ((((Realizer.snd.pair Realizer.snd).comp Realizer.add).pair (Realizer.fst.comp boolNat)).comp Realizer.add).congr
     (fun _ => by dsimp only [Function.comp_apply,valueStep]; omega)
 
 theorem valueFold (L : List Bool) (v : ℕ) :
     L.foldl (fun v b => valueStep (b,v)) v=value L.reverse+2^L.length*v := by
   induction L generalizing v with
   | nil => simp [value]
   | cons b L ih =>
     rw [List.foldl_cons,ih,List.reverse_cons,BinaryAdder.value_append]
     simp only [valueStep,value,List.length_reverse,List.length_cons,pow_succ,Nat.mul_zero,Nat.add_zero]
     ring

 def valueInitial : Realizer (fun A : List Bool => (A.reverse,(0 : ℕ))) := Realizer.reverse.pair (Realizer.constant 0)
 def valueRealizer : Realizer value := (valueInitial.comp valueStepRealizer.fold).congr (fun A => by
   change A.reverse.foldl (fun v b => valueStep (b,v)) 0=value A
   rw [valueFold,List.reverse_reverse]
   simp only [Nat.mul_zero,Nat.add_zero])

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ListPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 def appendList : Realizer (fun x : List α×List α => x.1++x.2) :=
   ((((Realizer.fst.comp Realizer.reverse).pair Realizer.snd).comp Realizer.cons.fold)).congr
     (fun _ => by simp only [Function.comp_apply,Realizer.fold_cons_eq,List.reverse_reverse])

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.PolynomialFoldBounded
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ListFlattenRepeat
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 def flattenStep (s : List α×List α) : List α := s.2++s.1
 def flattenStepRealizer : Realizer (flattenStep (α:=α)) := (Realizer.snd.pair Realizer.fst).comp appendList
 
 theorem flattenFold (xs : List (List α)) (acc : List α) : xs.foldl (fun b a => flattenStep (a,b)) acc=acc++xs.flatten := by
   induction xs generalizing acc with
   | nil => simp
   | cons a xs ih => rw [List.foldl_cons,ih]; simp [flattenStep,List.append_assoc]
 
 def flattenList : Realizer (fun xs : List (List α) => xs.flatten) :=
   ((Realizer.id.pair Realizer.nil).comp flattenStepRealizer.fold).congr (fun xs => by change xs.foldl (fun b a => flattenStep (a,b)) []=xs.flatten; rw [flattenFold]; rfl)

 def repeatStep (s : α×List α) : α×List α := (s.1,s.1::s.2)
 def repeatStepRealizer : Realizer (repeatStep (α:=α)) := Realizer.fst.pair Realizer.cons
 
 theorem repeatStep_iterate (n : ℕ) (a : α) (L : List α) : repeatStep^[n] (a,L)=(a,List.replicate n a++L) := by
   induction n with
   | zero => rfl
   | succ n ih => rw [Function.iterate_succ_apply',ih]; simp only [repeatStep,List.replicate_succ,List.cons_append]

 def replicateList : Realizer (fun x : ℕ×α => List.replicate x.1 x.2) :=
   (((Realizer.fst.pair (Realizer.snd.pair Realizer.nil)).comp repeatStepRealizer.iterate).comp Realizer.snd).congr
     (fun x => by dsimp only [Function.comp_apply]; rw [repeatStep_iterate]; simp)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.RangePolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.FilterPolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α γ : Type} [Coding α] [Coding γ]

 def selectSingleton {p : α×γ → Bool} (P : Realizer p) : Realizer (fun x : α×γ => if p x then [x.1] else []) :=
   (P.pair Realizer.id).comp ((((Realizer.fst.pair Realizer.nil).comp Realizer.cons)).choose Realizer.nil)
 
 theorem filter_flatten (p : α×γ → Bool) (xs : List α) (e : γ) :
     (xs.map (fun a => if p (a,e) then [a] else [])).flatten=xs.filter (fun a => p (a,e)) := by
   induction xs with
   | nil => rfl
   | cons a xs ih => cases hp : p (a,e) <;> simp [hp,ih]
 def filterEnvironment {p : α×γ → Bool} (P : Realizer p) :
     Realizer (fun x : List α×γ => x.1.filter (fun a => p (a,x.2))) :=
   ((mapEnvironment (selectSingleton P)).comp flattenList).congr (fun x => filter_flatten p x.1 x.2)

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ListAccessCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack
variable {α : Type} [Coding α]

 def tailList : Realizer (fun L : List α => L.tail) := (Uniform.tail (I:=Unit) (α:=fun _ => α)).specialize ()

 theorem tail_iterate (L : List α) (k : ℕ) : List.tail^[k] L=L.drop k := by
   induction k with
   | zero => rfl
   | succ k ih => rw [Function.iterate_succ_apply',ih,List.tail_drop]
 def dropList : Realizer (fun x : List α×ℕ => x.1.drop x.2) :=
   ((Realizer.snd.pair Realizer.fst).comp tailList.iterate).congr (fun x => by
     change List.tail^[x.2] x.1=x.1.drop x.2
     exact tail_iterate _ _)

 def headNat : Realizer (fun L : List ℕ => L.headD 0) where
   transform := Data.head
   charge := fun x => x.size+2
   routine := Routine.select true
   correct L := by cases L <;> rfl

 def countStep : Realizer (fun x : α×ℕ => x.2+1) := Realizer.snd.comp Realizer.succ
 theorem count_fold (L : List α) (k : ℕ) : L.foldl (fun k (_ : α) => k+1) k=k+L.length := by
   induction L generalizing k with
   | nil => simp
   | cons a L ih => rw [List.foldl_cons,ih,List.length_cons]; omega
 
 def listLength : Realizer (fun L : List α => L.length) :=
   ((Realizer.id.pair (Realizer.constant 0)).comp countStep.fold).congr (fun L => by
     change L.foldl (fun k (_ : α) => k+1) 0=L.length
     simp only [count_fold,Nat.zero_add])

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.DecodeWordList
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OwnerIndices
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OwnerSemantics
noncomputable section

open scoped Classical BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open WeightedHelpers

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.VertexPairCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ZipBitsCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
variable {α : Type} [OAI.ThreeMachine.StackCompiler.Coding α]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AdjacencyTableCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.VertexPairSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OriginalAdjacencyQuery
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RoundedGraphCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProjectionCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nonemptyNatList : Realizer (fun L : List ℕ => !L.isEmpty) := (Uniform.isCons (I:=Unit) (α:=fun _ => ℕ)).specialize ()

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FiniteArrayCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem fold_reverse_head {α : Type} (L : List α) (a : α) :
     L.reverse.foldl (fun _ b => b) a=L.headD a := by
   cases L with
   | nil => rfl
   | cons b L => rw [List.reverse_cons,List.foldl_append]; rfl
 def headList {α : Type} [Coding α] (a : α) : Realizer (fun L : List α => L.headD a) :=
   ((Realizer.reverse.pair (Realizer.constant a)).comp Realizer.fst.fold).congr (fun L => fold_reverse_head L a)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CoordinateArrayCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def lookupList {α : Type} [Coding α] (a : α) : Realizer (fun s : List α×ℕ => (s.1.drop s.2).headD a) :=
   dropList.comp (headList a)

end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack
 
end EdgeSublinearMWIS.Main.RawStack

namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GenericArrayPairs
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RawStack
variable {α β : Type} [Coding α] [Coding β]

 def arrayPairAt (a : α) (b : β) : Realizer (fun s : ℕ×(List α×List β) =>
     ((s.2.1.drop s.1).headD a,(s.2.2.drop s.1).headD b)) :=
   ((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp (lookupList a)).pair
     (((Realizer.snd.comp Realizer.snd).pair Realizer.fst).comp (lookupList b)))
 
 def arrayPairs (a : α) (b : β) (s : List α×List β) : List (α×β) :=
   (List.range s.1.length).map (fun i => ((s.1.drop i).headD a,(s.2.drop i).headD b))
 def arrayPairsRealizer (a : α) (b : β) : Realizer (arrayPairs a b) :=
   (((Realizer.fst.comp listLength).comp Realizer.range).pair Realizer.id).comp (mapEnvironment (arrayPairAt a b))

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.FractionAddition
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def sumWords (A B : List Bool) : List Bool := trim (BinaryAdder.word A B)

 def sumWordsRealizer : Realizer (fun s : List Bool×List Bool => sumWords s.1 s.2) :=
   BinaryAdder.wordRealizer.comp trimRealizer

 def fractionWidth (s : FractionWords) : ℕ := max s.1.length s.2.length+1

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedSumCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev SignedPairWords := (Bool×Bool)×(List Bool×List Bool)
 def signedNumeratorSum (s : SignedPairWords) : Bool×List Bool :=
   if xor s.1.1 s.1.2 then
     if BinarySubtract.less s.2.1 s.2.2 then (s.1.2,BinarySubtract.difference s.2.2 s.2.1)
     else (s.1.1,BinarySubtract.difference s.2.1 s.2.2)
   else (s.1.1,sumWords s.2.1 s.2.2)
 def signedPairLeft : Realizer (fun s : SignedPairWords => s.1.1) := Realizer.fst.comp Realizer.fst
 def signedPairRight : Realizer (fun s : SignedPairWords => s.1.2) := Realizer.fst.comp Realizer.snd
 
 def oppositeSigns : Realizer (fun s : SignedPairWords => xor s.1.1 s.1.2) := Realizer.fst.comp BinaryAdder.xorBits
 
 def signedPairLess : Realizer (fun s : SignedPairWords => BinarySubtract.less s.2.1 s.2.2) := Realizer.snd.comp BinarySubtract.lessRealizer
 
 def signedFirstDifference : Realizer (fun s : SignedPairWords => (s.1.1,BinarySubtract.difference s.2.1 s.2.2)) :=
   signedPairLeft.pair (Realizer.snd.comp BinarySubtract.differenceRealizer)
 
 def signedSecondDifference : Realizer (fun s : SignedPairWords => (s.1.2,BinarySubtract.difference s.2.2 s.2.1)) :=
   signedPairRight.pair ((((Realizer.snd.comp Realizer.snd).pair (Realizer.snd.comp Realizer.fst))).comp BinarySubtract.differenceRealizer)
 
 def signedMixedSum := (signedPairLess.pair Realizer.id).comp (signedSecondDifference.choose signedFirstDifference)
 
 def signedSameSum : Realizer (fun s : SignedPairWords => (s.1.1,sumWords s.2.1 s.2.2)) := signedPairLeft.pair (Realizer.snd.comp sumWordsRealizer)
 
 def signedNumeratorSumRealizer : Realizer signedNumeratorSum :=
   ((oppositeSigns.pair Realizer.id).comp (signedMixedSum.choose signedSameSum)).congr (fun s => rfl)

 def signedCrossLeft : Realizer (fun s : SignedWords×SignedWords => multiply s.1.2.1 s.2.2.2) :=
   (((((Realizer.fst.comp Realizer.snd).comp Realizer.fst)).pair (((Realizer.snd.comp Realizer.snd).comp Realizer.snd)))).comp multiplyRealizer
 def signedCrossRight : Realizer (fun s : SignedWords×SignedWords => multiply s.2.2.1 s.1.2.2) :=
   (((((Realizer.snd.comp Realizer.snd).comp Realizer.fst)).pair (((Realizer.fst.comp Realizer.snd).comp Realizer.snd)))).comp multiplyRealizer

 def signedCommonDen : Realizer (fun s : SignedWords×SignedWords => multiply s.1.2.2 s.2.2.2) :=
   (((((Realizer.fst.comp Realizer.snd).comp Realizer.snd)).pair (((Realizer.snd.comp Realizer.snd).comp Realizer.snd)))).comp multiplyRealizer
 
 def signedSumNumerator (s : SignedWords×SignedWords) : Bool×List Bool :=
   signedNumeratorSum ((s.1.1,s.2.1),(multiply s.1.2.1 s.2.2.2,multiply s.2.2.1 s.1.2.2))
 def signedSumNumeratorRealizer : Realizer signedSumNumerator :=
   ((((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).pair (signedCrossLeft.pair signedCrossRight)).comp signedNumeratorSumRealizer)
 
 def signedFractionAdd (s : SignedWords×SignedWords) : SignedWords :=
   ((signedSumNumerator s).1,((signedSumNumerator s).2,multiply s.1.2.2 s.2.2.2))
 def signedFractionAddRealizer : Realizer signedFractionAdd :=
   (signedSumNumeratorRealizer.comp Realizer.fst).pair ((signedSumNumeratorRealizer.comp Realizer.snd).pair signedCommonDen)
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedSumMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def signedFractionValue (s : SignedWords) : ℚ := (signedValue s.1 s.2.1:ℚ)/(value s.2.2:ℚ)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedProductCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def signedFractionNeg (s : SignedWords) : SignedWords := (!s.1,s.2)
 def signedFractionNegRealizer : Realizer signedFractionNeg := (Realizer.fst.comp Realizer.not).pair Realizer.snd
 
 def signedProductSign : Realizer (fun s : SignedWords×SignedWords => xor s.1.1 s.2.1) :=
   (((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp BinaryAdder.xorBits)
 
 def signedProductNum : Realizer (fun s : SignedWords×SignedWords => multiply s.1.2.1 s.2.2.1) :=
   (((((Realizer.fst.comp Realizer.snd).comp Realizer.fst)).pair (((Realizer.snd.comp Realizer.snd).comp Realizer.fst)))).comp multiplyRealizer
 
 def signedFractionMul (s : SignedWords×SignedWords) : SignedWords :=
   (xor s.1.1 s.2.1,(multiply s.1.2.1 s.2.2.1,multiply s.1.2.2 s.2.2.2))
 def signedFractionMulRealizer : Realizer signedFractionMul := signedProductSign.pair (signedProductNum.pair signedCommonDen)
 
 def signedFractionDiv (s : SignedWords×SignedWords) : SignedWords :=
   (xor s.1.1 s.2.1,(multiply s.1.2.1 s.2.2.2,multiply s.2.2.1 s.1.2.2))
 def signedFractionDivRealizer : Realizer signedFractionDiv := signedProductSign.pair (signedCrossLeft.pair signedCrossRight)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedNormalize
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def signedReduced (s : SignedWords) : SignedWords :=
   (rationalSign s,normalizeWords s.2.1 s.2.2)
 def signedReducedRealizer : Realizer signedReduced := signRealizer.pair normalizedRealizer

 def canonicalAdd (s : SignedWords×SignedWords) : SignedWords := signedReduced (signedFractionAdd s)
 def canonicalAddRealizer : Realizer canonicalAdd := signedFractionAddRealizer.comp signedReducedRealizer

 def canonicalMul (s : SignedWords×SignedWords) : SignedWords := signedReduced (signedFractionMul s)
 def canonicalMulRealizer : Realizer canonicalMul := signedFractionMulRealizer.comp signedReducedRealizer

 def canonicalDiv (s : SignedWords×SignedWords) : SignedWords := signedReduced (signedFractionDiv s)
 def canonicalDivRealizer : Realizer canonicalDiv := signedFractionDivRealizer.comp signedReducedRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedNormalizeBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedVectorCode
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev SignedVector := List SignedWords
 def signedZero : SignedWords := (false,([],[true]))
 def vectorPairAt : Realizer (fun s : ℕ×(SignedVector×SignedVector) =>
     ((s.2.1.drop s.1).headD signedZero,(s.2.2.drop s.1).headD signedZero)) :=
   ((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp (lookupList signedZero)).pair
     (((Realizer.snd.comp Realizer.snd).pair Realizer.fst).comp (lookupList signedZero)))
 
 def vectorPairs (s : SignedVector×SignedVector) : List (SignedWords×SignedWords) :=
   (List.range s.1.length).map (fun i => ((s.1.drop i).headD signedZero,(s.2.drop i).headD signedZero))
 def vectorPairsRealizer : Realizer vectorPairs :=
   (((Realizer.fst.comp listLength).comp Realizer.range).pair Realizer.id).comp (mapEnvironment vectorPairAt)
 
 def vectorProducts (s : SignedVector×SignedVector) : SignedVector := (vectorPairs s).map canonicalMul
 def vectorProductsRealizer : Realizer vectorProducts := vectorPairsRealizer.comp (mapList canonicalMulRealizer)
 
 def signedSum (xs : SignedVector) : SignedWords := xs.foldl (fun a b => canonicalAdd (b,a)) signedZero
 def signedSumRealizer : Realizer signedSum :=
   (Realizer.id.pair (Realizer.constant signedZero)).comp canonicalAddRealizer.fold
 
 def signedDot (s : SignedVector×SignedVector) : SignedWords := signedSum (vectorProducts s)
 def signedDotRealizer : Realizer signedDot := vectorProductsRealizer.comp signedSumRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedVectorArithmetic
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def canonicalSub (s : SignedWords×SignedWords) : SignedWords := canonicalAdd (s.1,signedFractionNeg s.2)
 def canonicalSubRealizer : Realizer canonicalSub :=
   (Realizer.fst.pair (Realizer.snd.comp signedFractionNegRealizer)).comp canonicalAddRealizer

 def vectorAdd (s : SignedVector×SignedVector) : SignedVector := (vectorPairs s).map canonicalAdd
 def vectorAddRealizer : Realizer vectorAdd := vectorPairsRealizer.comp (mapList canonicalAddRealizer)
 
 def vectorSub (s : SignedVector×SignedVector) : SignedVector := (vectorPairs s).map canonicalSub
 def vectorSubRealizer : Realizer vectorSub := vectorPairsRealizer.comp (mapList canonicalSubRealizer)
 
 def vectorScale (s : SignedVector×SignedWords) : SignedVector := s.1.map (fun a => canonicalMul (a,s.2))
 def vectorScaleRealizer : Realizer vectorScale := mapEnvironment canonicalMulRealizer

 def gsCoefficient (s : SignedVector×SignedVector) : SignedWords :=
   canonicalDiv (signedDot s,signedDot (s.2,s.2))
 def gsCoefficientRealizer : Realizer gsCoefficient :=
   (signedDotRealizer.pair ((Realizer.snd.pair Realizer.snd).comp signedDotRealizer)).comp canonicalDivRealizer
 
 def gsProjection (s : SignedVector×SignedVector) : SignedVector := vectorScale (s.2,gsCoefficient s)
 def gsProjectionRealizer : Realizer gsProjection :=
   (Realizer.snd.pair gsCoefficientRealizer).comp vectorScaleRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialFoldPower
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.SignedVectorSumBounds
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def vectorWidth (L : SignedVector) : ℕ := (L.map (fun a => fractionWidth a.2)).sum

 def subtractVector (s : SignedVector×SignedVector) : SignedVector := vectorSub (s.2,s.1)
 def subtractVectorRealizer : Realizer subtractVector := (Realizer.snd.pair Realizer.fst).comp vectorSubRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtRowCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def gsProjectionWith : Realizer (fun s : SignedVector×SignedVector => gsProjection (s.2,s.1)) :=
   (Realizer.snd.pair Realizer.fst).comp gsProjectionRealizer
 
 def gsProjections (s : SignedVector×List SignedVector) : List SignedVector :=
   s.2.map (fun g => gsProjection (s.1,g))
 def gsProjectionsRealizer : Realizer gsProjections :=
   (Realizer.snd.pair Realizer.fst).comp (mapEnvironment gsProjectionWith)
 
 def gsRow (s : SignedVector×List SignedVector) : SignedVector :=
   (gsProjections s).foldl (fun b a => subtractVector (a,b)) s.1
 def gsRowRealizer : Realizer gsRow :=
   (gsProjectionsRealizer.pair Realizer.fst).comp subtractVectorRealizer.fold

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 def RepresentsVector {n : ℕ} (A : SignedVector) (v : Vec n) : Prop :=
   ∃ a : Fin n → SignedWords, A=List.ofFn a ∧
     (∀ i,0< value (a i).2.2) ∧ ∀ i,(signedFractionValue (a i):ℝ)=v i

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def floorDivision (s : SignedWords) : List Bool×List Bool := divide s.2.1 s.2.2
 def floorDivisionRealizer : Realizer floorDivision := Realizer.snd.comp divideRealizer
 
 def floorRoundUp (s : SignedWords) : Bool := s.1 && !(trim (floorDivision s).2).isEmpty
 def floorRoundUpRealizer : Realizer floorRoundUp :=
   (Realizer.fst.pair (((floorDivisionRealizer.comp Realizer.snd).comp trimRealizer).comp nonemptyBits)).comp Realizer.and
 
 def floorIncrement (s : SignedWords) : List Bool := if floorRoundUp s then [true] else []
 def floorIncrementRealizer : Realizer floorIncrement :=
   (floorRoundUpRealizer.pair Realizer.id).comp ((Realizer.constant [true]).choose (Realizer.constant ([]:List Bool)))
 
 def floorMagnitude (s : SignedWords) : List Bool := sumWords (floorDivision s).1 (floorIncrement s)
 def floorMagnitudeRealizer : Realizer floorMagnitude :=
   ((floorDivisionRealizer.comp Realizer.fst).pair floorIncrementRealizer).comp sumWordsRealizer
 
 def signedFloorWords (s : SignedWords) : SignedWords := (s.1,(floorMagnitude s,[true]))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerRootStep
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.IntegerRoot
 def step (root rem digit : ℕ) : ℕ×ℕ :=
   let next := 4*rem+digit
   if next<4*root+1 then (2*root,next) else (2*root+1,next-(4*root+1))

end EdgeSublinearMWIS.Main.IntegerRoot
end

-- Solutions.BinaryRootStep
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev RootWords := List Bool×List Bool
 abbrev RootStepWords := (Bool×Bool)×RootWords
 def rootNextRemainder (s : RootStepWords) : List Bool := s.1.1::s.1.2::s.2.2
 def rootTrial (s : RootStepWords) : List Bool := true::false::s.2.1
 def rootNextRemainderRealizer : Realizer rootNextRemainder :=
   (Realizer.fst.comp Realizer.fst).pair (((Realizer.fst.comp Realizer.snd).pair (Realizer.snd.comp Realizer.snd)).comp Realizer.cons) |>.comp Realizer.cons
 def rootTrialRealizer : Realizer rootTrial :=
   ((Realizer.constant true).pair (((Realizer.constant false).pair (Realizer.snd.comp Realizer.fst)).comp Realizer.cons)).comp Realizer.cons

 def rootTakeBit (s : RootStepWords) : Bool := !(BinarySubtract.less (rootNextRemainder s) (rootTrial s))
 def rootTakeBitRealizer : Realizer rootTakeBit := ((rootNextRemainderRealizer.pair rootTrialRealizer).comp BinarySubtract.lessRealizer).comp Realizer.not
 
 def rootDifferenceRealizer : Realizer (fun s : RootStepWords => BinarySubtract.difference (rootNextRemainder s) (rootTrial s)) :=
   (rootNextRemainderRealizer.pair rootTrialRealizer).comp BinarySubtract.differenceRealizer
 
 def rootWordStep (s : RootStepWords) : RootWords :=
   (rootTakeBit s::s.2.1,if rootTakeBit s then BinarySubtract.difference (rootNextRemainder s) (rootTrial s) else rootNextRemainder s)
 def rootWordStepRealizer : Realizer rootWordStep :=
   ((rootTakeBitRealizer.pair (Realizer.snd.comp Realizer.fst)).comp Realizer.cons).pair
     ((rootTakeBitRealizer.pair Realizer.id).comp (rootDifferenceRealizer.choose rootNextRemainderRealizer))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryPairs
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev QuarterState := Bool×(Bool×List (Bool×Bool))
 def quarterStep (s : Bool×QuarterState) : QuarterState :=
   if s.2.1 then (false,(false,(s.2.2.1,s.1)::s.2.2.2)) else (true,(s.1,s.2.2.2))
 def quarterFull : Realizer (fun s : Bool×QuarterState => (false,(false,(s.2.2.1,s.1)::s.2.2.2))) :=
   (Realizer.constant false).pair ((Realizer.constant false).pair
     (((((Realizer.snd.comp Realizer.snd).comp Realizer.fst).pair Realizer.fst).pair ((Realizer.snd.comp Realizer.snd).comp Realizer.snd)).comp Realizer.cons))
 def quarterHalf : Realizer (fun s : Bool×QuarterState => (true,(s.1,s.2.2.2))) :=
   (Realizer.constant true).pair (Realizer.fst.pair ((Realizer.snd.comp Realizer.snd).comp Realizer.snd))

 def quarterStepRealizer : Realizer quarterStep :=
   (((Realizer.snd.comp Realizer.fst).pair Realizer.id).comp (quarterFull.choose quarterHalf)).congr (fun s => rfl)

 def quarterFinish (s : QuarterState) : List (Bool×Bool) := if s.1 then (s.2.1,false)::s.2.2 else s.2.2
 def quarterFinishRealizer : Realizer quarterFinish :=
   ((Realizer.fst.pair Realizer.id).comp
     (((((Realizer.snd.comp Realizer.fst).pair (Realizer.constant false)).pair (Realizer.snd.comp Realizer.snd)).comp Realizer.cons).choose
       (Realizer.snd.comp Realizer.snd))).congr (fun s => rfl)
 
 def quarterPairs (L : List Bool) : List (Bool×Bool) := quarterFinish (L.foldl (fun s b => quarterStep (b,s)) (false,(false,[])))
 def quarterPairsRealizer : Realizer quarterPairs :=
   ((Realizer.id.pair (Realizer.constant (false,(false,([] : List (Bool×Bool)))))).comp quarterStepRealizer.fold).comp quarterFinishRealizer
 
 def quarterLittle : List Bool → List (Bool×Bool)
   | [] => []
   | [b] => [(b,false)]
   | b::c::L => (b,c)::quarterLittle L

 def quarterValue : List (Bool×Bool) → ℕ
   | [] => 0
   | (b,c)::L => b.toNat+2*c.toNat+4*quarterValue L

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryRoot
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def rootWordFold (L : List (Bool×Bool)) (s : RootWords) : RootWords := L.foldl (fun s d => rootWordStep (d,s)) s

 def rootNatStep (s : (ℕ×ℕ)) (d : Bool×Bool) : ℕ×ℕ := IntegerRoot.step s.1 s.2 (d.1.toNat+2*d.2.toNat)

 def integerRootWord (L : List Bool) : List Bool := trim (rootWordFold (quarterPairs L) ([],[])).1
 def integerRootWordRealizer : Realizer integerRootWord :=
   ((((quarterPairsRealizer.pair (Realizer.constant (([] : List Bool),([] : List Bool)))).comp rootWordStepRealizer.fold).comp Realizer.fst).comp trimRealizer)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedDyadicRound
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev DyadicInput := SignedWords×ℕ
 def dyadicZeros : Realizer (fun s : DyadicInput => List.replicate s.2 false) := (Realizer.snd.pair (Realizer.constant false)).comp replicateList
 
 def dyadicNumerator : Realizer (fun s : DyadicInput => List.replicate s.2 false++s.1.2.1) :=
   (dyadicZeros.pair ((Realizer.fst.comp Realizer.snd).comp Realizer.fst)).comp appendBits

 def dyadicDenominator : Realizer (fun s : DyadicInput => List.replicate s.2 false++[true]) :=
   (dyadicZeros.pair (Realizer.constant [true])).comp appendBits

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalRoot
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev RationalRootInput := FractionWords×ℕ
 def rootDoubleInput (s : RationalRootInput) : DyadicInput := ((false,s.1),s.2+s.2)
 def rootDoubleInputRealizer : Realizer rootDoubleInput :=
   ((Realizer.constant false).pair Realizer.fst).pair ((Realizer.snd.pair Realizer.snd).comp Realizer.add)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryWordProduct
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def productWordStep (s : List Bool×List Bool) : List Bool := multiply s.1 s.2
 def productWordStepRealizer : Realizer productWordStep := multiplyRealizer

 def wordProduct (xs : List (List Bool)) : List Bool := xs.foldl (fun b a => productWordStep (a,b)) [true]
 def wordProductRealizer : Realizer wordProduct :=
   (Realizer.id.pair (Realizer.constant [true])).comp productWordStepRealizer.fold

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryPowerTwoCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def powerTwoWord (k : ℕ) : List Bool := List.replicate k false++[true]
 def powerTwoWordRealizer : Realizer powerTwoWord :=
   (((Realizer.id.pair (Realizer.constant false)).comp replicateList).pair (Realizer.constant [true])).comp appendBits

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSRationalRounding
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RationalRounding.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Computable rational rounding primitives with real error guarantees and grid
encoding bounds. These do not yet supply a RAM implementation.
-/

namespace EdgeSublinearMWIS.Main.GLS.RationalRounding

end EdgeSublinearMWIS.Main.GLS.RationalRounding
end

-- Solutions.SqrtUpperCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def upperRootInput (s : RationalRootInput) : SignedWords :=
   (true,(List.replicate (s.2+s.2) false++s.1.1,s.1.2))
 def upperRootInputRealizer : Realizer upperRootInput := (Realizer.constant true).pair
   ((rootDoubleInputRealizer.comp dyadicNumerator).pair (Realizer.fst.comp Realizer.snd))
 
 def upperRootInteger : RationalRootInput → List Bool := integerRootWord ∘ floorMagnitude ∘ upperRootInput
 def upperRootIntegerRealizer : Realizer upperRootInteger := (upperRootInputRealizer.comp floorMagnitudeRealizer).comp integerRootWordRealizer
 
 def upperRootSumInput (s : RationalRootInput) : List Bool×List Bool := (upperRootInteger s,[true])
 def upperRootSumInputRealizer : Realizer upperRootSumInput := upperRootIntegerRealizer.pair (Realizer.constant [true])
 
 def upperRootMagnitude : RationalRootInput → List Bool := (fun s : List Bool×List Bool => sumWords s.1 s.2) ∘ upperRootSumInput
 def upperRootMagnitudeRealizer : Realizer upperRootMagnitude := upperRootSumInputRealizer.comp sumWordsRealizer
 
 def sqrtUpperWords (s : RationalRootInput) : SignedWords :=
   (false,(upperRootMagnitude s,powerTwoWord s.2))
 def sqrtUpperWordsRealizer : Realizer sqrtUpperWords :=
   (Realizer.constant false).pair (upperRootMagnitudeRealizer.pair (Realizer.snd.comp powerTwoWordRealizer))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedFloorDyadic
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def scaledFloorInput (s : DyadicInput) : SignedWords :=
   (s.1.1,(List.replicate s.2 false++s.1.2.1,s.1.2.2))
 def scaledFloorInputRealizer : Realizer scaledFloorInput :=
   (Realizer.fst.comp Realizer.fst).pair (dyadicNumerator.pair ((Realizer.fst.comp Realizer.snd).comp Realizer.snd))
 
 def signedFloorDyadic (s : DyadicInput) : SignedWords :=
   (s.1.1,(floorMagnitude (scaledFloorInput s),List.replicate s.2 false++[true]))
 def signedFloorDyadicRealizer : Realizer signedFloorDyadic :=
   (Realizer.fst.comp Realizer.fst).pair ((scaledFloorInputRealizer.comp floorMagnitudeRealizer).pair dyadicDenominator)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedMatrixCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev SignedMatrix := List SignedVector
 def matrixVector (s : SignedMatrix×SignedVector) : SignedVector := s.1.map (fun row => signedDot (row,s.2))
 def matrixVectorRealizer : Realizer matrixVector := mapEnvironment signedDotRealizer
 
 def matrixScale (s : SignedMatrix×SignedWords) : SignedMatrix := s.1.map (fun row => vectorScale (row,s.2))
 def matrixScaleRealizer : Realizer matrixScale := mapEnvironment vectorScaleRealizer
 
 def matrixSub : SignedMatrix×SignedMatrix → SignedMatrix :=
   (fun pairs => pairs.map vectorSub) ∘ arrayPairs ([]:SignedVector) ([]:SignedVector)
 def matrixSubRealizer : Realizer matrixSub := (arrayPairsRealizer ([]:SignedVector) ([]:SignedVector)).comp (mapList vectorSubRealizer)
 
 def matrixAdd : SignedMatrix×SignedMatrix → SignedMatrix :=
   (fun pairs => pairs.map vectorAdd) ∘ arrayPairs ([]:SignedVector) ([]:SignedVector)
 def matrixAddRealizer : Realizer matrixAdd := (arrayPairsRealizer ([]:SignedVector) ([]:SignedVector)).comp (mapList vectorAddRealizer)
 
 def outerRow (s : SignedWords×SignedVector) : SignedVector := vectorScale (s.2,s.1)
 def outerRowRealizer : Realizer outerRow := (Realizer.snd.pair Realizer.fst).comp vectorScaleRealizer
 
 def matrixOuter (s : SignedVector×SignedVector) : SignedMatrix := s.1.map (fun a => outerRow (a,s.2))
 def matrixOuterRealizer : Realizer matrixOuter := mapEnvironment outerRowRealizer
 
 def floorVector (s : SignedVector×ℕ) : SignedVector := s.1.map (fun a => signedFloorDyadic (a,s.2))
 def floorVectorRealizer : Realizer floorVector := mapEnvironment signedFloorDyadicRealizer
 
 def floorMatrix (s : SignedMatrix×ℕ) : SignedMatrix := s.1.map (fun row => floorVector (row,s.2))
 def floorMatrixRealizer : Realizer floorMatrix := mapEnvironment floorVectorRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ListReplacementCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]

 def replaceChoice (default : α) (s : ℕ×(List α×(ℕ×α))) : α :=
   if s.1=s.2.2.1 then s.2.2.2 else (s.2.1.drop s.1).headD default
 def replaceChoiceRealizer (default : α) : Realizer (replaceChoice default) :=
   ((((Realizer.fst.pair ((Realizer.snd.comp Realizer.snd).comp Realizer.fst)).comp Realizer.eqNat).pair Realizer.id).comp
     (((Realizer.snd.comp Realizer.snd).comp Realizer.snd).choose
       ((((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp (lookupList default))))).congr (fun _ => by simp [replaceChoice])
 
 def replaceList (default : α) (s : List α×(ℕ×α)) : List α :=
   (List.range s.1.length).map (fun i => replaceChoice default (i,s))
 def replaceListRealizer (default : α) : Realizer (replaceList default) :=
   (((Realizer.fst.comp listLength).comp Realizer.range).pair Realizer.id).comp (mapEnvironment (replaceChoiceRealizer default))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiagonalMaximumCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev DiagonalEntry := ℕ×SignedWords
 def diagonalWordAt (s : ℕ×SignedMatrix) : SignedWords := (((s.2.drop s.1).headD []).drop s.1).headD signedZero
 def diagonalWordAtRealizer : Realizer diagonalWordAt :=
   ((((Realizer.snd.pair Realizer.fst).comp (lookupList ([]:SignedVector))).pair Realizer.fst).comp (lookupList signedZero))
 
 def diagonalEntryAt (s : ℕ×SignedMatrix) : DiagonalEntry := (s.1,diagonalWordAt s)
 def diagonalEntryAtRealizer : Realizer diagonalEntryAt := Realizer.fst.pair diagonalWordAtRealizer
 
 def diagonalEntries (A : SignedMatrix) : List DiagonalEntry := (List.range A.length).map (fun i => diagonalEntryAt (i,A))
 def diagonalEntriesRealizer : Realizer diagonalEntries :=
   ((listLength.comp Realizer.range).pair Realizer.id).comp (mapEnvironment diagonalEntryAtRealizer)
 
 def diagonalCompare (s : DiagonalEntry×DiagonalEntry) : Bool := fractionLE (s.2.2.2,s.1.2.2)
 def diagonalCompareRealizer : Realizer diagonalCompare :=
   ((((Realizer.snd.comp Realizer.snd).comp Realizer.snd).pair
     ((Realizer.fst.comp Realizer.snd).comp Realizer.snd)).comp fractionLERealizer)
 
 def diagonalMaxStep (s : DiagonalEntry×DiagonalEntry) : DiagonalEntry := if diagonalCompare s then s.1 else s.2
 def diagonalMaxStepRealizer : Realizer diagonalMaxStep :=
   (diagonalCompareRealizer.pair Realizer.id).comp (Realizer.fst.choose Realizer.snd)

 def diagonalWinner (xs : List DiagonalEntry) : DiagonalEntry :=
   xs.foldl (fun b a => diagonalMaxStep (a,b)) (xs.headD (0,signedZero))
 def diagonalWinnerRealizer : Realizer diagonalWinner :=
   (Realizer.id.pair (headList (0,signedZero))).comp diagonalMaxStepRealizer.fold
 
 def maximumDiagonal : SignedMatrix → DiagonalEntry := diagonalWinner ∘ diagonalEntries
 def maximumDiagonalRealizer : Realizer maximumDiagonal := diagonalEntriesRealizer.comp diagonalWinnerRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorAppend
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BorderedMatrix
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.InverseMath

 def border {K : Type} [Zero K] {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (b : Fin n → K) (c : K) :
     Matrix (Fin (n+1)) (Fin (n+1)) K :=
   fun i => Fin.lastCases (Fin.snoc b c) (fun i => Fin.snoc (A i) (b i)) i

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.LLLLovaszScalar
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def threeQuarter : SignedWords := (false,([true,true],[false,false,true]))

 abbrev LovaszScalarInput := SignedWords×(SignedWords×SignedWords)
 def lovaszSquare : Realizer (fun s : LovaszScalarInput => canonicalMul (s.1,s.1)) :=
   (Realizer.fst.pair Realizer.fst).comp canonicalMulRealizer
 
 def lovaszTerm : Realizer (fun s : LovaszScalarInput => canonicalMul (canonicalMul (s.1,s.1),s.2.1)) :=
   (lovaszSquare.pair (Realizer.snd.comp Realizer.fst)).comp canonicalMulRealizer
 
 def lovaszLeft (s : LovaszScalarInput) : SignedWords :=
   canonicalAdd (s.2.2,canonicalMul (canonicalMul (s.1,s.1),s.2.1))
 def lovaszLeftRealizer : Realizer lovaszLeft :=
   ((Realizer.snd.comp Realizer.snd).pair lovaszTerm).comp canonicalAddRealizer
 
 def lovaszRight (s : LovaszScalarInput) : SignedWords := canonicalMul (threeQuarter,s.2.1)
 def lovaszRightRealizer : Realizer lovaszRight :=
   ((Realizer.constant threeQuarter).pair (Realizer.snd.comp Realizer.fst)).comp canonicalMulRealizer
 
 def lovaszMagnitudes (s : LovaszScalarInput) : FractionWords×FractionWords := ((lovaszRight s).2,(lovaszLeft s).2)
 def lovaszTest : LovaszScalarInput → Bool := fractionLE ∘ lovaszMagnitudes
 def lovaszBad : LovaszScalarInput → Bool := Bool.not ∘ lovaszTest
 def lovaszMagnitudePair : Realizer lovaszMagnitudes :=
   (lovaszRightRealizer.comp (Realizer.snd : Realizer (Prod.snd : SignedWords → FractionWords))).pair
     (lovaszLeftRealizer.comp (Realizer.snd : Realizer (Prod.snd : SignedWords → FractionWords)))
 def lovaszTestRealizer : Realizer lovaszTest :=
   lovaszMagnitudePair.comp fractionLERealizer
 def lovaszBadRealizer : Realizer lovaszBad := lovaszTestRealizer.comp Realizer.not

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedNearest
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nearestNumerator (s : FractionWords) : List Bool := sumWords (false::s.1) s.2
 def nearestNumeratorRealizer : Realizer nearestNumerator :=
   (((Realizer.constant false).pair Realizer.fst).comp Realizer.cons |>.pair Realizer.snd).comp sumWordsRealizer
 
 def nearestDenominatorRealizer : Realizer (fun s : FractionWords => false::s.2) :=
   ((Realizer.constant false).pair Realizer.snd).comp Realizer.cons
 
 def nearestMagnitude (s : FractionWords) : List Bool :=
   (divide (nearestNumerator s) (false::s.2)).1
 def nearestMagnitudeRealizer : Realizer nearestMagnitude :=
   ((nearestNumeratorRealizer.pair nearestDenominatorRealizer).comp divideRealizer).comp Realizer.fst
 
 def signedNearest (s : SignedWords) : Bool×List Bool := (s.1,nearestMagnitude s.2)
 def signedNearestRealizer : Realizer signedNearest :=
   Realizer.fst.pair (Realizer.snd.comp nearestMagnitudeRealizer)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtFoldCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def gsAppend (s : SignedVector×List SignedVector) : List SignedVector := s.2++[gsRow s]
 def gsAppendRealizer : Realizer gsAppend :=
   (Realizer.snd.pair ((gsRowRealizer.pair (Realizer.constant ([] : List SignedVector))).comp Realizer.cons)).comp appendList
 
 def gsMatrix (bs : List SignedVector) : List SignedVector := bs.foldl (fun gs b => gsAppend (b,gs)) []
 def gsMatrixRealizer : Realizer gsMatrix :=
   (Realizer.id.pair (Realizer.constant ([] : List SignedVector))).comp gsAppendRealizer.fold

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeReductionMath
noncomputable section

namespace EdgeSublinearMWIS.Main.LLLBounds.GS
open LLLFactor.RedBasis LLLFactor.Reduction
section GS
variable {n : ℕ}

end GS
end EdgeSublinearMWIS.Main.LLLBounds.GS
end

-- Solutions.GramSchmidtFoldSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 def finitePrefix {α : Type} {n : ℕ} (f : Fin n → α) (k : ℕ) (hk : k≤ n) : List α :=
   List.ofFn (fun j : Fin k => f ⟨j.val,lt_of_lt_of_le j.isLt hk⟩)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedCanonicalBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def SignedCanonical (s : SignedWords) : Prop := signedReduced s=s
 def VectorCanonical (A : SignedVector) : Prop := ∀ s∈A,SignedCanonical s

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtCanonical
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GramSchmidtCramerProjection
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.IntegerVertexScale
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.IntegralLLLPotential
noncomputable section

open scoped BigOperators Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

def embed {n : ℕ} (b : Matrix (Fin n) (Fin n) ℤ) : Fin n → Vec n :=
  fun i => WithLp.toLp 2 (fun j => (b i j : ℝ))

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.IntegralLLLClosure
noncomputable section

open scoped Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

def IntegralRows {n : ℕ} (b : Fin n → Vec n) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) ℤ, b=embed B

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GeometricDescentBound
noncomputable section

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RuntimeMath

end EdgeSublinearMWIS.Main.RuntimeMath
end

-- Solutions.IntegralLLLStepBound
noncomputable section

open scoped BigOperators Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.IntegerHalfspaceEncoding
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.BinaryDual

end EdgeSublinearMWIS.Main.BinaryDual
end

-- Solutions.IntegralLLLInitialBound
noncomputable section

open scoped BigOperators Classical
open Matrix LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds

namespace EdgeSublinearMWIS.Main.LLLBounds
 
end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtIntegerCoordinates
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 def prefixGram {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) :
     Matrix (Fin i.val) (Fin i.val) ℤ := fun j k =>
   ∑ l,B ⟨j.val,by omega⟩ l*B ⟨k.val,by omega⟩ l
 def prefixCross {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : Fin i.val → ℤ :=
   fun j => ∑ l,B ⟨j.val,by omega⟩ l*B i l

 def gsNumerator {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) (k : Fin n) : ℤ :=
   (prefixGram B i).det*B i k-
     ∑ j : Fin i.val,(prefixGram B i).cramer (prefixCross B i) j*B ⟨j.val,by omega⟩ k

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtCoordinateBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtRationalBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds
open RawStack

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.GramSchmidtWordBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.GramSchmidtClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeStepCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def nearestIntegerCode (s : SignedWords) : SignedWords :=
   ((signedNearest s).1,((signedNearest s).2,[true]))
 def nearestIntegerCodeRealizer : Realizer nearestIntegerCode := signedNearestRealizer.comp
   (Realizer.fst.pair (Realizer.snd.pair (Realizer.constant [true])))

 abbrev SizeStepInput := (ℕ×ℕ)×(List SignedVector×List SignedVector)
 def sizeRowI : Realizer (fun s : SizeStepInput => (s.2.1.drop s.1.1).headD []) :=
   (((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.fst)).comp (lookupList []))
 def sizeRowJ : Realizer (fun s : SizeStepInput => (s.2.1.drop s.1.2).headD []) :=
   (((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.snd)).comp (lookupList []))
 def sizeGsJ : Realizer (fun s : SizeStepInput => (s.2.2.drop s.1.2).headD []) :=
   (((Realizer.snd.comp Realizer.snd).pair (Realizer.fst.comp Realizer.snd)).comp (lookupList []))

 def sizeCoefficient (s : SizeStepInput) : SignedWords :=
   gsCoefficient ((s.2.1.drop s.1.1).headD [],(s.2.2.drop s.1.2).headD [])
 def sizeCoefficientRealizer : Realizer sizeCoefficient := (sizeRowI.pair sizeGsJ).comp gsCoefficientRealizer
 
 def sizeInteger (s : SizeStepInput) : SignedWords := nearestIntegerCode (sizeCoefficient s)
 def sizeIntegerRealizer : Realizer sizeInteger := sizeCoefficientRealizer.comp nearestIntegerCodeRealizer
 
 def sizeNewRow (s : SizeStepInput) : SignedVector :=
   vectorSub ((s.2.1.drop s.1.1).headD [],vectorScale ((s.2.1.drop s.1.2).headD [],sizeInteger s))
 def sizeNewRowRealizer : Realizer sizeNewRow :=
   (sizeRowI.pair ((sizeRowJ.pair sizeIntegerRealizer).comp vectorScaleRealizer)).comp vectorSubRealizer
 
 def sizeStep (s : SizeStepInput) : List SignedVector×List SignedVector :=
   (replaceList [] (s.2.1,(s.1.1,sizeNewRow s)),s.2.2)
 def sizeStepRealizer : Realizer sizeStep :=
   ((((Realizer.snd.comp Realizer.fst).pair ((Realizer.fst.comp Realizer.fst).pair sizeNewRowRealizer)).comp
     (replaceListRealizer [])).pair (Realizer.snd.comp Realizer.snd))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizeStepSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReductionBasis
noncomputable section

set_option backward.isDefEq.respectTransparency false
open LLLFactor.Reduction LLLFactor.RedBasis
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLRowReduction
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

inductive RowReduction {n : ℕ} (i : Fin n) : ℕ → (Fin n → Vec n) → (Fin n → Vec n) → Prop
 | zero (b) : RowReduction i 0 b b
 | succ (m : ℕ) (hm : m< i.val) (b c : Fin n → Vec n) (r : ℤ)
     (near : IsNearestInt r (mu b i ⟨m,by omega⟩))
     (next : RowReduction i m (reduceBy b i ⟨m,by omega⟩ r) c) :
     RowReduction i (m+1) b c

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLRowCode
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 abbrev WordBasisState := List SignedVector×List SignedVector
 def rowPairs (s : ℕ×ℕ) : List (ℕ×ℕ) := (List.range s.1).reverse.map (fun j => (s.2,j))
 def rowPairsRealizer : Realizer rowPairs :=
   ((((Realizer.fst.comp Realizer.range).comp Realizer.reverse).pair Realizer.snd)).comp
     (mapEnvironment (Realizer.snd.pair Realizer.fst))
 
 def rowCode (s : ℕ×(ℕ×WordBasisState)) : WordBasisState :=
   (rowPairs (s.1,s.2.1)).foldl (fun st ij => sizeStep (ij,st)) s.2.2
 def rowCodeRealizer : Realizer rowCode :=
   ((((Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp rowPairsRealizer).pair
     (Realizer.snd.comp Realizer.snd))).comp sizeStepRealizer.fold

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSizePass
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

inductive SizePass {n : ℕ} : ℕ → (Fin n → Vec n) → (Fin n → Vec n) → Prop
 | zero (b) : SizePass 0 b b
 | succ (m : ℕ) (hm : m< n) (b c d : Fin n → Vec n)
     (prior : SizePass m b c) (row : RowReduction ⟨m,hm⟩ m c d) : SizePass (m+1) b d

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLFullPassCode
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 def rowIteration (s : ℕ×WordBasisState) : WordBasisState := rowCode (s.1,(s.1,s.2))
 def rowIterationRealizer : Realizer rowIteration :=
   (Realizer.fst.pair (Realizer.fst.pair Realizer.snd)).comp rowCodeRealizer
 def fullSizeCode (s : ℕ×WordBasisState) : WordBasisState :=
   (List.range s.1).foldl (fun st i => rowIteration (i,st)) s.2
 def fullSizeCodeRealizer : Realizer fullSizeCode :=
   ((Realizer.fst.comp Realizer.range).pair Realizer.snd).comp rowIterationRealizer.fold

 def sizePassInitialize (bs : List SignedVector) : ℕ×WordBasisState :=
   (bs.length,(bs,gsMatrix bs))
 def sizePassInitializeRealizer : Realizer sizePassInitialize :=
   listLength.pair (Realizer.id.pair gsMatrixRealizer)
 def sizePassCode (bs : List SignedVector) : WordBasisState := fullSizeCode (sizePassInitialize bs)
 def sizePassCodeRealizer : Realizer sizePassCode := sizePassInitializeRealizer.comp fullSizeCodeRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLovaszQueryCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev LovaszQueryInput := ℕ×WordBasisState
 def lovaszPrevGs : Realizer (fun s : LovaszQueryInput => (s.2.2.drop s.1).headD []) :=
   (((Realizer.snd.comp Realizer.snd).pair Realizer.fst).comp (lookupList []))
 def lovaszNextGs : Realizer (fun s : LovaszQueryInput => (s.2.2.drop (s.1+1)).headD []) :=
   (((Realizer.snd.comp Realizer.snd).pair (Realizer.fst.comp Realizer.succ)).comp (lookupList []))
 def lovaszNextRow : Realizer (fun s : LovaszQueryInput => (s.2.1.drop (s.1+1)).headD []) :=
   (((Realizer.snd.comp Realizer.fst).pair (Realizer.fst.comp Realizer.succ)).comp (lookupList []))

 def lovaszQueryData (s : LovaszQueryInput) : LovaszScalarInput :=
   (gsCoefficient ((s.2.1.drop (s.1+1)).headD [],(s.2.2.drop s.1).headD []),
     (signedDot ((s.2.2.drop s.1).headD [],(s.2.2.drop s.1).headD []),
       signedDot ((s.2.2.drop (s.1+1)).headD [],(s.2.2.drop (s.1+1)).headD [])))
 def lovaszQueryDataRealizer : Realizer lovaszQueryData :=
   (((lovaszNextRow.pair lovaszPrevGs).comp gsCoefficientRealizer).pair
     (((lovaszPrevGs.pair lovaszPrevGs).comp signedDotRealizer).pair
       ((lovaszNextGs.pair lovaszNextGs).comp signedDotRealizer)))
 
 def lovaszQuery : LovaszQueryInput → Bool := lovaszBad ∘ lovaszQueryData
 def lovaszQueryRealizer : Realizer lovaszQuery := lovaszQueryDataRealizer.comp lovaszBadRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFindBadCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def badList (s : WordBasisState) : List ℕ :=
   (List.range (s.1.length-1)).filter (fun i => lovaszQuery (i,s))
 def badListRealizer : Realizer badList :=
   (((((Realizer.fst.comp listLength).comp Realizer.pred).comp Realizer.range).pair Realizer.id)).comp
     (filterEnvironment lovaszQueryRealizer)

 def findBadCode (s : WordBasisState) : Bool×ℕ :=
   (!(badList s).isEmpty,(badList s).headD 0)
 def findBadCodeRealizer : Realizer findBadCode := badListRealizer.comp (nonemptyNatList.pair headNat)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GenericListTake
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 def takeList : Realizer (fun s : ℕ×List α => s.2.take s.1) :=
   ((((Realizer.snd.comp Realizer.reverse).pair
     ((((Realizer.snd.comp listLength).pair Realizer.fst).comp Realizer.sub))).comp dropList).comp Realizer.reverse).congr
       (fun s => by
         simp only [Function.comp_apply,List.drop_reverse,List.reverse_reverse]
         by_cases h : s.1≤ s.2.length
         · rw [Nat.sub_sub_self h]
         · have hg : s.2.length≤ s.1 := by omega
           rw [Nat.sub_eq_zero_of_le hg,Nat.sub_zero,List.take_length,List.take_of_length_le hg])

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.MatrixBorderCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def matrixColumn (s : SignedMatrix×ℕ) : SignedVector := s.1.map (fun row => (row.drop s.2).headD signedZero)
 def matrixColumnRealizer : Realizer matrixColumn := mapEnvironment (lookupList signedZero)
 
 def appendCoordinate (s : SignedVector×SignedWords) : SignedVector := s.1++[s.2]
 def appendCoordinateRealizer : Realizer appendCoordinate :=
   (Realizer.fst.pair ((Realizer.snd.pair (Realizer.constant ([]:SignedVector))).comp Realizer.cons)).comp appendList
 
 def appendColumn : SignedMatrix×SignedVector → SignedMatrix :=
   (fun pairs => pairs.map appendCoordinate) ∘ arrayPairs ([]:SignedVector) signedZero
 def appendColumnRealizer : Realizer appendColumn :=
   (arrayPairsRealizer ([]:SignedVector) signedZero).comp (mapList appendCoordinateRealizer)
 
 def borderMatrixWords (s : SignedMatrix×(SignedVector×SignedWords)) : SignedMatrix :=
   appendColumn (s.1,s.2.1)++[appendCoordinate s.2]
 def borderMatrixWordsRealizer : Realizer borderMatrixWords :=
   (((Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp appendColumnRealizer).pair
     (((Realizer.snd.comp appendCoordinateRealizer).pair (Realizer.constant ([]:SignedMatrix))).comp Realizer.cons)).comp appendList

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSCast
noncomputable section

namespace EdgeSublinearMWIS.Main.GLS.Cast

end EdgeSublinearMWIS.Main.GLS.Cast
end

-- Solutions.SignedMatrixSemantics
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open EdgeSublinearMWIS.Main.RealizerBounds

 def rationalVector {n : ℕ} (v : Fin n → ℚ) : Vec n := WithLp.toLp 2 (fun i => (v i:ℝ))
 def RepresentsMatrix {n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin n) (Fin n) ℚ) : Prop :=
   ∃ rows : Fin n → SignedVector,bs=List.ofFn rows ∧ ∀ i,RepresentsVector (rows i) (rationalVector (A i))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CanonicalVectorCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLFactor.RedBasis

 def normalizeVector (A : SignedVector) : SignedVector := A.map signedReduced
 def normalizeVectorRealizer : Realizer normalizeVector := mapList signedReducedRealizer
 
 def normalizeMatrix (A : SignedMatrix) : SignedMatrix := A.map normalizeVector
 def normalizeMatrixRealizer : Realizer normalizeMatrix := mapList normalizeVectorRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.NaturalProductCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 theorem replicate_flatten_length (a b : ℕ) :
     ((List.replicate a (List.replicate b true)).flatten).length=a*b := by
   simp [List.length_flatten,List.map_replicate,List.sum_replicate,Nat.mul_comm]
 def naturalProductRealizer : Realizer (fun s : ℕ×ℕ => s.1*s.2) :=
   (((((Realizer.fst.pair (Realizer.snd.comp replicateTrue)).comp replicateList).comp flattenList).comp listLength)).congr
     (fun s => replicate_flatten_length s.1 s.2)

 def naturalSquare : Realizer (fun n : ℕ => n*n) := (Realizer.id.pair Realizer.id).comp naturalProductRealizer
 
 def naturalFourth : Realizer (fun n : ℕ => (n*n)*(n*n)) := naturalSquare.comp naturalSquare
 
 def naturalFifth : Realizer (fun n : ℕ => n^5) :=
   ((naturalFourth.pair Realizer.id).comp naturalProductRealizer).congr (fun _ => by dsimp only [Function.comp_apply,id_eq]; ring)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationBasisCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def zeroSignedWord : SignedWords := (false,([],[true]))
 def unsignedIntegerWord (A : List Bool) : SignedWords := (false,(A,[true]))
 def unsignedIntegerRealizer : Realizer unsignedIntegerWord :=
   (Realizer.constant false).pair (Realizer.id.pair (Realizer.constant [true]))
 
 def diagonalWord (s : ℕ×(ℕ×SignedWords)) : SignedWords := if s.1=s.2.1 then s.2.2 else zeroSignedWord
 def diagonalWordRealizer : Realizer diagonalWord :=
   ((((Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp Realizer.eqNat).pair Realizer.id).comp
     ((Realizer.snd.comp Realizer.snd).choose (Realizer.constant zeroSignedWord))).congr (fun s => by
       dsimp only [Function.comp_apply,diagonalWord]
       simp only [decide_eq_true_eq,id_eq])
 
 def approximationDiagonal (s : ℕ×(ℕ×SignedWords)) : SignedVector :=
   (List.range s.1).map (fun j => diagonalWord (j,s.2))++[zeroSignedWord]
 def approximationDiagonalRealizer : Realizer approximationDiagonal :=
   (((((Realizer.fst.comp Realizer.range).pair Realizer.snd).comp (mapEnvironment diagonalWordRealizer))).pair
     (Realizer.constant [zeroSignedWord])).comp appendList
 
 def approximationDiagonalRows (s : ℕ×SignedWords) : List SignedVector :=
   (List.range s.1).map (fun i => approximationDiagonal (s.1,(i,s.2)))
 def approximationRowEnvironment : Realizer (fun s : ℕ×(ℕ×SignedWords) => (s.2.1,(s.1,s.2.2))) :=
   (Realizer.snd.comp Realizer.fst).pair (Realizer.fst.pair (Realizer.snd.comp Realizer.snd))
 
 def approximationDiagonalRowsRealizer : Realizer approximationDiagonalRows :=
   ((Realizer.fst.comp Realizer.range).pair Realizer.id).comp
     (mapEnvironment (approximationRowEnvironment.comp approximationDiagonalRealizer))
 
 def approximationWords (s : SignedVector×(List Bool×List Bool)) : List SignedVector :=
   approximationDiagonalRows (s.1.length,unsignedIntegerWord s.2.1)++
     [vectorScale (s.1,unsignedIntegerWord s.2.1)++[unsignedIntegerWord s.2.2]]
 def approximationLastRowRealizer : Realizer (fun s : SignedVector×(List Bool×List Bool) =>
     vectorScale (s.1,unsignedIntegerWord s.2.1)++[unsignedIntegerWord s.2.2]) :=
   (((Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).comp unsignedIntegerRealizer)).comp vectorScaleRealizer).pair
     ((((Realizer.snd.comp Realizer.snd).comp unsignedIntegerRealizer).pair (Realizer.constant ([]:SignedVector))).comp Realizer.cons)).comp appendList
 
 def approximationWordsRealizer : Realizer approximationWords :=
   (((((Realizer.fst.comp listLength).pair ((Realizer.snd.comp Realizer.fst).comp unsignedIntegerRealizer)).comp
     approximationDiagonalRowsRealizer)).pair
       ((approximationLastRowRealizer.pair (Realizer.constant ([]:List SignedVector))).comp Realizer.cons)).comp appendList

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidScalarCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def scalarOne : SignedWords := unsignedIntegerWord [true]
 def scalarTwo : SignedWords := unsignedIntegerWord [false,true]
 def naturalSignedWord : ℕ → SignedWords := unsignedIntegerWord ∘ natBits
 def naturalSignedWordRealizer : Realizer naturalSignedWord := naturalWordRealizer.comp unsignedIntegerRealizer
 
 def shapeDimensionSquare : ℕ → SignedWords := (fun s => canonicalMul (s,s)) ∘ naturalSignedWord
 def shapeDimensionSquareRealizer : Realizer shapeDimensionSquare := (naturalSignedWordRealizer.pair naturalSignedWordRealizer).comp canonicalMulRealizer
 
 def shapeDimensionDenominator (n : ℕ) : SignedWords := canonicalSub (shapeDimensionSquare n,scalarOne)
 def shapeDimensionDenominatorRealizer : Realizer shapeDimensionDenominator :=
   (shapeDimensionSquareRealizer.pair (Realizer.constant scalarOne)).comp canonicalSubRealizer
 
 def shapeDimensionCoefficient (n : ℕ) : SignedWords := canonicalDiv (shapeDimensionSquare n,shapeDimensionDenominator n)
 def shapeDimensionCoefficientRealizer : Realizer shapeDimensionCoefficient :=
   (shapeDimensionSquareRealizer.pair shapeDimensionDenominatorRealizer).comp canonicalDivRealizer
 
 def nextDimensionWord (n : ℕ) : SignedWords := canonicalAdd (naturalSignedWord n,scalarOne)
 def nextDimensionWordRealizer : Realizer nextDimensionWord := (naturalSignedWordRealizer.pair (Realizer.constant scalarOne)).comp canonicalAddRealizer
 
 def shapeCutDenominator (s : ℕ×SignedWords) : SignedWords := canonicalMul (nextDimensionWord s.1,s.2)
 def shapeCutDenominatorRealizer : Realizer shapeCutDenominator :=
   ((Realizer.fst.comp nextDimensionWordRealizer).pair Realizer.snd).comp canonicalMulRealizer
 
 def shapeCutCoefficient : ℕ×SignedWords → SignedWords := (fun s => canonicalDiv (scalarTwo,s)) ∘ shapeCutDenominator
 def shapeCutCoefficientRealizer : Realizer shapeCutCoefficient :=
   ((Realizer.constant scalarTwo).pair shapeCutDenominatorRealizer).comp canonicalDivRealizer
 
 def centerCutCoefficient : ℕ×SignedWords → SignedWords := (fun s => canonicalDiv (scalarOne,s)) ∘ shapeCutDenominator
 def centerCutCoefficientRealizer : Realizer centerCutCoefficient :=
   ((Realizer.constant scalarOne).pair shapeCutDenominatorRealizer).comp canonicalDivRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseStepCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev MatrixInverseState := SignedMatrix×SignedMatrix
 abbrev MatrixInverseStepInput := ℕ×MatrixInverseState
 def inverseOriginalRow : Realizer (fun s : MatrixInverseStepInput => (s.2.1.drop s.1).headD []) :=
   (((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp (lookupList ([]:SignedVector)))
 
 def inverseOriginalPivotRealizer : Realizer (fun s : MatrixInverseStepInput =>
     (((s.2.1.drop s.1).headD []).drop s.1).headD signedZero) :=
   (inverseOriginalRow.pair Realizer.fst).comp (lookupList signedZero)
 
 def inverseColumn (s : MatrixInverseStepInput) : SignedVector :=
   (matrixColumn (s.2.1,s.1)).take s.1
 def inverseColumnRealizer : Realizer inverseColumn :=
   (Realizer.fst.pair (((Realizer.snd.comp Realizer.fst).pair Realizer.fst).comp matrixColumnRealizer)).comp takeList
 
 def inverseZ (s : MatrixInverseStepInput) : SignedVector := matrixVector (s.2.2,inverseColumn s)
 def inverseZRealizer : Realizer inverseZ := ((Realizer.snd.comp Realizer.snd).pair inverseColumnRealizer).comp matrixVectorRealizer
 
 def inverseSchur (s : MatrixInverseStepInput) : SignedWords :=
   canonicalSub ((((s.2.1.drop s.1).headD []).drop s.1).headD signedZero,signedDot (inverseColumn s,inverseZ s))
 def inverseSchurRealizer : Realizer inverseSchur :=
   (inverseOriginalPivotRealizer.pair ((inverseColumnRealizer.pair inverseZRealizer).comp signedDotRealizer)).comp canonicalSubRealizer
 
 def inverseReciprocal : MatrixInverseStepInput → SignedWords := (fun q => canonicalDiv (scalarOne,q)) ∘ inverseSchur
 def inverseReciprocalRealizer : Realizer inverseReciprocal := ((Realizer.constant scalarOne).pair inverseSchurRealizer).comp canonicalDivRealizer
 
 def inverseNegative (s : MatrixInverseStepInput) : SignedWords := canonicalSub (signedZero,inverseReciprocal s)
 def inverseNegativeRealizer : Realizer inverseNegative := ((Realizer.constant signedZero).pair inverseReciprocalRealizer).comp canonicalSubRealizer
 
 def inverseUpperBlock (s : MatrixInverseStepInput) : SignedMatrix :=
   matrixAdd (s.2.2,matrixScale (matrixOuter (inverseZ s,inverseZ s),inverseReciprocal s))
 def inverseUpperBlockRealizer : Realizer inverseUpperBlock :=
   ((Realizer.snd.comp Realizer.snd).pair ((((inverseZRealizer.pair inverseZRealizer).comp matrixOuterRealizer).pair inverseReciprocalRealizer).comp matrixScaleRealizer)).comp matrixAddRealizer
 
 def inverseBorderVector (s : MatrixInverseStepInput) : SignedVector := vectorScale (inverseZ s,inverseNegative s)
 def inverseBorderVectorRealizer : Realizer inverseBorderVector := (inverseZRealizer.pair inverseNegativeRealizer).comp vectorScaleRealizer
 
 def inverseNextData (s : MatrixInverseStepInput) : SignedMatrix×(SignedVector×SignedWords) :=
   (inverseUpperBlock s,(inverseBorderVector s,inverseReciprocal s))
 def inverseNextDataRealizer : Realizer inverseNextData :=
   inverseUpperBlockRealizer.pair (inverseBorderVectorRealizer.pair inverseReciprocalRealizer)
 
 def inverseNext : MatrixInverseStepInput → SignedMatrix := normalizeMatrix ∘ borderMatrixWords ∘ inverseNextData
 def inverseNextRealizer : Realizer inverseNext := (inverseNextDataRealizer.comp borderMatrixWordsRealizer).comp normalizeMatrixRealizer
 
 def inverseStep (s : MatrixInverseStepInput) : MatrixInverseState := (s.2.1,inverseNext s)
 def inverseStepRealizer : Realizer inverseStep := (Realizer.snd.comp Realizer.fst).pair inverseNextRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseLoopCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def matrixInverseInitialize (orig : SignedMatrix) : List ℕ×MatrixInverseState :=
   (List.range orig.length,(orig,[]))
 def matrixInverseInitializeRealizer : Realizer matrixInverseInitialize :=
   ((listLength.comp Realizer.range).pair (Realizer.id.pair (Realizer.constant ([]:SignedMatrix))))
 
 def matrixInverseFold (orig : SignedMatrix) : MatrixInverseState :=
   (List.range orig.length).foldl (fun state i => inverseStep (i,state)) (orig,[])
 def matrixInverseFoldRealizer : Realizer matrixInverseFold := matrixInverseInitializeRealizer.comp inverseStepRealizer.fold
 def matrixInverseWords : SignedMatrix → SignedMatrix := Prod.snd ∘ matrixInverseFold
 def matrixInverseWordsRealizer : Realizer matrixInverseWords := matrixInverseFoldRealizer.comp Realizer.snd

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorTake
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixBorderSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BorderedInverse
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 def borderInv {K : Type} [Field K] {n : ℕ} (B : Matrix (Fin n) (Fin n) K) (z : Fin n → K) (t : K) :
     Matrix (Fin (n+1)) (Fin (n+1)) K :=
   border (B+t⁻¹ • Matrix.vecMulVec z z) ((-t⁻¹) • z) t⁻¹

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.BorderedPositive
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.InverseMath

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.RationalMatrixCast
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 def castMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ := A.map (Rat.castHom ℝ)
 def castVector {n : ℕ} (a : Fin n → ℚ) : Fin n → ℝ := fun i => (a i:ℝ)

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.PrincipalMatrix
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 def principal {K : Type} {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k≤ n) :
     Matrix (Fin k) (Fin k) K := A.submatrix (Fin.castLE hk) (Fin.castLE hk)
 def principalColumn {K : Type} {n k : ℕ} (A : Matrix (Fin n) (Fin n) K) (hk : k< n) : Fin k → K :=
   fun i => A ⟨i.val,by omega⟩ ⟨k,hk⟩

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.VectorPrefix
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLSwapCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
variable {α : Type} [Coding α]

 def swapOld (a : α) : Realizer (fun s : ℕ×List α => (s.2.drop s.1).headD a) :=
   (Realizer.snd.pair Realizer.fst).comp (lookupList a)
 def swapNew (a : α) : Realizer (fun s : ℕ×List α => (s.2.drop (s.1+1)).headD a) :=
   (Realizer.snd.pair (Realizer.fst.comp Realizer.succ)).comp (lookupList a)

 def swapFirst (a : α) (s : ℕ×List α) : List α :=
   replaceList a (s.2,(s.1,(s.2.drop (s.1+1)).headD a))
 def swapFirstRealizer (a : α) : Realizer (swapFirst a) :=
   (Realizer.snd.pair (Realizer.fst.pair (swapNew a))).comp (replaceListRealizer a)
 
 def swapAdjacent (a : α) (s : ℕ×List α) : List α :=
   replaceList a (swapFirst a s,(s.1+1,(s.2.drop s.1).headD a))
 def swapAdjacentRealizer (a : α) : Realizer (swapAdjacent a) :=
   ((swapFirstRealizer a).pair ((Realizer.fst.comp Realizer.succ).pair (swapOld a))).comp (replaceListRealizer a)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRoundCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev FinishPassInput := (Bool×ℕ)×WordBasisState
 def finishContinue : Realizer (fun s : FinishPassInput =>
     (false,swapAdjacent [] (s.1.2,s.2.1))) :=
   (Realizer.constant false).pair
     ((((Realizer.fst.comp Realizer.snd).pair (Realizer.snd.comp Realizer.fst)).comp (swapAdjacentRealizer [])))
 
 def finishDone : Realizer (fun s : FinishPassInput => (true,s.2.1)) :=
   (Realizer.constant true).pair (Realizer.snd.comp Realizer.fst)
 
 def finishWithBad (s : FinishPassInput) : Bool×List SignedVector :=
   if s.1.1 then (false,swapAdjacent [] (s.1.2,s.2.1)) else (true,s.2.1)
 def finishWithBadRealizer : Realizer finishWithBad :=
   (((Realizer.fst.comp Realizer.fst).pair Realizer.id).comp (finishContinue.choose finishDone)).congr (fun _ => rfl)
 
 def finishPass (s : WordBasisState) : Bool×List SignedVector := finishWithBad (findBadCode s,s)
 def finishPassRealizer : Realizer finishPass :=
   (findBadCodeRealizer.pair Realizer.id).comp finishWithBadRealizer
 
 def basisRound (bs : List SignedVector) : Bool×List SignedVector := finishPass (sizePassCode bs)
 def basisRoundRealizer : Realizer basisRound := sizePassCodeRealizer.comp finishPassRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLoopCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler

 abbrev ReductionState := Bool×List SignedVector
 def reductionActive : ReductionState → ReductionState := basisRound ∘ Prod.snd
 def reductionActiveRealizer : Realizer reductionActive := Realizer.snd.comp basisRoundRealizer
 def reductionBody (s : ReductionState) : ReductionState := if s.1 then s else reductionActive s
 def reductionBodyRealizer : Realizer reductionBody :=
   ((Realizer.fst.pair Realizer.id).comp (Realizer.id.choose reductionActiveRealizer)).congr (fun _ => rfl)
 def reductionLoop (s : ℕ×List SignedVector) : ReductionState :=
   reductionBody^[s.1] (false,s.2)
 def reductionLoopRealizer : Realizer reductionLoop :=
   (Realizer.fst.pair ((Realizer.constant false).pair Realizer.snd)).comp reductionBodyRealizer.iterate

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLovaszQueryMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFindBadMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReducedNormBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLFullSwap
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 def FullSwap {n : ℕ} (b c : Fin n → Vec n) : Prop :=
   ∃ d, SizePass n b d ∧ ∃ (k : ℕ) (hk : 2≤ k ∧ k≤ n), Cond119 d k ∧
     c=d ∘ Equiv.swap (⟨k-2,by omega⟩:Fin n) ⟨k-1,by omega⟩

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLRoundMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBoundedFullReduction
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

inductive FullTrace {n : ℕ} (b : Fin n → Vec n) : ℕ → (Fin n → Vec n) → Prop
 | zero : FullTrace b 0 b
 | succ {t c d} (prefixTrace : FullTrace b t c) (step : FullSwap c d) : FullTrace b (t+1) d

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLSizeNormGrowth
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLPassNorm
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLUniformTrace
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLLoopInvariant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 structure BasisInvariant {n : ℕ} (original : Fin n → Vec n) (H : ℕ) (b : Fin n → Vec n) : Prop where
   linear : LinearIndependent ℝ b
   integral : IntegralRows b
   lattice : latticeOf b=latticeOf original
   gram : ∀ k≤ n,1≤ LLLFactor.Reduction.gram b k ∧ LLLFactor.Reduction.gram b k≤(2:ℝ)^H
   norm : ∀ k,‖b k‖≤(n+1)*((2:ℝ)^H+1)

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 def ReductionGood {n : ℕ} (original : Fin n → Vec n) (H t : ℕ) (s : ReductionState) : Prop :=
   ∃ (b : Fin n → Vec n) (A : Fin n → SignedVector), s.2=List.ofFn A ∧
     (∀ k,RepresentsVector (A k) (b k)) ∧ (∀ k,VectorCanonical (A k)) ∧
     BasisInvariant original H b ∧ (s.1=true → IsReduced b) ∧ (s.1=false → FullTrace original t b)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLoopCorrect
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLowerTrace
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 inductive LowerTrace {n : ℕ} (i : Fin n) (b : Fin n → Vec n) : ℕ → (Fin n → Vec n) → Prop
 | zero : LowerTrace i b 0 b
 | succ {t c} (prior : LowerTrace i b t c) (j : Fin n) (hj : j< i) (r : ℤ)
     (near : IsNearestInt r (mu c i j)) : LowerTrace i b (t+1) (reduceBy c i j r)

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLBitGrowthPower
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 def intermediateExponent (n H : ℕ) : ℕ := H+n+3+n*(3*H+n+6)

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLPassInitializeClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLowerWordTrace
noncomputable section

open scoped Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerBasisWordBounds
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRowWordBudget
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLFullPassBudget
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialComposedFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.LLLRowClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRowIterationClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.FoldLocalClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.LLLFullSizeClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialPipelineClock
noncomputable section

set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.RuntimeMath

end EdgeSublinearMWIS.Main.RuntimeMath
end

-- Solutions.LLLSizePassClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLRoundClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBodyClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLLoopClock
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLInitialInvariant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

 def encodedExponent (S : ℕ) : ℕ := 100*(S+1)^5

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.StreamParserIteration
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ProjectionSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open WeightedHelpers

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordArrayCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SparsePathParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixRowsParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev MatrixReadState := ℕ×(List Bool×List (List SignedWords))
 def readMatrixRow : Realizer (fun s : MatrixReadState => readMany s.1 s.2.1) :=
   (Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp readManyRealizer
 
 def readMatrixStep (s : MatrixReadState) : MatrixReadState :=
   let row := readMany s.1 s.2.1
   (s.1,(row.2,row.1::s.2.2))
 def readMatrixStepRealizer : Realizer readMatrixStep := Realizer.fst.pair
   ((readMatrixRow.comp Realizer.snd).pair
     (((readMatrixRow.comp Realizer.fst).pair (Realizer.snd.comp Realizer.snd)).comp Realizer.cons))

 def readMatrixRows (s : ℕ×List Bool) : List (List SignedWords)×List Bool :=
   let t := readMatrixStep^[s.1] (s.1,(s.2,[]))
   (t.2.2.reverse,t.2.1)
 def readMatrixRowsRealizer : Realizer readMatrixRows :=
   ((Realizer.fst.pair (Realizer.fst.pair (Realizer.snd.pair (Realizer.constant ([] : List (List SignedWords)))))).comp
     readMatrixStepRealizer.iterate).comp
       (((Realizer.snd.comp Realizer.snd).comp Realizer.reverse).pair (Realizer.snd.comp Realizer.fst))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBitProgramCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 def encodedExponentRealizer : Realizer encodedExponent :=
   ((Realizer.constant (100:ℕ)).pair (Realizer.succ.comp naturalFifth)).comp naturalProductRealizer
 
 def reductionCount (S : ℕ) : ℕ := 4*(encodedExponent S+1)
 def reductionCountRealizer : Realizer reductionCount :=
   ((Realizer.constant (4:ℕ)).pair (encodedExponentRealizer.comp Realizer.succ)).comp naturalProductRealizer
 
 def parseIntegerMatrix (L : List Bool) : List SignedVector := (readMatrixRows (readNatural L)).1
 def parseIntegerMatrixRealizer : Realizer parseIntegerMatrix :=
   (readNaturalRealizer.comp readMatrixRowsRealizer).comp Realizer.fst
 
 def prepareReduction (L : List Bool) : ℕ×List SignedVector :=
   (reductionCount L.length,parseIntegerMatrix L)
 def prepareReductionRealizer : Realizer prepareReduction :=
   (listLength.comp reductionCountRealizer).pair parseIntegerMatrixRealizer

 def serializeRow (A : SignedVector) : List Bool := A.flatMap rationalBits
 def serializeRowRealizer : Realizer serializeRow :=
   ((mapList rationalBitsRealizer).comp flattenList).congr (fun _ => by simp only [Function.comp_apply,serializeRow,List.flatMap_def] )
 
 def serializeMatrix (bs : List SignedVector) : List Bool := encodeNat bs.length++bs.flatMap serializeRow
 def serializePayloadRealizer : Realizer (fun bs : List SignedVector => bs.flatMap serializeRow) :=
   ((mapList serializeRowRealizer).comp flattenList).congr (fun _ => by simp only [Function.comp_apply,List.flatMap_def])
 
 def serializeMatrixRealizer : Realizer serializeMatrix :=
   ((listLength.comp naturalCodeRealizer).pair serializePayloadRealizer).comp appendBits
 
 def finishReduction : ReductionState → List Bool := serializeMatrix ∘ Prod.snd
 def finishReductionRealizer : Realizer finishReduction := Realizer.snd.comp serializeMatrixRealizer
 
 def integerLLL : List Bool → List Bool := finishReduction ∘ reductionLoop ∘ prepareReduction
 def integerLLLRealizer : Realizer integerLLL := (prepareReductionRealizer.comp reductionLoopRealizer).comp finishReductionRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerMatrixEncoding
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def integerCode (z : ℤ) : RationalCode := ⟨z,1,by omega⟩

 def integerWords {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Fin n → SignedVector :=
   fun i => List.ofFn (fun j => codeWords (integerCode (B i j)))
 def integerMatrixInput {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : List Bool :=
   encodeNat n++(List.ofFn (fun i => (List.ofFn (fun j => encodeRat (B i j:ℚ))).flatten)).flatten

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixRowsParserMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBitProgramMath
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLDeterminantTrace
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 def ReductionGram {n : ℕ} (original : Fin n → Vec n) (s : ReductionState) : Prop :=
   ∃ (b : Fin n → Vec n) (A : Fin n → SignedVector),s.2=List.ofFn A ∧
     (∀ i,RepresentsVector (A i) (b i)) ∧ (∀ i,VectorCanonical (A i)) ∧
     LinearIndependent ℝ b ∧ gram b n=gram original n

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RepresentedBasisUnique
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLReducedGramBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLFirstVectorBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.LLLBitGram
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.IntegerBasisDeterminant
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineLattice
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

 def approximationBasis {n : ℕ} (a : Fin n → ℤ) (T U : ℤ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
   fun i j => if hi : i.val< n then (if i=j then T else 0)
     else if hj : j.val< n then a ⟨j.val,hj⟩ else U

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.ApproximationBasisSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidScalarSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedMatrixRoundingSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseStepSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseLoopSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath

 def inversePrefix (orig : SignedMatrix) (k : ℕ) : MatrixInverseState :=
   (List.range k).foldl (fun state i => inverseStep (i,state)) (orig,[])

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSDeterminantBounds
noncomputable section
-- Adapted from EdouardBonnet/lax-109476, commit0a042604c7ae1ef4cd9a4c7d82eb902f313d4864.
-- Apache-2.0; original license retained in external-lp/LICENSE.

open scoped BigOperators Matrix

namespace EdgeSublinearMWIS.Main.GLS.DeterminantBounds

end EdgeSublinearMWIS.Main.GLS.DeterminantBounds
end

-- Solutions.IntegerMatrixInverseFormula
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.MatrixDenominatorBounds
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 def matrixDen {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : ℕ := ∏ i,∏ j,(A i j).den

 def clearedMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℤ :=
   fun i j => (A i j).num*(matrixDen A/(A i j).den:ℕ)

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.MatrixInverseHeight
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.InverseMath

 def inverseHeight (N H : ℕ) : ℕ := N*N*H+N*N+((N*N+1)*H)*N

end EdgeSublinearMWIS.Main.InverseMath
end

-- Solutions.MatrixInverseClockBounds
noncomputable section

open scoped Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseClock
noncomputable section

open scoped Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ThinDirectionCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev ThinDirectionData := SignedMatrix×DiagonalEntry
 def thinDirectionReciprocal (s : ThinDirectionData) : SignedWords := canonicalDiv (scalarOne,s.2.2)
 def thinDirectionReciprocalRealizer : Realizer thinDirectionReciprocal :=
   ((Realizer.constant scalarOne).pair (Realizer.snd.comp Realizer.snd)).comp canonicalDivRealizer
 
 def thinDirectionColumn (s : ThinDirectionData) : SignedVector := matrixColumn (s.1,s.2.1)
 def thinDirectionColumnRealizer : Realizer thinDirectionColumn :=
   (Realizer.fst.pair (Realizer.snd.comp Realizer.fst)).comp matrixColumnRealizer
 
 def normalizedDirectionWords : ThinDirectionData → SignedVector :=
   vectorScale ∘ (fun s => (thinDirectionColumn s,thinDirectionReciprocal s))
 def normalizedDirectionWordsRealizer : Realizer normalizedDirectionWords :=
   (thinDirectionColumnRealizer.pair thinDirectionReciprocalRealizer).comp vectorScaleRealizer
 
 def thinDirectionData (bs : SignedMatrix) : ThinDirectionData := (bs,maximumDiagonal bs)
 def thinDirectionDataRealizer : Realizer thinDirectionData := Realizer.id.pair maximumDiagonalRealizer
 
 def thinDirectionFinish (s : ThinDirectionData) : SignedVector×ℕ := (normalizedDirectionWords s,s.2.1)
 def thinDirectionFinishRealizer : Realizer thinDirectionFinish := normalizedDirectionWordsRealizer.pair (Realizer.snd.comp Realizer.fst)
 
 def inverseThinDirection : SignedMatrix → SignedVector×ℕ := thinDirectionFinish ∘ thinDirectionData
 def inverseThinDirectionRealizer : Realizer inverseThinDirection := thinDirectionDataRealizer.comp thinDirectionFinishRealizer
 
 def ellipsoidThinDirection : SignedMatrix → SignedVector×ℕ := inverseThinDirection ∘ matrixInverseWords
 def ellipsoidThinDirectionRealizer : Realizer ellipsoidThinDirection := matrixInverseWordsRealizer.comp inverseThinDirectionRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationModuliCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def commonDenominatorWord (A : SignedVector) : List Bool := wordProduct (A.map (fun s => s.2.2))
 def commonDenominatorRealizer : Realizer commonDenominatorWord :=
   (mapList (Realizer.snd.comp Realizer.snd)).comp wordProductRealizer
 
 def precisionExponent (s : ℕ×SignedVector) : ℕ := (s.2.length+1)*(s.1+s.2.length+2)
 def precisionSum : Realizer (fun s : ℕ×SignedVector => s.1+s.2.length+2) :=
   (((Realizer.fst.pair (Realizer.snd.comp listLength)).comp Realizer.add).comp Realizer.succ).comp Realizer.succ
 
 def precisionExponentRealizer : Realizer precisionExponent :=
   (((Realizer.snd.comp listLength).comp Realizer.succ).pair precisionSum).comp naturalProductRealizer
 
 def approximationModuli (s : ℕ×SignedVector) : List Bool×List Bool :=
   (multiply (commonDenominatorWord s.2) (powerTwoWord (precisionExponent s)),commonDenominatorWord s.2)
 def approximationModuliRealizer : Realizer approximationModuli :=
   ((((Realizer.snd.comp commonDenominatorRealizer).pair (precisionExponentRealizer.comp powerTwoWordRealizer)).comp multiplyRealizer)).pair
     (Realizer.snd.comp commonDenominatorRealizer)
 
 def approximationMatrixWords (s : ℕ×SignedVector) : List SignedVector := approximationWords (s.2,approximationModuli s)
 def approximationMatrixWordsRealizer : Realizer approximationMatrixWords :=
   (Realizer.snd.pair approximationModuliRealizer).comp approximationWordsRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationModuliMath
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

 def denominatorProduct {n : ℕ} (q : Fin n → RationalCode) : ℕ := ∏ i,(q i).denominator

 def approximationNumerator {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) (i : Fin n) : ℤ :=
   (q i).numerator*(denominatorProduct q/(q i).denominator:ℕ)*2^((n+1)*(r+n+2))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.LLLBitProgramClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationPipelineCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def approximationInput : ℕ×SignedVector → List Bool := serializeMatrix ∘ approximationMatrixWords
 def approximationInputRealizer : Realizer approximationInput := approximationMatrixWordsRealizer.comp serializeMatrixRealizer
 
 def approximationReducedWords : ℕ×SignedVector → List SignedVector := parseIntegerMatrix ∘ integerLLL ∘ approximationInput
 def approximationReducedWordsRealizer : Realizer approximationReducedWords :=
   (approximationInputRealizer.comp integerLLLRealizer).comp parseIntegerMatrixRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PolynomialRestrictedComposition
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ApproximationPipelineMath
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds LLLBounds

 def ValidApproximationInput (s : ℕ×SignedVector) : Prop :=
   ∃ (n : ℕ) (q : Fin n → RationalCode),s.2=List.ofFn (fun i => codeWords (q i))
 def approximationIntegerBasis {n : ℕ} (q : Fin n → RationalCode) (r : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℤ :=
   approximationBasis (approximationNumerator q r)
     ((denominatorProduct q:ℤ)*2^((n+1)*(r+n+2))) (denominatorProduct q)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationExtractCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev ApproximationExtractInput := SignedVector×((List Bool×List Bool)×SignedVector)
 def extractBasisLast (s : ApproximationExtractInput) : SignedWords :=
   (s.2.2.drop s.1.length).headD zeroSignedWord
 def extractBasisLastRealizer : Realizer extractBasisLast :=
   ((Realizer.snd.comp Realizer.snd).pair (Realizer.fst.comp listLength)).comp (lookupList zeroSignedWord)
 
 def extractApproximationDenominator (s : ApproximationExtractInput) : SignedWords :=
   canonicalDiv (extractBasisLast s,unsignedIntegerWord s.2.1.2)
 def extractApproximationDenominatorRealizer : Realizer extractApproximationDenominator :=
   (extractBasisLastRealizer.pair (((Realizer.snd.comp Realizer.fst).comp Realizer.snd).comp unsignedIntegerRealizer)).comp canonicalDivRealizer
 
 def extractReciprocalRealizer : Realizer (fun s : ApproximationExtractInput =>
     canonicalDiv (unsignedIntegerWord [true],unsignedIntegerWord s.2.1.1)) :=
   ((Realizer.constant (unsignedIntegerWord [true])).pair
     (((Realizer.snd.comp Realizer.fst).comp Realizer.fst).comp unsignedIntegerRealizer)).comp canonicalDivRealizer
 
 def extractBasisPrefixRealizer : Realizer (fun s : ApproximationExtractInput => s.2.2.take s.1.length) :=
   ((Realizer.fst.comp listLength).pair (Realizer.snd.comp Realizer.snd)).comp takeList
 
 def extractApproximationNumerators (s : ApproximationExtractInput) : SignedVector :=
   vectorSub (vectorScale (s.1,extractApproximationDenominator s),
     vectorScale (s.2.2.take s.1.length,canonicalDiv (unsignedIntegerWord [true],unsignedIntegerWord s.2.1.1)))
 def extractApproximationNumeratorsRealizer : Realizer extractApproximationNumerators :=
   (((Realizer.fst.pair extractApproximationDenominatorRealizer).comp vectorScaleRealizer).pair
     ((extractBasisPrefixRealizer.pair extractReciprocalRealizer).comp vectorScaleRealizer)).comp vectorSubRealizer
 
 def extractApproximation (s : ApproximationExtractInput) : SignedVector×SignedWords :=
   (extractApproximationNumerators s,extractApproximationDenominator s)
 def extractApproximationRealizer : Realizer extractApproximation := extractApproximationNumeratorsRealizer.pair extractApproximationDenominatorRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiophantineWordAlgorithm
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def approximationFirstReduced : ℕ×SignedVector → SignedVector := (fun bs : List SignedVector => bs.headD []) ∘ approximationReducedWords
 def approximationFirstReducedRealizer : Realizer approximationFirstReduced := approximationReducedWordsRealizer.comp (headList ([]:SignedVector))
 def approximationExtractionData (s : ℕ×SignedVector) : ApproximationExtractInput :=
   (s.2,(approximationModuli s,approximationFirstReduced s))
 def approximationExtractionDataRealizer : Realizer approximationExtractionData :=
   Realizer.snd.pair (approximationModuliRealizer.pair approximationFirstReducedRealizer)
 def simultaneousApproximation : ℕ×SignedVector → SignedVector×SignedWords := extractApproximation ∘ approximationExtractionData
 def simultaneousApproximationRealizer : Realizer simultaneousApproximation :=
   approximationExtractionDataRealizer.comp extractApproximationRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiophantineWordClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationExtractSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ApproximationExtractInteger
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiophantineCoordinates
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineExtract
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineNormBound
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.LLLBounds

end EdgeSublinearMWIS.Main.LLLBounds
end

-- Solutions.DiophantineWordCorrect
noncomputable section

open scoped BigOperators Classical
open LLLFactor.RedBasis LLLFactor.Reduction
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open LLLBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CanonicalApproximation
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def rationalCode (q : ℚ) : RationalCode := ⟨q.num,q.den,q.den_pos⟩

 def canonicalApproximationInput (s : ℕ×SignedVector) : ℕ×SignedVector := (s.1,normalizeVector s.2)
 def canonicalApproximationInputRealizer : Realizer canonicalApproximationInput :=
   Realizer.fst.pair (Realizer.snd.comp normalizeVectorRealizer)
 
 def canonicalApproximation : ℕ×SignedVector → SignedVector×SignedWords := simultaneousApproximation ∘ canonicalApproximationInput
 def canonicalApproximationRealizer : Realizer canonicalApproximation := canonicalApproximationInputRealizer.comp simultaneousApproximationRealizer

 def ValidRationalVector (s : ℕ×SignedVector) : Prop :=
   ∃ (n : ℕ) (a : Fin n → ℚ),RepresentsVector s.2 (rationalVector a)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplaneApproximationCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev HyperplaneApproximationInput := ℕ×(SignedVector×SignedVector)
 def hyperplaneBeta (s : HyperplaneApproximationInput) : SignedWords :=
   canonicalMul (naturalSignedWord (s.1+1),signedDot s.2)
 def hyperplaneBetaRealizer : Realizer hyperplaneBeta :=
   (((Realizer.fst.comp Realizer.succ).comp naturalSignedWordRealizer).pair (Realizer.snd.comp signedDotRealizer)).comp canonicalMulRealizer
 
 def hyperplaneCoordinates (s : HyperplaneApproximationInput) : SignedVector :=
   appendCoordinate (s.2.1,hyperplaneBeta s)
 def hyperplaneCoordinatesRealizer : Realizer hyperplaneCoordinates :=
   ((Realizer.snd.comp Realizer.fst).pair hyperplaneBetaRealizer).comp appendCoordinateRealizer
 
 def hyperplanePrecision (s : HyperplaneApproximationInput) : ℕ := s.1+3
 def hyperplanePrecisionRealizer : Realizer hyperplanePrecision :=
   (((Realizer.fst.comp Realizer.succ).comp Realizer.succ).comp Realizer.succ)
 
 def hyperplaneApproximationData (s : HyperplaneApproximationInput) : ℕ×SignedVector :=
   (hyperplanePrecision s,hyperplaneCoordinates s)
 def hyperplaneApproximationDataRealizer : Realizer hyperplaneApproximationData := hyperplanePrecisionRealizer.pair hyperplaneCoordinatesRealizer
 
 def hyperplaneApproximation : HyperplaneApproximationInput → SignedVector×SignedWords := canonicalApproximation ∘ hyperplaneApproximationData
 def hyperplaneApproximationRealizer : Realizer hyperplaneApproximation := hyperplaneApproximationDataRealizer.comp canonicalApproximationRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidRecoveryCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev EllipsoidRecoveryInput := ℕ×(SignedMatrix×SignedVector)
 def ellipsoidRecoveryDirection (s : EllipsoidRecoveryInput) : SignedVector := (ellipsoidThinDirection s.2.1).1
 def ellipsoidRecoveryDirectionRealizer : Realizer ellipsoidRecoveryDirection :=
   (((Realizer.snd.comp Realizer.fst).comp ellipsoidThinDirectionRealizer).comp Realizer.fst)
 def ellipsoidRecoveryData (s : EllipsoidRecoveryInput) : HyperplaneApproximationInput :=
   (s.1,(ellipsoidRecoveryDirection s,s.2.2))
 def ellipsoidRecoveryDataRealizer : Realizer ellipsoidRecoveryData :=
   Realizer.fst.pair (ellipsoidRecoveryDirectionRealizer.pair (Realizer.snd.comp Realizer.snd))
 def ellipsoidRecovery : EllipsoidRecoveryInput → SignedVector×SignedWords := hyperplaneApproximation ∘ ellipsoidRecoveryData
 def ellipsoidRecoveryRealizer : Realizer ellipsoidRecovery := ellipsoidRecoveryDataRealizer.comp hyperplaneApproximationRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplanePrecision
noncomputable section

open scoped Classical
set_option autoImplicit false
namespace EdgeSublinearMWIS.Main.ConvexTools

 def thinExponent (n : ℕ) : ℕ := 10*(n+2)^2
 def approximationExponent (n : ℕ) : ℕ := (n+2)*((n+3)+(n+1)+2)

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.EllipsoidDyadicScalar
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def dyadicUnitWord (p : ℕ) : SignedWords := (false,([true],powerTwoWord p))
 def dyadicUnitWordRealizer : Realizer dyadicUnitWord :=
   (Realizer.constant false).pair ((Realizer.constant [true]).pair powerTwoWordRealizer)

 def enlargedUnitWord (p : ℕ) : SignedWords := canonicalAdd (scalarOne,dyadicUnitWord p)
 def enlargedUnitWordRealizer : Realizer enlargedUnitWord :=
   ((Realizer.constant scalarOne).pair dyadicUnitWordRealizer).comp canonicalAddRealizer

 def enlargementCoefficient : ℕ → SignedWords := (fun s => canonicalMul (s,s)) ∘ enlargedUnitWord
 def enlargementCoefficientRealizer : Realizer enlargementCoefficient :=
   (enlargedUnitWordRealizer.pair enlargedUnitWordRealizer).comp canonicalMulRealizer

 def roundingAllowance (s : ℕ×ℕ) : SignedWords := canonicalMul (naturalSignedWord s.1,dyadicUnitWord s.2)
 def roundingAllowanceRealizer : Realizer roundingAllowance :=
   ((Realizer.fst.comp naturalSignedWordRealizer).pair (Realizer.snd.comp dyadicUnitWordRealizer)).comp canonicalMulRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCutShapeCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev CutShapeInput := ℕ×(SignedMatrix×SignedVector)
 def cutDirection (s : CutShapeInput) : SignedVector := matrixVector s.2
 def cutDirectionRealizer : Realizer cutDirection := Realizer.snd.comp matrixVectorRealizer
 
 def cutQuadratic (s : CutShapeInput) : SignedWords := signedDot (s.2.2,cutDirection s)
 def cutQuadraticRealizer : Realizer cutQuadratic := ((Realizer.snd.comp Realizer.snd).pair cutDirectionRealizer).comp signedDotRealizer
 
 def cutRankOne (s : CutShapeInput) : SignedMatrix := matrixOuter (cutDirection s,cutDirection s)
 def cutRankOneRealizer : Realizer cutRankOne := (cutDirectionRealizer.pair cutDirectionRealizer).comp matrixOuterRealizer
 
 def cutRankScalar (s : CutShapeInput) : SignedWords := shapeCutCoefficient (s.1,cutQuadratic s)
 def cutRankScalarRealizer : Realizer cutRankScalar := (Realizer.fst.pair cutQuadraticRealizer).comp shapeCutCoefficientRealizer
 
 def cutRankCorrection (s : CutShapeInput) : SignedMatrix := matrixScale (cutRankOne s,cutRankScalar s)
 def cutRankCorrectionRealizer : Realizer cutRankCorrection := (cutRankOneRealizer.pair cutRankScalarRealizer).comp matrixScaleRealizer
 
 def cutDifference (s : CutShapeInput) : SignedMatrix := matrixSub (s.2.1,cutRankCorrection s)
 def cutDifferenceRealizer : Realizer cutDifference := ((Realizer.snd.comp Realizer.fst).pair cutRankCorrectionRealizer).comp matrixSubRealizer
 
 def cutShapeWords (s : CutShapeInput) : SignedMatrix := matrixScale (cutDifference s,shapeDimensionCoefficient s.1)
 def cutShapeWordsRealizer : Realizer cutShapeWords :=
   (cutDifferenceRealizer.pair (Realizer.fst.comp shapeDimensionCoefficientRealizer)).comp matrixScaleRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidStep
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidStep.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Internal lemmas for the ellipsoid algorithm. These establish the normalized
central-cut matrix update, containment, and determinant shrink factor. They do not yet
establish a rounded rational algorithm or a RAM runtime bound.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStep

open Matrix

end EdgeSublinearMWIS.Main.GLS.EllipsoidStep
end

-- Solutions.GLSEllipsoidRounding
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidRounding.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
Internal shape-rounding lemmas. Entrywise rounding needs a diagonal enlargement:
entrywise inequalities alone do not imply containment of ellipsoids.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidRounding

open Matrix

end EdgeSublinearMWIS.Main.GLS.EllipsoidRounding
end

-- Solutions.GLSEllipsoidBounds
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidBounds.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Internal conditioning and precision bounds for general central-cut shapes. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidBounds

open Matrix EllipsoidRounding

end EdgeSublinearMWIS.Main.GLS.EllipsoidBounds
end

-- Solutions.EllipsoidCutShapeSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixDiagonalCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def diagonalRow (s : ℕ×(ℕ×SignedWords)) : SignedVector :=
   (List.range s.1).map (fun j => diagonalWord (j,s.2))
 def diagonalRowRealizer : Realizer diagonalRow :=
   ((Realizer.fst.comp Realizer.range).pair Realizer.snd).comp (mapEnvironment diagonalWordRealizer)
 
 def matrixDiagonal (s : ℕ×SignedWords) : SignedMatrix :=
   (List.range s.1).map (fun i => diagonalRow (s.1,(i,s.2)))
 def matrixDiagonalRealizer : Realizer matrixDiagonal :=
   ((Realizer.fst.comp Realizer.range).pair Realizer.id).comp
     (mapEnvironment (approximationRowEnvironment.comp diagonalRowRealizer))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidRoundedShapeCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev ShapeRoundInput := (ℕ×ℕ)×SignedMatrix
 def roundingDiagonal (s : ShapeRoundInput) : SignedMatrix := matrixDiagonal (s.1.1,roundingAllowance s.1)
 def roundingDiagonalRealizer : Realizer roundingDiagonal :=
   ((Realizer.fst.comp Realizer.fst).pair (Realizer.fst.comp roundingAllowanceRealizer)).comp matrixDiagonalRealizer
 
 def roundedShapeWords (s : ShapeRoundInput) : SignedMatrix := matrixAdd (floorMatrix (s.2,s.1.2),roundingDiagonal s)
 def roundedShapeWordsRealizer : Realizer roundedShapeWords :=
   (((Realizer.snd.pair (Realizer.fst.comp Realizer.snd)).comp floorMatrixRealizer).pair roundingDiagonalRealizer).comp matrixAddRealizer

 abbrev FullShapeInput := ((ℕ×ℕ)×ℕ)×(SignedMatrix×SignedVector)
 def shapeCutDataRealizer : Realizer (fun s : FullShapeInput => (s.1.1.1,s.2)) :=
   ((Realizer.fst.comp Realizer.fst).comp Realizer.fst).pair Realizer.snd
 
 def shapeRoundData (s : FullShapeInput) : ShapeRoundInput := (s.1.1,cutShapeWords (s.1.1.1,s.2))
 def shapeRoundDataRealizer : Realizer shapeRoundData :=
   (Realizer.fst.comp Realizer.fst).pair (shapeCutDataRealizer.comp cutShapeWordsRealizer)
 
 def roundedStepShapeWords (s : FullShapeInput) : SignedMatrix :=
   matrixScale (roundedShapeWords (shapeRoundData s),enlargementCoefficient s.1.2)
 def roundedStepShapeWordsRealizer : Realizer roundedStepShapeWords :=
   ((shapeRoundDataRealizer.comp roundedShapeWordsRealizer).pair
     ((Realizer.fst.comp Realizer.snd).comp enlargementCoefficientRealizer)).comp matrixScaleRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidCenter
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidCenter.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Computable center updates and their error in the new ellipsoid's metric. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open EdgeSublinearMWIS.Main.GLS.Cast

end EdgeSublinearMWIS.Main.GLS.EllipsoidCenter
end

-- Solutions.EllipsoidRoundedShapeSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SqrtUpperMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SignedSqrtUpper
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def signedSqrtUpper (s : SignedWords×ℕ) : SignedWords := sqrtUpperWords (s.1.2,s.2)
 def signedSqrtUpperRealizer : Realizer signedSqrtUpper :=
   ((Realizer.fst.comp Realizer.snd).pair Realizer.snd).comp sqrtUpperWordsRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCenterCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev CenterUpdateInput := (ℕ×ℕ)×(SignedMatrix×(SignedVector×SignedVector))
 def centerShapeData (s : CenterUpdateInput) : CutShapeInput := (s.1.1,(s.2.1,s.2.2.1))
 def centerShapeDataRealizer : Realizer centerShapeData :=
   (Realizer.fst.comp Realizer.fst).pair ((Realizer.snd.comp Realizer.fst).pair ((Realizer.snd.comp Realizer.snd).comp Realizer.fst))
 
 def centerRootData (s : CenterUpdateInput) : SignedWords×ℕ := (cutQuadratic (centerShapeData s),s.1.2)
 def centerRootDataRealizer : Realizer centerRootData :=
   (centerShapeDataRealizer.comp cutQuadraticRealizer).pair (Realizer.fst.comp Realizer.snd)
 
 def centerRoot : CenterUpdateInput → SignedWords := signedSqrtUpper ∘ centerRootData
 def centerRootRealizer : Realizer centerRoot := centerRootDataRealizer.comp signedSqrtUpperRealizer
 
 def centerScalar (s : CenterUpdateInput) : SignedWords := centerCutCoefficient (s.1.1,centerRoot s)
 def centerScalarRealizer : Realizer centerScalar :=
   ((Realizer.fst.comp Realizer.fst).pair centerRootRealizer).comp centerCutCoefficientRealizer
 
 def centerDisplacement (s : CenterUpdateInput) : SignedVector := vectorScale (cutDirection (centerShapeData s),centerScalar s)
 def centerDisplacementRealizer : Realizer centerDisplacement :=
   ((centerShapeDataRealizer.comp cutDirectionRealizer).pair centerScalarRealizer).comp vectorScaleRealizer
 
 def approximateCenterWords (s : CenterUpdateInput) : SignedVector := vectorSub (s.2.2.2,centerDisplacement s)
 def approximateCenterWordsRealizer : Realizer approximateCenterWords :=
   (((Realizer.snd.comp Realizer.snd).comp Realizer.snd).pair centerDisplacementRealizer).comp vectorSubRealizer
 
 def roundedCenterWords (s : CenterUpdateInput) : SignedVector := floorVector (approximateCenterWords s,s.1.2)
 def roundedCenterWordsRealizer : Realizer roundedCenterWords :=
   (approximateCenterWordsRealizer.pair (Realizer.fst.comp Realizer.snd)).comp floorVectorRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCenterSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidUpdateCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def accuracyExponent (n : ℕ) : ℕ := 2*n+4
 def accuracyExponentRealizer : Realizer accuracyExponent :=
   ((((Realizer.constant (2:ℕ)).pair Realizer.id).comp naturalProductRealizer).pair (Realizer.constant (4:ℕ))).comp Realizer.add
 
 def gridExponent (s : ℕ×ℕ) : ℕ := 2*s.2+3*s.1+9
 def gridDouble : Realizer (fun s : ℕ×ℕ => 2*s.2) := ((Realizer.constant (2:ℕ)).pair Realizer.snd).comp naturalProductRealizer
 def gridTriple : Realizer (fun s : ℕ×ℕ => 3*s.1) := ((Realizer.constant (3:ℕ)).pair Realizer.fst).comp naturalProductRealizer

 def gridExponentRealizer : Realizer gridExponent :=
   (((gridDouble.pair gridTriple).comp Realizer.add).pair (Realizer.constant (9:ℕ))).comp Realizer.add

 abbrev EllipsoidUpdateInput := (ℕ×ℕ)×(SignedMatrix×(SignedVector×SignedVector))
 def ellipsoidShapeData (s : EllipsoidUpdateInput) : FullShapeInput :=
   (((s.1.1,gridExponent s.1),accuracyExponent s.1.1),(s.2.1,s.2.2.1))
 def ellipsoidShapeDataRealizer : Realizer ellipsoidShapeData :=
   ((((Realizer.fst.comp Realizer.fst).pair (Realizer.fst.comp gridExponentRealizer)).pair
     ((Realizer.fst.comp Realizer.fst).comp accuracyExponentRealizer)).pair
       ((Realizer.snd.comp Realizer.fst).pair ((Realizer.snd.comp Realizer.snd).comp Realizer.fst)))
 
 def ellipsoidCenterData (s : EllipsoidUpdateInput) : CenterUpdateInput :=
   ((s.1.1,gridExponent s.1),s.2)
 def ellipsoidCenterDataRealizer : Realizer ellipsoidCenterData :=
   (((Realizer.fst.comp Realizer.fst).pair (Realizer.fst.comp gridExponentRealizer)).pair Realizer.snd)
 
 def ellipsoidUpdate (s : EllipsoidUpdateInput) : SignedMatrix×SignedVector :=
   (roundedStepShapeWords (ellipsoidShapeData s),roundedCenterWords (ellipsoidCenterData s))
 def ellipsoidUpdateRealizer : Realizer ellipsoidUpdate :=
   (ellipsoidShapeDataRealizer.comp roundedStepShapeWordsRealizer).pair
     (ellipsoidCenterDataRealizer.comp roundedCenterWordsRealizer)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidPrecision
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidPrecision.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! A uniform dyadic grid for both parts of the rational center update. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open EdgeSublinearMWIS.Main.GLS.Cast

end EdgeSublinearMWIS.Main.GLS.EllipsoidPrecision
end

-- Solutions.GLSEllipsoidDeterminant
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidDeterminant.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Determinant bounds from quadratic-form comparison, used for rounded updates. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidDeterminant

open Matrix EllipsoidRounding

end EdgeSublinearMWIS.Main.GLS.EllipsoidDeterminant
end

-- Solutions.GLSEllipsoidIteration
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidIteration.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-! Conditioning and determinant shrinkage of the same rational stored update. -/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant EdgeSublinearMWIS.Main.GLS.Cast

end EdgeSublinearMWIS.Main.GLS.EllipsoidIteration
end

-- Solutions.GLSEllipsoidSequence
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidSequence.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

/-!
A concrete sequence of rational stored ellipsoids. The cut normals are supplied
externally; no LP separation, stopping rule, certificate recovery, or RAM execution
is asserted here.
-/

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open EdgeSublinearMWIS.Main.GLS.Cast

end EdgeSublinearMWIS.Main.GLS.EllipsoidSequence
end

-- Solutions.EllipsoidUpdateSemantics
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidCanonicalUpdate
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def normalizeEllipsoidState (s : SignedMatrix×SignedVector) : SignedMatrix×SignedVector :=
   (normalizeMatrix s.1,normalizeVector s.2)
 def normalizeEllipsoidStateRealizer : Realizer normalizeEllipsoidState :=
   (Realizer.fst.comp normalizeMatrixRealizer).pair (Realizer.snd.comp normalizeVectorRealizer)
 
 def canonicalEllipsoidUpdate : EllipsoidUpdateInput → SignedMatrix×SignedVector := normalizeEllipsoidState ∘ ellipsoidUpdate
 def canonicalEllipsoidUpdateRealizer : Realizer canonicalEllipsoidUpdate := ellipsoidUpdateRealizer.comp normalizeEllipsoidStateRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidPhaseCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev EllipsoidPhaseState := (ℕ×ℕ)×(SignedMatrix×SignedVector)
 abbrev EllipsoidPhaseStepInput := SignedVector×EllipsoidPhaseState
 def phaseStepData (s : EllipsoidPhaseStepInput) : EllipsoidUpdateInput :=
   (s.2.1,(s.2.2.1,(s.1,s.2.2.2)))
 def phaseStepDataRealizer : Realizer phaseStepData :=
   (Realizer.snd.comp Realizer.fst).pair
     (((Realizer.snd.comp Realizer.snd).comp Realizer.fst).pair
       (Realizer.fst.pair ((Realizer.snd.comp Realizer.snd).comp Realizer.snd)))
 
 def phaseStepCounter (s : EllipsoidPhaseStepInput) : ℕ×ℕ := (s.2.1.1,s.2.1.2+1)
 def phaseStepCounterRealizer : Realizer phaseStepCounter :=
   ((Realizer.snd.comp Realizer.fst).comp Realizer.fst).pair
     (((Realizer.snd.comp Realizer.fst).comp Realizer.snd).comp Realizer.succ)
 
 def ellipsoidPhaseStep (s : EllipsoidPhaseStepInput) : EllipsoidPhaseState :=
   (phaseStepCounter s,canonicalEllipsoidUpdate (phaseStepData s))
 def ellipsoidPhaseStepRealizer : Realizer ellipsoidPhaseStep :=
   phaseStepCounterRealizer.pair (phaseStepDataRealizer.comp canonicalEllipsoidUpdateRealizer)
 
 def phaseInitialRaw (n : ℕ) : SignedMatrix×SignedVector :=
   (matrixDiagonal (n,scalarOne),List.replicate n signedZero)
 def phaseInitialRawRealizer : Realizer phaseInitialRaw :=
   ((Realizer.id.pair (Realizer.constant scalarOne)).comp matrixDiagonalRealizer).pair
     ((Realizer.id.pair (Realizer.constant signedZero)).comp replicateList)
 
 def phaseInitial (n : ℕ) : EllipsoidPhaseState := ((n,0),normalizeEllipsoidState (phaseInitialRaw n))
 def phaseInitialRealizer : Realizer phaseInitial :=
   (Realizer.id.pair (Realizer.constant (0:ℕ))).pair (phaseInitialRawRealizer.comp normalizeEllipsoidStateRealizer)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidBudgetCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds
open ConvexTools GLS.EllipsoidSequence

 def thinExponentRealizer : Realizer thinExponent :=
   ((((Realizer.constant (10:ℕ)).pair ((Realizer.succ.comp Realizer.succ).comp naturalSquare)).comp naturalProductRealizer)).congr
     (fun _ => by simp only [Function.comp_apply,thinExponent,pow_two])
 
 def phaseThresholdExponent (n : ℕ) : ℕ := thinExponent n+n+1
 def phaseThresholdExponentRealizer : Realizer phaseThresholdExponent :=
   ((thinExponentRealizer.pair Realizer.id).comp Realizer.add).comp Realizer.succ
 
 def phaseBudget (n : ℕ) : ℕ := thresholdSteps n (phaseThresholdExponent n)
 def phaseBudgetInner (n : ℕ) : ℕ := phaseThresholdExponent n*n+1
 def phaseBudgetInnerRealizer : Realizer phaseBudgetInner :=
   ((phaseThresholdExponentRealizer.pair Realizer.id).comp naturalProductRealizer).comp Realizer.succ
 
 def phaseBudgetFactorRealizer : Realizer (fun n : ℕ => 4*(n+1)) :=
   ((Realizer.constant (4:ℕ)).pair Realizer.succ).comp naturalProductRealizer
 
 def phaseBudgetRealizer : Realizer phaseBudget := (phaseBudgetFactorRealizer.pair phaseBudgetInnerRealizer).comp naturalProductRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PostprocessCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PreprocessGuard
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.NonzeroCoordinateCode
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def wordNonzero (s : SignedWords) : Bool := !(trim s.2.1).isEmpty
 def wordNonzeroRealizer : Realizer wordNonzero :=
   (((Realizer.snd.comp Realizer.fst).comp trimRealizer).comp nonemptyBits)

 def nonzeroCoordinate (s : ℕ×SignedVector) : Bool := wordNonzero ((s.2.drop s.1).headD signedZero)
 def nonzeroCoordinateRealizer : Realizer nonzeroCoordinate :=
   ((Realizer.snd.pair Realizer.fst).comp (lookupList signedZero)).comp wordNonzeroRealizer
 
 def nonzeroIndices (ps : SignedVector) : List ℕ :=
   (List.range ps.length).filter (fun i => nonzeroCoordinate (i,ps))
 def nonzeroIndicesRealizer : Realizer nonzeroIndices :=
   ((listLength.comp Realizer.range).pair Realizer.id).comp (filterEnvironment nonzeroCoordinateRealizer)
 
 def findNonzero (ps : SignedVector) : Bool×ℕ := (!(nonzeroIndices ps).isEmpty,(nonzeroIndices ps).headD 0)
 def findNonzeroRealizer : Realizer findNonzero := nonzeroIndicesRealizer.comp (nonemptyNatList.pair headNat)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ListEraseCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α : Type} [Coding α]

 def eraseIndex (s : List α×ℕ) : List α := s.1.take s.2++s.1.drop (s.2+1)
 def eraseIndexRealizer : Realizer (eraseIndex (α:=α)) :=
   (((Realizer.snd.pair Realizer.fst).comp takeList).pair
     ((Realizer.fst.pair (Realizer.snd.comp Realizer.succ)).comp dropList)).comp appendList

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.AffineEliminationCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev EliminationParameters := ℕ×(SignedVector×SignedWords)
 abbrev EliminationRowInput := (SignedVector×SignedWords)×EliminationParameters
 def eliminationRowPivot (s : EliminationRowInput) : SignedWords := (s.1.1.drop s.2.1).headD signedZero
 def eliminationRowPivotRealizer : Realizer eliminationRowPivot :=
   ((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp (lookupList signedZero)
 
 def eliminationNormalPivot (s : EliminationRowInput) : SignedWords := (s.2.2.1.drop s.2.1).headD signedZero
 def eliminationNormalPivotRealizer : Realizer eliminationNormalPivot :=
   (((Realizer.snd.comp Realizer.snd).comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp (lookupList signedZero)
 
 def eliminationRatio (s : EliminationRowInput) : SignedWords := canonicalDiv (eliminationRowPivot s,eliminationNormalPivot s)
 def eliminationRatioRealizer : Realizer eliminationRatio := (eliminationRowPivotRealizer.pair eliminationNormalPivotRealizer).comp canonicalDivRealizer
 
 def eliminationRowRest (s : EliminationRowInput) : SignedVector := eraseIndex (s.1.1,s.2.1)
 def eliminationRowRestRealizer : Realizer eliminationRowRest :=
   ((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp eraseIndexRealizer
 
 def eliminationNormalRest (s : EliminationRowInput) : SignedVector := eraseIndex (s.2.2.1,s.2.1)
 def eliminationNormalRestRealizer : Realizer eliminationNormalRest :=
   (((Realizer.snd.comp Realizer.snd).comp Realizer.fst).pair (Realizer.snd.comp Realizer.fst)).comp eraseIndexRealizer
 
 def eliminationRowCoefficients (s : EliminationRowInput) : SignedVector :=
   vectorSub (eliminationRowRest s,vectorScale (eliminationNormalRest s,eliminationRatio s))
 def eliminationRowCoefficientsRealizer : Realizer eliminationRowCoefficients :=
   (eliminationRowRestRealizer.pair ((eliminationNormalRestRealizer.pair eliminationRatioRealizer).comp vectorScaleRealizer)).comp vectorSubRealizer
 
 def eliminationRowOffset (s : EliminationRowInput) : SignedWords :=
   canonicalAdd (s.1.2,canonicalMul (eliminationRatio s,s.2.2.2))
 def eliminationRowOffsetRealizer : Realizer eliminationRowOffset :=
   ((Realizer.fst.comp Realizer.snd).pair
     ((eliminationRatioRealizer.pair ((Realizer.snd.comp Realizer.snd).comp Realizer.snd)).comp canonicalMulRealizer)).comp canonicalAddRealizer
 
 def eliminationRow (s : EliminationRowInput) : SignedVector×SignedWords := (eliminationRowCoefficients s,eliminationRowOffset s)
 def eliminationRowRealizer : Realizer eliminationRow := eliminationRowCoefficientsRealizer.pair eliminationRowOffsetRealizer
 
 abbrev AffineWordState := SignedMatrix×SignedVector
 def eliminationRows (s : AffineWordState×EliminationParameters) : List (SignedVector×SignedWords) :=
   (arrayPairs ([]:SignedVector) signedZero s.1).map (fun row => eliminationRow (row,s.2))
 def eliminationRowsRealizer : Realizer eliminationRows :=
   ((Realizer.fst.comp (arrayPairsRealizer ([]:SignedVector) signedZero)).pair Realizer.snd).comp (mapEnvironment eliminationRowRealizer)
 
 def affineEliminate : AffineWordState×EliminationParameters → AffineWordState :=
   (fun xs => (xs.map Prod.fst,xs.map Prod.snd)) ∘ eliminationRows
 def affineEliminateRealizer : Realizer affineEliminate := eliminationRowsRealizer.comp ((mapList Realizer.fst).pair (mapList Realizer.snd))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RectangularMatrixSemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open RealizerBounds

 def RepresentsRectMatrix {m n : ℕ} (bs : SignedMatrix) (A : Matrix (Fin m) (Fin n) ℚ) : Prop :=
   ∃ rows : Fin m → SignedVector,bs=List.ofFn rows ∧ ∀ i,RepresentsVector (rows i) (rationalVector (A i))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AffineEliminationSemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open RealizerBounds

 def eliminatedRow {n : ℕ} (a p : Fin (n+1) → ℚ) (j : Fin (n+1)) : Fin n → ℚ :=
   fun i => a (j.succAbove i)-(a j/p j)*p (j.succAbove i)
 def eliminatedOffset {n : ℕ} (a p : Fin (n+1) → ℚ) (b d : ℚ) (j : Fin (n+1)) : ℚ := b+(a j/p j)*d

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.CanonicalAffineElimination
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def canonicalAffineEliminate : AffineWordState×EliminationParameters → AffineWordState := normalizeEllipsoidState ∘ affineEliminate
 def canonicalAffineEliminateRealizer : Realizer canonicalAffineEliminate := affineEliminateRealizer.comp normalizeEllipsoidStateRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleRecoveryParameters
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def phaseRecoveryInput (st : EllipsoidPhaseState) : EllipsoidRecoveryInput := (st.1.1,st.2)
 def phaseRecoveryInputRealizer : Realizer phaseRecoveryInput := (Realizer.fst.comp Realizer.fst).pair Realizer.snd
 
 def phaseRecoveredCoefficients : EllipsoidPhaseState → SignedVector := Prod.fst ∘ ellipsoidRecovery ∘ phaseRecoveryInput
 def phaseRecoveredCoefficientsRealizer : Realizer phaseRecoveredCoefficients := (phaseRecoveryInputRealizer.comp ellipsoidRecoveryRealizer).comp Realizer.fst
 def phaseSplitCoefficients (s : ℕ×SignedVector) : SignedVector×SignedWords := (s.2.take s.1,(s.2.drop s.1).headD signedZero)
 def phaseSplitCoefficientsRealizer : Realizer phaseSplitCoefficients := takeList.pair
   ((Realizer.snd.pair Realizer.fst).comp (lookupList signedZero))
 
 def phaseNormalAndOffset (st : EllipsoidPhaseState) : SignedVector×SignedWords := phaseSplitCoefficients (st.1.1,phaseRecoveredCoefficients st)
 def phaseNormalAndOffsetRealizer : Realizer phaseNormalAndOffset :=
   ((Realizer.fst.comp Realizer.fst).pair phaseRecoveredCoefficientsRealizer).comp phaseSplitCoefficientsRealizer
 def eliminationParameters (s : SignedVector×SignedWords) : EliminationParameters := ((findNonzero s.1).2,s)
 def eliminationParametersRealizer : Realizer eliminationParameters :=
   ((Realizer.fst.comp findNonzeroRealizer).comp Realizer.snd).pair Realizer.id
 
 def phaseEliminationParameters : EllipsoidPhaseState → EliminationParameters := eliminationParameters ∘ phaseNormalAndOffset
 def phaseEliminationParametersRealizer : Realizer phaseEliminationParameters := phaseNormalAndOffsetRealizer.comp eliminationParametersRealizer
 abbrev OracleCoreState := AffineWordState×EllipsoidPhaseState
 def oracleDimensionReduction (st : OracleCoreState) : OracleCoreState :=
   (canonicalAffineEliminate (st.1,phaseEliminationParameters st.2),phaseInitial (st.2.1.1-1))
 def oracleDimensionReductionRealizer : Realizer oracleDimensionReduction :=
   ((Realizer.fst.pair (Realizer.snd.comp phaseEliminationParametersRealizer)).comp canonicalAffineEliminateRealizer).pair
     ((((Realizer.snd.comp Realizer.fst).comp Realizer.fst).comp Realizer.pred).comp phaseInitialRealizer)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AffineEvaluationCode
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev AffineEvaluationInput := (SignedMatrix×SignedVector)×SignedVector
 def affineEvaluation (s : AffineEvaluationInput) : SignedVector := vectorAdd (matrixVector (s.1.1,s.2),s.1.2)
 def affineEvaluationRealizer : Realizer affineEvaluation :=
   ((((Realizer.fst.comp Realizer.fst).pair Realizer.snd).comp matrixVectorRealizer).pair (Realizer.fst.comp Realizer.snd)).comp vectorAddRealizer

 abbrev AffinePullbackInput := ℕ×(SignedVector×SignedMatrix)
 def affinePullbackCoordinate (s : ℕ×(SignedVector×SignedMatrix)) : SignedWords := signedDot (s.2.1,matrixColumn (s.2.2,s.1))
 def affinePullbackCoordinateRealizer : Realizer affinePullbackCoordinate :=
   ((Realizer.snd.comp Realizer.fst).pair (((Realizer.snd.comp Realizer.snd).pair Realizer.fst).comp matrixColumnRealizer)).comp signedDotRealizer
 
 def affinePullback (s : AffinePullbackInput) : SignedVector :=
   (List.range s.1).map (fun i => affinePullbackCoordinate (i,s.2))
 def affinePullbackRealizer : Realizer affinePullback :=
   ((Realizer.fst.comp Realizer.range).pair Realizer.snd).comp (mapEnvironment affinePullbackCoordinateRealizer)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RationalVectorClearing
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def clearingModulus : SignedVector → List Bool :=
   Prod.fst ∘ approximationModuli ∘ (fun xs => (0,xs))
 def clearingModulusRealizer : Realizer clearingModulus :=
   (((Realizer.constant (0:ℕ)).pair Realizer.id).comp approximationModuliRealizer).comp Realizer.fst
 
 def clearCanonicalVector (xs : SignedVector) : SignedVector := vectorScale (xs,unsignedIntegerWord (clearingModulus xs))
 def clearCanonicalVectorRealizer : Realizer clearCanonicalVector :=
   (Realizer.id.pair (clearingModulusRealizer.comp unsignedIntegerRealizer)).comp vectorScaleRealizer
 
 def clearRationalVector : SignedVector → SignedVector := clearCanonicalVector ∘ normalizeVector
 def clearRationalVectorRealizer : Realizer clearRationalVector := normalizeVectorRealizer.comp clearCanonicalVectorRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.SelectiveChoose
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.ThreeMachine.StackCompiler
namespace Routine
open Tree
variable {f g : Data → Data} {c d : Data → ℕ}
def selectiveChoose (R : Routine f c) (S : Routine g d) :
    Routine (fun x => if x.head.nonempty then f x else g x)
      (fun x => (if x.head.nonempty then c x else d x)+30*(x.size+(if x.head.nonempty then f x else g x).size+1)) where
  Vars := (Fin 3 ⊕ R.Vars) ⊕ S.Vars
  finiteVars := inferInstance
  decVars := inferInstance
  input := .inl (.inl 0)
  output := .inl (.inl 1)
  distinct := by simp
  code := chooseCode R S
  correct x := by
    let z := zeroStore R.Vars
    let w := zeroStore S.Vars
    let s := foldStore x .nil .nil
    let s' := foldStore x .nil x.head
    let y := if x.head.nonempty then f x else g x
    let t := foldStore x y x.head
    have es : start (0 : Fin 3) x = s := by
      funext i; fin_cases i <;> simp [s,start,zeroStore,foldStore]
    have ef : finish (Sum.inl (Sum.inl (0 : Fin 3))) (Sum.inl (Sum.inl (1 : Fin 3))) x y =
        join (join (foldStore x y .nil) z) w := by
      rw [finish,start_left,start_left,es,join_update_left,join_update_left]
      simp only [s,foldStore_update_one]
      rfl
    have h₁ : Bounded (.select true (.inl (.inl 2)) (.inl (.inl 0)))
        (join (join s z) w) (join (join s' z) w) (2+x.size) := by
      simpa [join_update_left,s,s',foldStore_update_two] using
        (Eval.select true (.inl (.inl 2)) (.inl (.inl 0)) (join (join s z) w)).bounded
    have h₂ : Bounded (.branch (.inl (.inl 2)) ((R.invoke (1 : Fin 3) 0).rename Sum.inl)
        (S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)))
        (join (join s' z) w) (join (join t z) w)
        ((if x.head.nonempty then c x else d x)+10*(x.size+(if x.head.nonempty then f x else g x).size+2)+1) := by
      cases he : x.head.nonempty with
      | false =>
        have hh := (S.invoke_correct (Sum.inl (1 : Fin 3)) (Sum.inl 0) (join s' z)).branch_false
          (src := Sum.inl (Sum.inl (2 : Fin 3))) (p := ((R.invoke (1 : Fin 3) 0).rename Sum.inl)) (by simpa [s'] using he)
        simpa only [join_update_left,s',foldStore_update_one,t,y,he,Bool.false_eq_true,ite_false,join_inl,foldStore_zero] using
          (hh.mono (m := (if x.head.nonempty then c x else d x)+10*(x.size+(if x.head.nonempty then f x else g x).size+2)+1)
            (by simp only [he,Bool.false_eq_true,ite_false,join_inl,foldStore_zero,foldStore_one,s',Data.size_nil]; omega))
      | true =>
        have hh := ((R.invoke_correct (1 : Fin 3) 0 s').left w).branch_true
          (src := Sum.inl (Sum.inl (2 : Fin 3))) (q := S.invoke (Sum.inl (1 : Fin 3)) (Sum.inl 0)) (by simpa [s'] using he)
        simpa only [s',foldStore_update_one,t,y,he,ite_true,foldStore_zero] using
          (hh.mono (m := (if x.head.nonempty then c x else d x)+10*(x.size+(if x.head.nonempty then f x else g x).size+2)+1)
            (by simp only [he,ite_true,foldStore_zero,foldStore_one,s',Data.size_nil]; omega))
    have h₃ : Bounded (.nil (.inl (.inl 2))) (join (join t z) w)
        (join (join (foldStore x y .nil) z) w) (1+x.head.size) := by
      simpa only [join_update_left,t,foldStore_update_two,join_inl,foldStore_two] using
        (Eval.nil (.inl (.inl 2)) (join (join t z) w)).bounded
    rw [start_left,start_left,es,ef]
    have hh := h₁.seq (h₂.seq h₃)
    exact hh.mono (by
      have hx : x.head.size ≤ x.size := by cases x <;> simp [Data.head]; omega
      omega)

end Routine
end OAI.ThreeMachine.StackCompiler

namespace OAI.ThreeMachine.StackCompiler.Realizer
variable {α β : Type} [Coding α] [Coding β]
 def selectiveChoose {f g : α → β} (R : Realizer f) (S : Realizer g) :
     Realizer (fun x : Bool×α => if x.1 then f x.2 else g x.2) where
   transform := fun x => if x.head.nonempty then (snd.comp R).transform x else (snd.comp S).transform x
   charge := _
   routine := (snd.comp R).routine.selectiveChoose (snd.comp S).routine
   correct x := by
     rcases x with ⟨b,x⟩
     cases b <;> simp only [enc_pair,enc_false,enc_true,Data.head,Data.nonempty,
       Bool.false_eq_true,ite_false,ite_true]
     · exact (snd.comp S).correct (Bool.false,x)
     · exact (snd.comp R).correct (Bool.true,x)
 
end OAI.ThreeMachine.StackCompiler.Realizer
end

-- Solutions.OracleControlCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 abbrev OracleState := Bool×OracleCoreState
 abbrev OraclePreparedCut := SignedVector×OracleCoreState
 abbrev OracleCutInput := SignedVector×OracleState
 def oracleCoreQuery (st : OracleCoreState) : SignedVector :=
   affineEvaluation (st.1,vectorScale (st.2.2.2,naturalSignedWord (st.2.1.1+1)))
 def oracleQueryScaleRealizer : Realizer (fun st : OracleCoreState => naturalSignedWord (st.2.1.1+1)) :=
   ((((Realizer.snd.comp Realizer.fst).comp Realizer.fst).comp Realizer.succ).comp naturalSignedWordRealizer)
 
 def oracleCoreQueryRealizer : Realizer oracleCoreQuery :=
   (Realizer.fst.pair ((((Realizer.snd.comp Realizer.snd).comp Realizer.snd).pair oracleQueryScaleRealizer).comp vectorScaleRealizer)).comp affineEvaluationRealizer
 
 def oracleInitial (n : ℕ) : OracleState := (false,((phaseInitial n).2,phaseInitial n))
 def oracleInitialRealizer : Realizer oracleInitial := (Realizer.constant Bool.false).pair
   ((phaseInitialRealizer.comp Realizer.snd).pair phaseInitialRealizer)
 
 def oracleAtBoundary (st : OracleCoreState) : Bool := decide (phaseBudget st.2.1.1 ≤ st.2.1.2)
 def oracleAtBoundaryRealizer : Realizer oracleAtBoundary :=
   (((((Realizer.snd.comp Realizer.fst).comp Realizer.fst).comp phaseBudgetRealizer).pair
     ((Realizer.snd.comp Realizer.fst).comp Realizer.snd)).comp Realizer.le)
 
 def oracleBoundary (st : OracleCoreState) : OracleCoreState :=
   if oracleAtBoundary st then oracleDimensionReduction st else st
 def oracleBoundaryRealizer : Realizer oracleBoundary :=
   (oracleAtBoundaryRealizer.pair Realizer.id).comp (oracleDimensionReductionRealizer.selectiveChoose Realizer.id)
 def oraclePhaseAdvance (s : OraclePreparedCut) : OracleCoreState := (s.2.1,ellipsoidPhaseStep (s.1,s.2.2))
 def oraclePhaseAdvanceRealizer : Realizer oraclePhaseAdvance :=
   (Realizer.snd.comp Realizer.fst).pair ((Realizer.fst.pair (Realizer.snd.comp Realizer.snd)).comp ellipsoidPhaseStepRealizer)
 
 def oracleBigCut : OraclePreparedCut → OracleState := (fun core => (false,oracleBoundary core)) ∘ oraclePhaseAdvance
 def oracleBigCutRealizer : Realizer oracleBigCut := oraclePhaseAdvanceRealizer.comp ((Realizer.constant Bool.false).pair oracleBoundaryRealizer)
 def scalarHalf : SignedWords := (false,([true],[false,true]))
 def oracleSmallAdvance (s : OraclePreparedCut) : OracleState :=
   (false,(s.2.1,((s.2.2.1.1,1),(s.2.2.2.1,List.replicate s.2.2.1.1 scalarHalf))))
 def oracleSmallDimension : Realizer (fun s : OraclePreparedCut => s.2.2.1.1) :=
   ((Realizer.snd.comp Realizer.snd).comp Realizer.fst).comp Realizer.fst
 
 def oracleSmallAdvanceRealizer : Realizer oracleSmallAdvance :=
   (Realizer.constant Bool.false).pair ((Realizer.snd.comp Realizer.fst).pair
     ((oracleSmallDimension.pair (Realizer.constant (1:ℕ))).pair
       ((((Realizer.snd.comp Realizer.snd).comp Realizer.snd).comp Realizer.fst).pair
         ((oracleSmallDimension.pair (Realizer.constant scalarHalf)).comp replicateList))))
 def oracleReject (s : OraclePreparedCut) : OracleState := (true,s.2)
 def oracleRejectRealizer : Realizer oracleReject := (Realizer.constant Bool.true).pair Realizer.snd
 def oracleSmallFirst (s : OraclePreparedCut) : Bool := decide (s.2.2.1.2=0)
 def oracleSmallFirstRealizer : Realizer oracleSmallFirst :=
   (((((Realizer.snd.comp Realizer.snd).comp Realizer.fst).comp Realizer.snd).pair (Realizer.constant (0:ℕ))).comp Realizer.eqNat)
 def oracleSmallCut (s : OraclePreparedCut) : OracleState := if oracleSmallFirst s then oracleSmallAdvance s else oracleReject s
 def oracleSmallCutRealizer : Realizer oracleSmallCut :=
   (oracleSmallFirstRealizer.pair Realizer.id).comp (oracleSmallAdvanceRealizer.selectiveChoose oracleRejectRealizer)
 def oracleSmall (s : OraclePreparedCut) : Bool := decide (s.2.2.1.1 ≤ 1)
 def oracleSmallRealizer : Realizer oracleSmall := (oracleSmallDimension.pair (Realizer.constant (1:ℕ))).comp Realizer.le
 def oracleNonzeroCut (s : OraclePreparedCut) : OracleState := if oracleSmall s then oracleSmallCut s else oracleBigCut s
 def oracleNonzeroCutRealizer : Realizer oracleNonzeroCut :=
   (oracleSmallRealizer.pair Realizer.id).comp (oracleSmallCutRealizer.selectiveChoose oracleBigCutRealizer)
 def oraclePreparedNonzero (s : OraclePreparedCut) : Bool := (findNonzero s.1).1
 def oraclePreparedNonzeroRealizer : Realizer oraclePreparedNonzero := (Realizer.fst.comp findNonzeroRealizer).comp Realizer.fst
 def oraclePreparedCut (s : OraclePreparedCut) : OracleState := if oraclePreparedNonzero s then oracleNonzeroCut s else oracleReject s
 def oraclePreparedCutRealizer : Realizer oraclePreparedCut :=
   (oraclePreparedNonzeroRealizer.pair Realizer.id).comp (oracleNonzeroCutRealizer.selectiveChoose oracleRejectRealizer)
 def oraclePullbackData (s : OraclePreparedCut) : AffinePullbackInput := (s.2.2.1.1,(s.1,s.2.1.1))
 def oraclePullbackDataRealizer : Realizer oraclePullbackData := oracleSmallDimension.pair
   (Realizer.fst.pair ((Realizer.snd.comp Realizer.fst).comp Realizer.fst))
 
 def oraclePrepareCut (s : OraclePreparedCut) : OraclePreparedCut :=
   (clearRationalVector (affinePullback (oraclePullbackData s)),s.2)
 def oraclePrepareCutRealizer : Realizer oraclePrepareCut :=
   ((oraclePullbackDataRealizer.comp affinePullbackRealizer).comp clearRationalVectorRealizer).pair Realizer.snd
 
 def oracleActiveCut (s : OracleCutInput) : OracleState := oraclePreparedCut (oraclePrepareCut (s.1,s.2.2))
 def oracleActiveCutRealizer : Realizer oracleActiveCut :=
   (((Realizer.fst.pair (Realizer.snd.comp Realizer.snd)).comp oraclePrepareCutRealizer).comp oraclePreparedCutRealizer)
 def oracleCut (s : OracleCutInput) : OracleState := if s.2.1 then s.2 else oracleActiveCut s
 def oracleCutRealizer : Realizer oracleCut :=
   ((Realizer.snd.comp Realizer.fst).pair Realizer.id).comp (Realizer.snd.selectiveChoose oracleActiveCutRealizer)
 def oracleExecute (s : ℕ×SignedMatrix) : OracleState :=
   s.2.foldl (fun st cut => oracleCut (cut,st)) (oracleInitial s.1)
 def oracleExecuteRealizer : Realizer oracleExecute :=
   (Realizer.snd.pair (Realizer.fst.comp oracleInitialRealizer)).comp oracleCutRealizer.fold

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RectangularRowsParser
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readRectangularRows (s : (ℕ×ℕ)×List Bool) : SignedMatrix×List Bool :=
   let t := readMatrixStep^[s.1.2] (s.1.1,(s.2,[]))
   (t.2.2.reverse,t.2.1)
 def readRectangularRowsRealizer : Realizer readRectangularRows :=
   (((Realizer.fst.comp Realizer.snd).pair
     ((Realizer.fst.comp Realizer.fst).pair (Realizer.snd.pair (Realizer.constant ([]:SignedMatrix))))).comp readMatrixStepRealizer.iterate).comp
       (((Realizer.snd.comp Realizer.snd).comp Realizer.reverse).pair (Realizer.snd.comp Realizer.fst))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PostprocessSemantics
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ExpandedBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def Expanded {f : α → β} (R : Realizer f) (N : α → ℕ) : Prop :=
   ∃ C q : ℕ,0< C ∧ ∀x,R.time x≤ C*(volume x+N x+1)^q ∧ volume (f x)≤ C*(volume x+N x+1)^q

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ExpandedPair
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
 
end EdgeSublinearMWIS.Main.RealizerBounds

namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
 
end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.ReadUnboundedNatural
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def readUnboundedNatural (L : List Bool) : ℕ×List Bool := (value (readWord L).1,(readWord L).2)
 def readUnboundedNaturalRealizer : Realizer readUnboundedNatural :=
   readWordRealizer.comp ((Realizer.fst.comp valueRealizer).pair Realizer.snd)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleTranscriptParserCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def skipOracleBound (s : ℕ×List Bool) : ℕ×List Bool := (s.1,(readWord s.2).2)
 def skipOracleBoundRealizer : Realizer skipOracleBound := Realizer.fst.pair ((Realizer.snd.comp readWordRealizer).comp Realizer.snd)
 
 def oracleCountHeader (s : ℕ×List Bool) : ℕ×(ℕ×List Bool) := (s.1,readUnboundedNatural s.2)
 def oracleCountHeaderRealizer : Realizer oracleCountHeader := Realizer.fst.pair (Realizer.snd.comp readUnboundedNaturalRealizer)
 def oracleHeader : List Bool → ℕ×(ℕ×List Bool) := oracleCountHeader ∘ skipOracleBound ∘ readUnboundedNatural
 def oracleHeaderRealizer : Realizer oracleHeader := (readUnboundedNaturalRealizer.comp skipOracleBoundRealizer).comp oracleCountHeaderRealizer
 
 def oracleRowsInput (s : ℕ×(ℕ×List Bool)) : (ℕ×ℕ)×List Bool := ((s.1+1,s.2.1),s.2.2)
 def oracleRowsInputRealizer : Realizer oracleRowsInput :=
   ((Realizer.fst.comp Realizer.succ).pair (Realizer.snd.comp Realizer.fst)).pair (Realizer.snd.comp Realizer.snd)
 
 def oracleNormals (s : ℕ×(ℕ×List Bool)) : SignedMatrix :=
   (readRectangularRows (oracleRowsInput s)).1.map (fun row => row.take s.1)
 def oracleNormalsRealizer : Realizer oracleNormals :=
   ((((oracleRowsInputRealizer.comp readRectangularRowsRealizer).comp Realizer.fst).pair Realizer.fst).comp
     (mapEnvironment ((Realizer.snd.pair Realizer.fst).comp takeList)))
 
 def parseOracleTranscript : List Bool → ℕ×SignedMatrix := (fun s => (s.1,oracleNormals s)) ∘ oracleHeader
 def parseOracleTranscriptRealizer : Realizer parseOracleTranscript := oracleHeaderRealizer.comp (Realizer.fst.pair oracleNormalsRealizer)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleOutputCode
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def oracleQueryOutput (st : OracleState) : List Bool := true::serializeRow (oracleCoreQuery st.2)
 def oracleQueryOutputRealizer : Realizer oracleQueryOutput :=
   ((Realizer.constant Bool.true).pair ((Realizer.snd.comp oracleCoreQueryRealizer).comp serializeRowRealizer)).comp Realizer.cons
 
 def oracleOutput (st : OracleState) : List Bool := if st.1 then [false] else oracleQueryOutput st
 def oracleOutputRealizer : Realizer oracleOutput :=
   (Realizer.fst.pair Realizer.id).comp ((Realizer.constant [Bool.false]).selectiveChoose oracleQueryOutputRealizer)
 def binaryOracle : List Bool → List Bool := oracleOutput ∘ oracleExecute ∘ parseOracleTranscript
 def binaryOracleRealizer : Realizer binaryOracle := (parseOracleTranscriptRealizer.comp oracleExecuteRealizer).comp oracleOutputRealizer

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleTranscriptParserMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def halfspaceCodeRow {n : ℕ} (c : RationalHalfspace n) : List RationalCode :=
   List.ofFn (fun i => rationalCode (c.normal i))++[rationalCode c.bound]

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidPhaseMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath GLS.EllipsoidSequence GLS.EllipsoidRounding GLS.Cast

 def ellipsoidPrefix (n : ℕ) (vs : ℕ → SignedVector) (k : ℕ) : EllipsoidPhaseState :=
   ((List.range k).map vs).foldl (fun st v => ellipsoidPhaseStep (v,st)) (phaseInitial n)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidPrefixCongruence
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCounterMath
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 def CounterGood (N : ℕ) (st : OracleCoreState) : Prop :=
   st.2.1.1 ≤ N ∧ st.2.1.2 < phaseBudget st.2.1.1 ∧ (st.2.1.1 ≤ 1 → st.2.1.2 ≤ 1)
 def counterPotential (N : ℕ) (st : OracleCoreState) : ℕ :=
   (st.2.1.1+1)*(phaseBudget N+3)-st.2.1.2

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryHullHyperplane
noncomputable section

open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.OraclePhaseInvariant
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

 def SmallPhaseGeometry {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState) : Prop :=
   st.1.1=n ∧ st.1.2 ≤ 1 ∧
     RepresentsMatrix st.2.1 (1:Matrix (Fin n) (Fin n) ℚ) ∧
     RepresentsVector st.2.2 (rationalVector (fun _ : Fin n => (st.1.2:ℚ)/2)) ∧
     (st.1.2=1 → ∀ v∈V,∀ i,v i=true) ∧
     (∀ row∈st.2.1,VectorCanonical row) ∧ VectorCanonical st.2.2
 inductive PhaseGeometry {n : ℕ} (V : Finset (Fin n → Bool)) (st : EllipsoidPhaseState) : Prop
   | small (hn : n ≤ 1) (hsmall : SmallPhaseGeometry V st) : PhaseGeometry V st
   | large (hn : 2 ≤ n) (vs : ℕ → SignedVector) (a : ℕ → Fin n → ℚ) (k : ℕ)
       (hv : ∀ j,RepresentsVector (vs j) (rationalVector (a j)))
       (ha : ∀ j,1 ≤ realVector (a j) ⬝ᵥ realVector (a j))
       (hst : st=ellipsoidPrefix n vs k) (hk : k ≤ phaseBudget n)
       (hcuts : ∀ j < k,∀ v∈V,realVector (a j) ⬝ᵥ
         ((fun i => (if v i then 1 else 0)/(n+1:ℝ))-realVector (centers n a 0 j)) ≤ 0) : PhaseGeometry V st

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleQuerySemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.AffineCoordinateElimination
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

 def coordinateProjection {n : ℕ} (j : Fin (n+1)) : (Fin (n+1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) where
   toFun x := fun i => x (j.succAbove i)
   map_add' _ _ := rfl
   map_smul' _ _ := rfl
 def coordinateInsertion {n : ℕ} (p : Fin (n+1) → ℝ) (d : ℝ) (j : Fin (n+1))
     (y : Fin n → ℝ) : Fin (n+1) → ℝ :=
   Fin.insertNth j ((d-∑ i,p (j.succAbove i)*y i)/p j) y

 def coordinateInsertionLinear {n : ℕ} (p : Fin (n+1) → ℝ) (j : Fin (n+1)) :
     (Fin n → ℝ) →ₗ[ℝ] (Fin (n+1) → ℝ) where
   toFun := coordinateInsertion p 0 j
   map_add' x y := by
     funext i
     rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i,rfl⟩
     · simp only [coordinateInsertion,Fin.insertNth_apply_same,Pi.add_apply,mul_add,Finset.sum_add_distrib,zero_sub]
       ring
     · simp only [coordinateInsertion,Fin.insertNth_apply_succAbove,Pi.add_apply]
   map_smul' a x := by
     funext i
     rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i,rfl⟩
     · simp only [coordinateInsertion,Fin.insertNth_apply_same,Pi.smul_apply,smul_eq_mul,zero_sub,RingHom.id_apply]
       have he : (∑ t,p (i.succAbove t)*(a*x t))=a*∑ t,p (i.succAbove t)*x t := by
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro t ht
         ring
       rw [he]
       ring
     · simp only [coordinateInsertion,Fin.insertNth_apply_succAbove,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
 def coordinateInsertionAffine {n : ℕ} (p : Fin (n+1) → ℝ) (d : ℝ) (j : Fin (n+1)) :
     (Fin n → ℝ) →ᵃ[ℝ] (Fin (n+1) → ℝ) where
   toFun := coordinateInsertion p d j
   linear := coordinateInsertionLinear p j
   map_vadd' x y := by
     funext i
     rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨i,rfl⟩
     · simp only [coordinateInsertion,coordinateInsertionLinear,LinearMap.coe_mk,AddHom.coe_mk,
         vadd_eq_add,Pi.add_apply,Fin.insertNth_apply_same,mul_add,Finset.sum_add_distrib,zero_sub]
       ring
     · simp only [coordinateInsertion,coordinateInsertionLinear,LinearMap.coe_mk,AddHom.coe_mk,
         vadd_eq_add,Pi.add_apply,Fin.insertNth_apply_succAbove]

 def projectedBinarySet {n : ℕ} (V : Finset (Fin (n+1) → Bool)) (j : Fin (n+1)) : Finset (Fin n → Bool) :=
   V.image (fun v i => v (j.succAbove i))

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.AffineEliminationMath
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools
open RawStack

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.AffineIntegerHeight
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.ConvexTools
open RawStack GLS.DeterminantBounds

 def AffineIntegerHeight {m n : ℕ} (J : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ) : Prop :=
   ∃ (D : ℤ) (U : Matrix (Fin m) (Fin n) ℤ) (v : Fin m → ℤ),D≠0 ∧ D.natAbs ≤ 2^J ∧
     (∀ i j,(U i j).natAbs ≤ 2^J ∧ A i j=(U i j:ℚ)/D) ∧
     (∀ i,(v i).natAbs ≤ 2^J ∧ b i=(v i:ℚ)/D)

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.HyperplaneApproximationMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplaneCoefficientHeight
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

end EdgeSublinearMWIS.Main.ConvexTools

namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools
 
end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.DiagonalMaximumMath
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.PositiveMatrixCauchy
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.PositiveMatrixEntryBound
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.EllipsoidThinDirection
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

 def normalizedColumn {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Fin n → ℝ :=
   fun i => B i k/B k k
 def inverseEllipsoid {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (c : Fin n → ℝ) : Set (Fin n → ℝ) :=
   {x | (x-c) ⬝ᵥ (B *ᵥ (x-c))≤1}

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.GLSEllipsoidBall
noncomputable section
-- Adapted from https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/EllipsoidBall.lean
-- Original work licensed under Apache-2.0; license retained at external-lp/LICENSE.

open scoped BigOperators Matrix

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι : Type} [Fintype ι] [DecidableEq ι]

end EdgeSublinearMWIS.Main.GLS.EllipsoidBall
end

-- Solutions.EllipsoidLargeInverseDiagonal
noncomputable section

open scoped BigOperators Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.EllipsoidMath

end EdgeSublinearMWIS.Main.EllipsoidMath
end

-- Solutions.ThinDirectionMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.GLSEllipsoidStateBounds
noncomputable section
-- Adapted from EdouardBonnet/lax-109476, commit 0a042604c7ae1ef4cd9a4c7d82eb902f313d4864.
-- Apache-2.0; original license retained in external-lp/LICENSE.

open scoped BigOperators

namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize

open Matrix EllipsoidBounds EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence RationalRounding
open EdgeSublinearMWIS.Main.GLS.Cast

end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
end

-- Solutions.EllipsoidSequenceHeight
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
open EllipsoidSequence EllipsoidRounding EllipsoidPrecision Cast

end EdgeSublinearMWIS.Main.GLS.EllipsoidStateSize
end

-- Solutions.OracleCounterTermination
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleQueryBudget
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools

 def oracleQueries : Polynomial ℕ := Polynomial.C 203*Polynomial.X^5

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RecoveryUniformHeight
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath ConvexTools

 def recoveryHeight (N : ℕ) : ℕ := approximationExponent N+phaseBudget N+2*N+4
 def affineHeight (N n : ℕ) : ℕ := (N-n)*(recoveryHeight N+1)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCoreModel
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 def affineLift {N n : ℕ} (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ)
     (z : Fin n → ℝ) : Fin N → ℝ := (A.map (Rat.castHom ℝ)) *ᵥ z+(fun i => (b i:ℝ))

 structure CoreModel {N n : ℕ} (Orig : Finset (Fin N → Bool)) (st : OracleCoreState)
     (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool)) : Prop where
   order : n ≤ N
   affineRows : RepresentsRectMatrix st.1.1 A
   affineOffsets : RepresentsVector st.1.2 (rationalVector b)
   rowsCanonical : ∀ row∈st.1.1,VectorCanonical row
   offsetsCanonical : VectorCanonical st.1.2
   height : ConvexTools.AffineIntegerHeight (affineHeight N n) A b
   phase : PhaseGeometry V st.2
   lifts : ∀ z∈binaryHull V,affineLift A b z∈binaryHull Orig
   nonempty : Orig.Nonempty → V.Nonempty
 def CoreGeometry (N : ℕ) (Orig : Finset (Fin N → Bool)) (st : OracleCoreState) : Prop :=
   ∃ (n : ℕ) (A : Matrix (Fin N) (Fin n) ℚ) (b : Fin N → ℚ) (V : Finset (Fin n → Bool)),CoreModel Orig st A b V

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RecoveryParametersSemantics
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleModelElimination
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidRecoveryMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath ConvexTools

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.BinaryScaledUnit
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.EllipsoidPhaseRecovery
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open InverseMath EllipsoidMath ConvexTools GLS.EllipsoidSequence GLS.Cast GLS.EllipsoidRounding

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePhaseHeight
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.EllipsoidStateSize

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleBoundaryGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence ConvexTools

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.EllipsoidHistoryAppend
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleModelPhaseAdvance
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleBigCutGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCutGeometry
noncomputable section

open scoped Classical BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.ConvexTools

end EdgeSublinearMWIS.Main.ConvexTools
end

-- Solutions.OracleValidCut
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools GLS.Cast

 def StrictOracleCut {N : ℕ} (Orig : Finset (Fin N → Bool)) (cut : RationalHalfspace N)
     (y : Fin N → ℚ) : Prop :=
   cut.bound < cut.eval y ∧ ∀ z∈binaryHull Orig,cut.evalReal z ≤ (cut.bound:ℝ)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleClearedCutGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools GLS.Cast

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleSmallCutGeometry
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.Cast

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePhaseCenter
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePreparedCutSoundness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.Cast

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleActiveCutSoundness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 def rationalWords {n : ℕ} (a : Fin n → ℚ) : SignedVector := List.ofFn (fun i => codeWords (rationalCode (a i)))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleSerializationMath
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ProgramOutputUnique
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main

end EdgeSublinearMWIS.Main
end

-- Solutions.OracleTranscriptState
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack

 def oracleTranscriptState {N : ℕ} (cuts : List (RationalHalfspace N)) : OracleState :=
   oracleExecute (N,cuts.map (fun cut => rationalWords cut.normal))

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleDialogueSoundness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

 def ImplementsBinaryOracle (E : Program) : Prop := ∀ input : List Bool,Evaluates E input (binaryOracle input)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.WordRationalHeight
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.MatrixInverseValidClock
noncomputable section

open scoped Classical
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

 def ValidPositiveMatrix (bs : SignedMatrix) : Prop :=
   ∃ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),RepresentsMatrix bs A ∧ (castMatrix A).PosDef

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.HyperplaneApproximationClock
noncomputable section

open scoped Classical
open LLLFactor.RedBasis
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ValidHyperplaneInput (s : HyperplaneApproximationInput) : Prop :=
   ∃ (u c : Fin s.1 → ℚ),RepresentsVector s.2.1 (rationalVector u) ∧
     RepresentsVector s.2.2 (rationalVector c)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedClockComposition
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def RestrictedPoly {f : α → β} (R : Realizer f) (P : α → Prop) : Prop :=
   ∃ C q : ℕ,0 < C ∧ ∀ x,P x → R.time x ≤ C*(volume x+1)^q ∧ volume (f x) ≤ C*(volume x+1)^q

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.EllipsoidRecoveryClock
noncomputable section

open scoped Classical
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds InverseMath

 def ValidRecoveryInput (s : EllipsoidRecoveryInput) : Prop :=
   0 < s.1 ∧ ∃ (A : Matrix (Fin s.1) (Fin s.1) ℚ) (c : Fin s.1 → ℚ),
     RepresentsMatrix s.2.1 A ∧ RepresentsVector s.2.2 (rationalVector c) ∧ (castMatrix A).PosDef

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleReductionClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ValidReductionPhase (st : EllipsoidPhaseState) : Prop := ValidRecoveryInput (phaseRecoveryInput st)
 def ValidReductionCore (st : OracleCoreState) : Prop := ValidReductionPhase st.2

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedSelectiveChoose
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.SelectiveChoosePolynomial
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace OAI.ThreeMachine.StackCompiler.Realizer
variable {α β : Type} [Coding α] [Coding β]
 
end OAI.ThreeMachine.StackCompiler.Realizer
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.OracleBranchClocks
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def BoundarySafe (st : OracleCoreState) : Prop := oracleAtBoundary st=true → ValidReductionCore st
 
 def BigCutSafe (s : OraclePreparedCut) : Prop := BoundarySafe (oraclePhaseAdvance s)

 def NonzeroCutSafe (s : OraclePreparedCut) : Prop := oracleSmall s=false → BigCutSafe s
 
 def PreparedSafe (s : OraclePreparedCut) : Prop := oraclePreparedNonzero s=true → NonzeroCutSafe s
 
 def ActiveCutSafe (s : OracleCutInput) : Prop := PreparedSafe (oraclePrepareCut (s.1,s.2.2))
 
 def OracleCutSafe (s : OracleCutInput) : Prop := s.2.1=false → ActiveCutSafe s

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleClockValidity
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.Cast

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleHeightBounds
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open ConvexTools GLS.EllipsoidStateSize

 def phaseHeight (N : ℕ) : ℕ := 2050*(N+1)^4

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OraclePhaseSize
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open GLS.EllipsoidSequence GLS.EllipsoidStateSize

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleCoreSize
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds ConvexTools

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleDialogueClockValidity
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ValidExecutionInput (s : ℕ×SignedMatrix) : Prop :=
   ∃ (E : Program) (bound : Polynomial ℕ) (Orig : Finset (Fin s.1 → Bool))
     (qs : List (Fin s.1 → ℚ)) (cuts : List (RationalHalfspace s.1)),
     ImplementsBinaryOracle E ∧ AdmissibleDialogue E bound s.1 Orig qs cuts ∧
       s.2=cuts.map (fun cut => rationalWords cut.normal)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β : Type} [Coding α] [Coding β]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.RestrictedComposedFoldClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.OracleExecutionClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleTranscriptParserClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def oracleHeaderMagnitude (L : List Bool) : ℕ := (oracleHeader L).1+(oracleHeader L).2.1

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleOutputBounds
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.RestrictedExpandedClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RealizerBounds
open OAI.ThreeMachine.StackCompiler
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

 def RestrictedExpanded {f : α → β} (R : Realizer f) (N : α → ℕ) (P : α → Prop) : Prop :=
   ∃ C q : ℕ,0 < C ∧ ∀ x,P x → R.time x ≤ C*(volume x+N x+1)^q ∧ volume (f x) ≤ C*(volume x+N x+1)^q

end EdgeSublinearMWIS.Main.RealizerBounds
end

-- Solutions.OracleByteClock
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def ValidOracleWord (L : List Bool) : Prop := ValidExecutionInput (parseOracleTranscript L)

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleWorkPolynomials
noncomputable section

open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main.RawStack
open OAI.ThreeMachine.StackCompiler EdgeSublinearMWIS.Main.RealizerBounds

 def oracleWorkBase (bound : Polynomial ℕ) : Polynomial ℕ :=
   Polynomial.C 50*(Polynomial.X+bound+oracleQueries+Polynomial.C 1)^2

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.OracleFiniteProgram
noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace EdgeSublinearMWIS.Main
open RawStack

end EdgeSublinearMWIS.Main
end

-- Solutions.OracleQualitativeCorrectness
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main.RawStack

end EdgeSublinearMWIS.Main.RawStack
end

-- Solutions.ExactBinaryOracleLocal
noncomputable section

open scoped Classical BigOperators
open LLLFactor.RedBasis Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
namespace EdgeSublinearMWIS.Main
open RawStack OAI.ThreeMachine.StackCompiler RealizerBounds

end EdgeSublinearMWIS.Main
end

-- Solutions.Sol_exact_binary_oracle
noncomputable section

end


