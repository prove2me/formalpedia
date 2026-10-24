-- Prove2me | Definitions.Def_OAIQWRHT004
-- name    : OAIQWRHT004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T22:21:17.377338+00:00
-- url     : https://prove2.me/theorems/23d02921-dd7b-47fe-8c9c-45a6aa253511
-- title:
--   OpenAI rational hitting lists split: definitions bundle OAIQWRHT004
-- statement:
--   One of the five definitions bundles (`OAIQWRHT000` to `OAIQWRHT004`) of the split of OpenAI's proof that one deterministic Turing machine writes, in polynomial time, a polynomial-size list of rational matrix tuples hitting every admissible nonzero noncommutative rational formula of size at most $s$ (`OAI.RationalHitting.main`, the paper's Theorem 1.1). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Computability/RationalHitting` (OpenAI, *Polynomial Hitting Lists for Noncommutative Rational Formulas*, OpenAI Math Release, September 24, 2026, result family 116, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies. Among them are the cyclotomic grid construction of the list (`Generator.list`, `ExecutableGenerator.list`), the pencil certificates, the binary arithmetic procedures, the stack language with its time bounds, and the compiler to `Turing.TM0` machines. The bundles split the material only to keep each one within the platform's compile limits.
--
--   The definitions of the published statement (`Formula`, `Evaluates`, `Admissible`, `Nonzero`, `Output`, `encodeOutput`, `Machine`, `run`, `OutputsWithin`, `Hits`, `MainStatement` and the rest) are not repeated: the bundles import them from the published bundle `Def_RationalHitting`. It also imports the bundles `OAIQWRHT002`, `OAIQWRHT003` of this split.
--
--   Modules (some only in part): `DenseDeterminant`, `GridComputation`, `LiftComputation`, `MatrixComputation`, `OutputComputation`, `RationalArithmetic`, `RationalBinary`, `StackLanguage`, `TaylorComputation`, `UnaryArithmetic`.
--
--   The theorems the definitions do not need are proved in the three solutions of this split. One proves the published intermediate statement `OAI.RationalHitting.Generator.list_hits` (the paper's Proposition 5.1), one proves `OAI.RationalHitting.ExecutableGenerator.implementation` (Proposition 5.3) using it, and the third proves `OAI.RationalHitting.main` from both. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Polynomial Hitting Lists for Noncommutative Rational Formulas, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 116; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026/Polynomial-Hitting-Lists-for-Noncommutative-Rational-Formulas-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability/RationalHitting at commit adc7f12

import Mathlib
import Definitions.Def_RationalHitting
import Definitions.Def_OAIQWRHT002
import Definitions.Def_OAIQWRHT003

section
-- module Solutions.OAIQW_RationalHitting.StackLanguage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite structured binary-stack language. Every primitive is a push,
pop, or transfer. -/
namespace RationalHitting.StackLanguage
open Turing
open RationalHitting.TMTime
variable {K : Type} [DecidableEq K]

/-- Possible jump targets; inspecting a head has only three finite cases. -/
def successors : List (Program K) → Finset (List (Program K))
  | [] => ∅
  | .skip :: ps => {ps}
  | .push _ _ :: ps | .drop _ :: ps | .transfer _ _ :: ps => {ps}
  | .seq p q :: ps => {p::q::ps}
  | .branch _ p q r :: ps => {p::ps,q::ps,r::ps}
  | .loop k p :: ps => {ps,p::.loop k p::ps}

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.RationalBinary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

/-- Exact final canonical binary fraction, with a cubic bit-time stack implementation.
This supplies the output-format obligation of the uniform list generator. -/
theorem eval_rationalEncode (s : Store (Fin 16)) (a b : ℤ) (hb : b≠0)
    (h0 : s 0=a.natAbs.bits) (h5 : s 5=b.natAbs.bits)
    (h12 : s 12=[decide (a<0)]) (h13 : s 13=[decide (b<0)]) (h15 : s 15=[])
    (hs : ∀ i : Fin 16, i.val<12 → i≠0 → i≠5 → s i=[])
    (B : ℕ) (ha : a.natAbs.bits.length≤B) (hd : b.natAbs.bits.length≤B) :
    ∃ t ≤ 3100*(B+1)^3, Eval rationalEncode s
      (update (update (update s 0 []) 5 []) 14 (encodeRat (Rat.divInt a b)++s 14)) t := by
  let g := Nat.gcd a.natAbs b.natAbs
  let A := a.natAbs/g
  let D := b.natAbs/g
  let sign := decide ((Rat.divInt a b).num<0)
  have hsg : (if s 0=[] then false else decide (a<0) ^^ decide (b<0))=sign := by
    have hz : a.natAbs.bits=[] ↔ a=0 := by
      constructor
      · intro he
        have hy := congrArg wordValue he
        simpa using hy
      · intro he; simp [he]
    simp only [h0,hz]
    exact (RationalCanonical.divInt_sign a b hb).symm
  have hA : A.bits.length≤B := by
    apply le_trans _ ha
    rw [Nat.size_eq_bits_len,Nat.size_le]
    have he := wordValue_lt a.natAbs.bits
    simp only [wordValue_bits] at he
    exact (Nat.div_le_self _ _).trans_lt he
  have hD : D.bits.length≤B := by
    apply le_trans _ hd
    rw [Nat.size_eq_bits_len,Nat.size_le]
    have he := wordValue_lt b.natAbs.bits
    simp only [wordValue_bits] at he
    exact (Nat.div_le_self _ _).trans_lt he
  let u1 := update s 15 [sign]
  let u2 := update (update u1 0 A.bits) 5 D.bits
  let u3 := update (update u2 5 []) 14 (encodedWord D.bits++s 14)
  let u4 := update (update u3 0 []) 14 (encodedWord A.bits++encodedWord D.bits++s 14)
  obtain ⟨t1,ht1,e1⟩ := eval_fractionSign s (decide (a<0)) (decide (b<0)) h12 h13
  have ev1 : Eval fractionSign s u1 t1 := by simpa [u1,hsg,h15] using e1
  have hs1 : fractionScratch (fun k => u1 (reduceReg k)) := by
    intro k hk0 hk5
    have hv : (reduceReg (fractionArith k)).val<12 := by simp [reduceReg,fractionArith]
    have hn : reduceReg (fractionArith k) ≠ (15 : Fin 16) := by
      intro hh; have hh' := congrArg (fun x : Fin 16 => x.val) hh; change k.val=15 at hh'; omega
    have hn0 : reduceReg (fractionArith k) ≠ (0 : Fin 16) := by
      intro hh; apply hk0; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) hh
    have hn5 : reduceReg (fractionArith k) ≠ (5 : Fin 16) := by
      intro hh; apply hk5; apply Fin.ext; exact congrArg (fun x : Fin 16 => x.val) hh
    simpa [u1,hn] using hs _ hv hn0 hn5
  obtain ⟨t2,ht2,e2⟩ := eval_fractionReduce_rename reduceReg reduceReg_inj u1 hs1
    (by simpa [u1,reduceReg] using hs 10 (by decide) (by decide) (by decide))
    (by simpa [u1,reduceReg] using hs 11 (by decide) (by decide) (by decide))
    a.natAbs b.natAbs B (by simpa [u1,reduceReg] using h0)
    (by simpa [u1,reduceReg] using h5) (Int.natAbs_pos.mpr hb) ha hd
  have ev2 : Eval (fractionReduce.rename reduceReg) u1 u2 t2 := e2
  have h1 : s 1=[] := hs 1 (by decide) (by decide) (by decide)
  have h2 : s 2=[] := hs 2 (by decide) (by decide) (by decide)
  have ev3 : Eval (encodeWord.rename denominatorReg) u2 u3 (11*D.bits.length+7) := by
    simpa [denominatorReg,u3,u2,u1] using
      eval_encodeWord_rename denominatorReg denominatorReg_inj u2
        (by simp [denominatorReg,u2,u1,h1]) (by simp [denominatorReg,u2,u1,h2])
  have ev4 : Eval (encodeWord.rename numeratorReg) u3 u4 (11*A.bits.length+7) := by
    simpa [numeratorReg,u4,u3,u2,u1,List.append_assoc] using
      eval_encodeWord_rename numeratorReg numeratorReg_inj u3
        (by simp [numeratorReg,u3,u2,u1,h1]) (by simp [numeratorReg,u3,u2,u1,h2])
  have ev5 := Eval.transfer (15 : Fin 16) 14 u4
  have hh := Eval.seq ev1 (Eval.seq ev2 (Eval.seq ev3 (Eval.seq ev4 ev5)))
  have heq : transfer 15 14 u4 =
      update (update (update s 0 []) 5 []) 14 (encodeRat (Rat.divInt a b)++s 14) := by
    rw [transfer_cons (by decide) u4 sign [] (by simp [u4,u3,u2,u1])]
    funext k
    by_cases hk0 : k=0 <;> by_cases hk5 : k=5 <;> by_cases hk14 : k=14 <;> by_cases hk15 : k=15 <;>
      simp_all [u4,u3,u2,u1,encodeRat,encodedWord_bits,
        RationalCanonical.divInt_num_abs a b hb,RationalCanonical.divInt_den a b hb,A,D,g,sign,
        List.append_assoc]
  refine ⟨1+t1+(1+t2+(1+(11*D.bits.length+7)+(1+(11*A.bits.length+7)+1))),?_,?_⟩
  · linarith only [ht1,ht2,hA,hD,Nat.zero_le (B^2),Nat.zero_le (B^3)]
  · simpa only [rationalEncode,heq] using hh

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.DenseDeterminant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open Function

instance instCodingDenseSquare : Coding DenseSquare := ⟨fun a => code (Unary.mk a.dim,a.rows)⟩

end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.UnaryArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
open Function

def divStep (a : DivState) : DivState :=
  (a.1,if 0<a.1.val ∧ a.1.val≤a.2.2.val+1 then
    (⟨a.2.1.val+1⟩,⟨a.2.2.val+1-a.1.val⟩) else (a.2.1,⟨a.2.2.val+1⟩))

end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

namespace Procedure

def wordLength : Procedure _root_.id unaryCode List.length where
  Registers := Fin 2
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := unaryLength 0 1
  bound := 4*TimeBound.variable+1
  correct a := by
    refine ⟨4*a.length+1,by simp,?_⟩
    have hh := eval_unaryLength (a:=(0:Fin 2)) (b:=1) (by decide) (single 0 a)
    simpa [single,unaryCode] using hh
  size a := by simp [unaryCode];omega

end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
open Function

def doubleState (a : Unary×Unary) : Unary×Unary := (a.1,⟨doubleBelow a.1.val a.2.val⟩)

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.RationalArithmetic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
open Function

variable {K : Type} [DecidableEq K]

lemma eval_rationalClean (a : ℤ) (b : NZInt) : ∃ t≤4000*(a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3,
    Eval rationalClean (both (0:Fin 16) 5 (intCode a) (intCode b.val))
      (single 14 (encodeRat (Rat.divInt a b.val))) t := by
  let s := both (0:Fin 16) 5 (intCode a) (intCode b.val)
  let u := update (update s 0 a.natAbs.bits) 12 [decide (a<0)]
  let v := update (update u 5 b.val.natAbs.bits) 13 [decide (b.val<0)]
  have e1 : Eval (unpackInt 0 12) s u 5 := by
    simpa [s,u,both,single] using eval_unpackInt (a:=(0:Fin 16)) (sg:=12) (by decide) s a (by simp [s,both,single])
  have e2 : Eval (unpackInt 5 13) u v 5 := by
    simpa [v,u,s,both,single] using eval_unpackInt (a:=(5:Fin 16)) (sg:=13) (by decide) u b.val
      (by simp [u,s,both,single])
  obtain ⟨t,ht,he⟩ := eval_rationalEncode v a b.val b.property
    (by simp [v,u,s,both,single]) (by simp [v]) (by simp [v,u]) (by simp [v])
    (by simp [v,u,s,both,single])
    (by intro i hi h0 h5;simp [v,u,s,both,single,h0,h5,show i≠12 by omega,show i≠13 by omega])
    (a.natAbs.bits.length+b.val.natAbs.bits.length+1) (by omega) (by omega)
  let w := update (update (update v 0 []) 5 []) 14 (encodeRat (Rat.divInt a b.val))
  have e3 : Eval rationalEncode v w t := by simpa [w,v,u,s,both,single] using he
  have e4 : Eval (clear 12) w (update w 12 []) 3 := by simpa [w,v,u] using eval_clear (12:Fin 16) w
  have ho : update (update w 12 []) 13 []=single 14 (encodeRat (Rat.divInt a b.val)) := by
    funext k;fin_cases k <;> simp [w,v,u,s,both,single]
  have e5 : Eval (clear 13) (update w 12 []) (single 14 (encodeRat (Rat.divInt a b.val))) 3 := by
    have hh := eval_clear (13:Fin 16) (update w 12 [])
    rw [ho] at hh
    simpa [w,v] using hh
  refine ⟨1+5+(1+5+(1+t+(1+3+3))),?_,Eval.seq e1 (Eval.seq e2 (Eval.seq e3 (Eval.seq e4 e5)))⟩
  have hp : (a.natAbs.bits.length+b.val.natAbs.bits.length+2)^3≤
      (a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3 := by gcongr ; omega
  have hp0 : 1≤(a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3 := by
    have hpos : 0<(a.natAbs.bits.length+b.val.natAbs.bits.length+8)^3 := by positivity
    omega
  simp only [Nat.add_assoc,Nat.reduceAdd] at ht hp hp0 ⊢
  omega

namespace Procedure

def rationalEncode : Procedure (pairCode intCode (fun b : NZInt => intCode b.val)) _root_.id
    (fun a => encodeRat (Rat.divInt a.1 a.2.val)) :=
  fromBinary rationalClean 0 5 14 (by decide) (4000*(TimeBound.variable+1)^3)
    (by intro a b;simpa only [intCode_length,TimeBound.eval_mul,TimeBound.eval_numeral,
      TimeBound.eval_pow,TimeBound.eval_add,TimeBound.eval_variable,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.reduceAdd,id_eq] using eval_rationalClean a b)
    (by
      intro a b
      let L := a.natAbs.bits.length+b.val.natAbs.bits.length+1
      have ha : a.natAbs.size≤L := by rw [←Nat.size_eq_bits_len];dsimp [L];omega
      have hb : b.val.natAbs.size≤L := by rw [←Nat.size_eq_bits_len];dsimp [L];omega
      have hh := EncodingBounds.encodeRat_ratio_le a b.val b.property L (Nat.size_le.mp ha) (Nat.size_le.mp hb)
      have hp : L+7≤(L+7)^3 := Nat.le_self_pow (by decide) _
      simp only [intCode_length,TimeBound.eval_mul,TimeBound.eval_numeral,TimeBound.eval_pow,
        TimeBound.eval_add,TimeBound.eval_variable,id_eq]
      dsimp [L] at hh hp
      simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Nat.reduceAdd] at hp ⊢
      omega)
end Procedure
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

namespace Unary
instance instOfNat (n : ℕ) : OfNat Unary n := ⟨⟨n⟩⟩
instance instAdd : Add Unary := ⟨fun a b => ⟨a.val+b.val⟩⟩
instance instSub : Sub Unary := ⟨fun a b => ⟨a.val-b.val⟩⟩
instance instDiv : Div Unary := ⟨fun a b => ⟨a.val/b.val⟩⟩
instance instMod : Mod Unary := ⟨fun a b => ⟨a.val%b.val⟩⟩
instance instPowNat : Pow Unary ℕ := ⟨fun a b => ⟨a.val^b⟩⟩
def toInt (a : Unary) : ℤ := a.val
def choose (a b : Unary) : ℤ := a.val.choose b.val
def powInt (a : ℤ) (b : Unary) : ℤ := a^b.val
def eqb (a b : Unary) : Bool := decide (a.val=b.val)
def ltb (a b : Unary) : Bool := decide (a.val<b.val)
end Unary

end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.TaylorComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
open scoped BigOperators

namespace Runtime

abbrev TaylorArgs := Unary×ℤ×ℤ×Unary×Unary

end Runtime
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.LiftComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RationalHitting.StackLanguage
open scoped BigOperators
namespace Runtime

abbrev LiftArgs := (Unary×Unary×Unary)×(ℤ×ℤ×ℤ×ℤ)×(Unary×Unary×Unary×Unary)
abbrev LiftTermArgs := ((LiftArgs×Unary)×Unary)×Unary

end Runtime
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.MatrixComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
namespace Runtime

abbrev GridPoint := Unary×Unary×Unary

def gridFn (x : GridPoint) : Fin 3 → ℕ := ![x.1.val,x.2.1.val,x.2.2.val]

def matrix (p : Params) (x : GridPoint) (a : Unary) : DenseSquare :=
  ⟨p.m*p.q,fun i j => entry p.m p.N p.q a.val x.1.val x.2.1.val x.2.2.val i.val j.val⟩

end Runtime
end RationalHitting.StackLanguage


end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.GridComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
namespace Runtime

abbrev TupleWordArgs := (Params×GridPoint)×DenseSquare×ℤ

def tupleWord (p : Params) (x : GridPoint) (A : DenseSquare) (den : ℤ) : BitWord :=
  ⟨(List.range p.n).flatMap fun i => (matrixWord A (matrix p x ⟨i+1⟩) den).val⟩

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage
namespace Runtime

def point (p : Params) (x : GridPoint) : List BitWord :=
  let A := matrix p x 0
  let den := A.val.det
  if den=0 then [] else [tupleWord p x A den]

end Runtime
end RationalHitting.StackLanguage


namespace RationalHitting.StackLanguage

namespace Runtime

def words (p : Params) : List BitWord :=
  (List.range p.H).flatMap fun t => (List.range p.H).flatMap fun q =>
    (List.range p.H).flatMap fun r => point p (⟨t+1⟩,⟨q+1⟩,⟨r+1⟩)

end Runtime
end RationalHitting.StackLanguage

end OAI
end

section
-- module Solutions.OAIQW_RationalHitting.OutputComputation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace RationalHitting.StackLanguage
namespace Runtime

/-- Literal canonical output, including dimension and accepted-list length. -/
def word (p : Params) : BitWord :=
  ⟨encodeNat (p.m*p.q)++encodeNat (words p).length++(words p).flatMap BitWord.val⟩

end Runtime
end RationalHitting.StackLanguage

end OAI
end


