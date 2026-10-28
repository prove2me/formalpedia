-- Prove2me | Definitions.Def_OAIQ076M007
-- name    : OAIQ076M007
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T09:03:24.944032+00:00
-- url     : https://prove2.me/theorems/67f829d0-6b6e-4a77-98c9-166e970e7414
-- title:
--   Definitions bundle OAIQ076M007 of the split of OpenAI, Constant-factor hardness of Min-UnCut (result family 102)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MinUncut.main`, carved from OpenAI's openai/math development (OpenAI, *Constant-factor hardness of Min-UnCut (result family 102)*, OpenAI Math Release, September 23, 2026, result family 102, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 318 declarations of OpenAI's Lean: 108 definitions, 3 inductive types or structures, 4 instances and 203 theorems. The definitions and types are `OAI.MinUncut.Costed.Arena.OutputState.tick`, `OAI.MinUncut.Costed.Arena.outRead`, `OAI.MinUncut.Costed.Arena.outputStep`, `OAI.MinUncut.Costed.Arena.prepareUnbounded`, `OAI.MinUncut.Costed.Arena.stopExpr`, `OAI.MinUncut.Costed.CodeRun.finiteMachine`, `OAI.MinUncut.Costed.Expr.edge`, `OAI.MinUncut.Costed.Expr.or`, `OAI.MinUncut.Costed.FiberPrefix.code`, `OAI.MinUncut.Costed.GraphCodec.outputsInTime`, `OAI.MinUncut.Costed.GraphRegisters.RenderState.tick`, `OAI.MinUncut.Costed.GraphRegisters.accumulatedEdge`, `OAI.MinUncut.Costed.GraphRegisters.cumulative`, `OAI.MinUncut.Costed.GraphRegisters.demandEqual`, `OAI.MinUncut.Costed.GraphRegisters.demandLeft`, `OAI.MinUncut.Costed.GraphRegisters.demandOffset`, `OAI.MinUncut.Costed.GraphRegisters.demandRight`, `OAI.MinUncut.Costed.GraphRegisters.lastVertexExpr`, `OAI.MinUncut.Costed.GraphRegisters.localEdge`, `OAI.MinUncut.Costed.GraphRegisters.nextCol`, `OAI.MinUncut.Costed.GraphRegisters.nextCount`, `OAI.MinUncut.Costed.GraphRegisters.nextRow`, `OAI.MinUncut.Costed.GraphRegisters.normalizeProgram`, `OAI.MinUncut.Costed.GraphRegisters.privateBase`, `OAI.MinUncut.Costed.GraphRegisters.rawGraphWords`, `OAI.MinUncut.Costed.GraphRegisters.rawRow`, `OAI.MinUncut.Costed.GraphRegisters.rawTable`, `OAI.MinUncut.Costed.GraphRegisters.renderRaw`, `OAI.MinUncut.Costed.GraphRegisters.renderTick`, `OAI.MinUncut.Costed.GraphRegisters.vertexExpr`, `OAI.MinUncut.Costed.PolyProgram.prec`, `OAI.MinUncut.Costed.PolyProgram.zero`, `OAI.MinUncut.Costed.SourceWords.demandStageWords`, `OAI.MinUncut.Costed.SourceWords.equationExpr`, `OAI.MinUncut.Costed.SourceWords.firstExpr`, `OAI.MinUncut.Costed.SourceWords.secondAddress`, `OAI.MinUncut.Costed.SourceWords.secondExpr`, `OAI.MinUncut.Costed.SourceWords.signatureExpr`, `OAI.MinUncut.Costed.SourceWords.slotExpr`, `OAI.MinUncut.Costed.SourceWords.thresholdExpr` and 71 more.
--
--   **Sources.** They come from these modules of lean/OAI/Computability, in whole or in part: `MinUncut_Analysis_FiniteGaussianLaw`, `MinUncut_Analysis_GaussianSmallBall`, `MinUncut_Analysis_LiteralGaussian`, `MinUncut_Encoding_RawGraphEncoding`, `MinUncut_Encoding_SignatureEncoding`, `MinUncut_Estimates_ActualBoxBound`, `MinUncut_Estimates_Assembly`, `MinUncut_Estimates_Basic`, `MinUncut_Estimates_CodeComputability`, `MinUncut_Estimates_CodeContinuations`, `MinUncut_Estimates_Convolution`, `MinUncut_Estimates_CountedWordParser`, `MinUncut_Estimates_CoupledAnswer`, `MinUncut_Estimates_FiberPrefix`, `MinUncut_Estimates_FirstError`, `MinUncut_Estimates_PolynomialRecursor`, `MinUncut_Estimates_SamplerAssembly`, `MinUncut_Estimates_SamplerCost`, `MinUncut_Estimates_TM2Costed`, `MinUncut_Estimates_UniformEquationOutput`, `MinUncut_Estimates_UniformGrid`, `MinUncut_Estimates_WeightedTestLaw`, `MinUncut_Games_QuestionExpressions`, `MinUncut_Graphs_CanonicalPathGraph`, `MinUncut_Graphs_CanonicalSamplerGraph`, `MinUncut_Graphs_DemandExpressions`, `MinUncut_Graphs_DemandOrder`, `MinUncut_Graphs_GraphSize`, `MinUncut_Graphs_GraphWordCodec`, `MinUncut_Graphs_HonestRows`, `MinUncut_Graphs_SignedGraph`, `MinUncut_Machines_CodeFiniteMachine`, `MinUncut_Machines_FiniteAlphabetBounds`, `MinUncut_Machines_FramedWordDecoder`, `MinUncut_Machines_GraphRenderMachine`, `MinUncut_Machines_MachineCompare`, `MinUncut_Machines_MachineFiniteAlphabet`, `MinUncut_Machines_MachineRegularTableRuntime`, `MinUncut_Machines_MachineSubroutine`, `MinUncut_Machines_MachineSubstitution`, `MinUncut_Machines_Runtime`, `MinUncut_Machines_RuntimeModel2`, `MinUncut_PCP_Occurrences`, `MinUncut_PCP_RawInitialTables`, `MinUncut_Search_ArithmeticTactic`, `MinUncut_Search_InnerParameters`, `MinUncut_Search_OuterParameters`, `MinUncut_Search_ParameterFields`, `MinUncut_Search_RationalBasics`, `MinUncut_Search_RationalInner`, `MinUncut_Search_RawRationalArithmetic`, `MinUncut_Search_TemplateArithmetic`.
--
--   **Imports.** It imports the published bundle `Def_MinUncut`; the bundles `OAIQ076M000`, `OAIQ076M001`, `OAIQ076M002` and `OAIQ076M003` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ076M014`, `OAIQ076M015`, `OAIQ076M016`, `OAIQ076M017`, `OAIQ076M018`, `OAIQ076M019`, `OAIQ076M020` and `OAIQ076M021`.
-- source:
--   OpenAI, Constant-factor hardness of Min-UnCut (result family 102), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 102; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Constant-factor-hardness-of-Min-UnCut-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Computability at commit adc7f12

import Mathlib
import Definitions.Def_MinUncut
import Definitions.Def_OAIQ076M000
import Definitions.Def_OAIQ076M001
import Definitions.Def_OAIQ076M002
import Definitions.Def_OAIQ076M003

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_Occurrences
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Hastad.SourceOccurrences

open MinUncutGames.Reduction.CloneGap
open scoped BigOperators

namespace Encoding

theorem nodup_enumerate {α : Type} (a : Encoding α) : a.enumerate.Nodup :=
  List.nodup_ofFn_ofInjective a.code.symm.injective

end Encoding

end MinUncutGames.Foundations.Hastad.SourceOccurrences

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RawRationalArithmetic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Preprocess
namespace RawRat

def value (q : RawRat) : ℚ := ((q.1:ℚ)-(q.2.1:ℚ))/((q.2.2:ℚ)+1)
def ofNat (n : ℕ) : RawRat := (n,0,0)
def neg (q : RawRat) : RawRat := (q.2.1,q.1,q.2.2)
def add (q r : RawRat) : RawRat :=
  (q.1*(r.2.2+1)+r.1*(q.2.2+1),q.2.1*(r.2.2+1)+r.2.1*(q.2.2+1),
    (q.2.2+1)*(r.2.2+1)-1)
def mul (q r : RawRat) : RawRat :=
  (q.1*r.1+q.2.1*r.2.1,q.1*r.2.1+q.2.1*r.1,(q.2.2+1)*(r.2.2+1)-1)
def inv (q : RawRat) : RawRat :=
  if q.1=q.2.1 then ofNat 0 else
  if q.2.1<q.1 then (q.2.2+1,0,q.1-q.2.1-1) else (0,q.2.2+1,q.2.1-q.1-1)
def le (q r : RawRat) : Prop :=
  q.1*(r.2.2+1)+r.2.1*(q.2.2+1) ≤ r.1*(q.2.2+1)+q.2.1*(r.2.2+1)
def lt (q r : RawRat) : Prop :=
  q.1*(r.2.2+1)+r.2.1*(q.2.2+1) < r.1*(q.2.2+1)+q.2.1*(r.2.2+1)
instance instDecidableLe (q r : RawRat) : Decidable (le q r) := inferInstanceAs (Decidable (_≤_))

@[simp] lemma value_nat (n : ℕ) : (ofNat n).value=n := by simp [ofNat,value]
@[simp] lemma value_neg (q : RawRat) : q.neg.value = -q.value := by simp [neg,value]; ring
@[simp] lemma value_add (q r : RawRat) : (add q r).value=q.value+r.value := by
  simp only [add,value,product_denominator]
  push_cast
  have hq : (q.2.2:ℚ)+1≠0 := by positivity
  have hr : (r.2.2:ℚ)+1≠0 := by positivity
  field_simp
  ring
@[simp] lemma value_mul (q r : RawRat) : (mul q r).value=q.value*r.value := by
  simp only [mul,value,product_denominator]
  push_cast
  rw [← mul_div_mul_comm]
  congr 1
  ring
@[simp] lemma value_inv (q : RawRat) : q.inv.value=q.value⁻¹ := by
  unfold inv
  by_cases h : q.1=q.2.1
  · simp [h,value,ofNat]
  · simp only [h,ite_false]
    by_cases hlt : q.2.1<q.1
    · rw [ite_eq_left hlt]
      have hsub : 1≤q.1-q.2.1 := by omega
      have hd : (((q.1-q.2.1-1:ℕ):ℚ)+1)=(q.1:ℚ)-q.2.1 := by
        rw [Nat.cast_sub hsub,Nat.cast_sub (by omega : q.2.1≤q.1)]
        simp
      simp only [value,hd,Nat.cast_zero,sub_zero,Nat.cast_add,Nat.cast_one,inv_div]
    · rw [ite_eq_right hlt]
      have hsub : 1≤q.2.1-q.1 := by omega
      have hd : (((q.2.1-q.1-1:ℕ):ℚ)+1)=(q.2.1:ℚ)-q.1 := by
        rw [Nat.cast_sub hsub,Nat.cast_sub (by omega : q.1≤q.2.1)]
        simp
      simp only [value,hd,Nat.cast_zero,zero_sub,Nat.cast_add,Nat.cast_one,inv_div]
      rw [show (q.1:ℚ)-q.2.1=-((q.2.1:ℚ)-q.1) by ring, div_neg, neg_div]

lemma le_iff (q r : RawRat) : le q r ↔ q.value ≤ r.value := by
  unfold le value
  rw [div_le_div_iff₀ (by positivity : (0:ℚ)<q.2.2+1) (by positivity : (0:ℚ) < r.2.2+1)]
  have hc : q.1*(r.2.2+1)+r.2.1*(q.2.2+1) ≤ r.1*(q.2.2+1)+q.2.1*(r.2.2+1) ↔
      (q.1:ℚ)*(r.2.2+1)+(r.2.1:ℚ)*(q.2.2+1)≤(r.1:ℚ)*(q.2.2+1)+(q.2.1:ℚ)*(r.2.2+1) := by
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith
lemma lt_iff (q r : RawRat) : lt q r ↔ q.value < r.value := by
  unfold lt value
  rw [div_lt_div_iff₀ (by positivity : (0:ℚ)<q.2.2+1) (by positivity : (0:ℚ) < r.2.2+1)]
  have hc : q.1*(r.2.2+1)+r.2.1*(q.2.2+1) < r.1*(q.2.2+1)+q.2.1*(r.2.2+1) ↔
      (q.1:ℚ)*(r.2.2+1)+(r.2.1:ℚ)*(q.2.2+1)<(r.1:ℚ)*(q.2.2+1)+(q.2.1:ℚ)*(r.2.2+1) := by
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith

end RawRat

lemma choose_factorial (n k : ℕ) : n.choose k =
    if k≤n then n.factorial/(k.factorial*(n-k).factorial) else 0 := by
  by_cases h : k≤n
  · rw [ite_eq_left h]
    exact Nat.choose_eq_factorial_div_factorial h
  · rw [ite_eq_right h,Nat.choose_eq_zero_of_lt (by omega : n<k)]

lemma primrec_choose : Primrec₂ Nat.choose := by
  have h : Primrec (fun p : ℕ × ℕ=>if p.2≤p.1 then
      p.1.factorial/(p.2.factorial*(p.1-p.2).factorial) else 0) :=
    Primrec.ite (Primrec.nat_le.comp Primrec.snd Primrec.fst)
      (Primrec.nat_div.comp (primrec_factorial.comp Primrec.fst)
        (Primrec.nat_mul.comp (primrec_factorial.comp Primrec.snd)
          (primrec_factorial.comp Primrec.nat_sub))) (Primrec.const 0)
  exact h.to₂.of_eq (fun n k=>(choose_factorial n k).symm)

namespace RawRat

lemma primrec_ofNat : Primrec ofNat := Primrec.id.pair ((Primrec.const 0).pair (Primrec.const 0))
lemma primrec_neg : Primrec neg :=
  (Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))

lemma primrec_add : Primrec₂ add := by
  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp p d') (Primrec.nat_mul.comp p' d)).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp n d') (Primrec.nat_mul.comp n' d)).pair
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp d d') (Primrec.const 1)))).to₂

lemma primrec_mul : Primrec₂ mul := by
  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact ((Primrec.nat_add.comp (Primrec.nat_mul.comp p p') (Primrec.nat_mul.comp n n')).pair
    ((Primrec.nat_add.comp (Primrec.nat_mul.comp p n') (Primrec.nat_mul.comp n p')).pair
      (Primrec.nat_sub.comp (Primrec.nat_mul.comp d d') (Primrec.const 1)))).to₂

lemma primrec_inv : Primrec inv := by
  let p : Primrec (fun q : RawRat => q.1) := Primrec.fst
  let n : Primrec (fun q : RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let d : Primrec (fun q : RawRat => q.2.2+1) := Primrec.succ.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp p n) (Primrec.const (ofNat 0))
    (Primrec.ite (Primrec.nat_lt.comp n p)
      (d.pair ((Primrec.const 0).pair (Primrec.nat_sub.comp (Primrec.nat_sub.comp p n) (Primrec.const 1))))
      ((Primrec.const 0).pair (d.pair (Primrec.nat_sub.comp (Primrec.nat_sub.comp n p) (Primrec.const 1)))))

lemma primrec_le : PrimrecRel le := by

  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.nat_le.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p d') (Primrec.nat_mul.comp n' d))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p' d) (Primrec.nat_mul.comp n d'))

lemma primrec_lt : PrimrecRel lt := by
  let p : Primrec (fun q : RawRat × RawRat => q.1.1) := Primrec.fst.comp Primrec.fst
  let n : Primrec (fun q : RawRat × RawRat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  let d : Primrec (fun q : RawRat × RawRat => q.1.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  let p' : Primrec (fun q : RawRat × RawRat => q.2.1) := Primrec.fst.comp Primrec.snd
  let n' : Primrec (fun q : RawRat × RawRat => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  let d' : Primrec (fun q : RawRat × RawRat => q.2.2.2+1) := Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.nat_lt.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p d') (Primrec.nat_mul.comp n' d))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p' d) (Primrec.nat_mul.comp n d'))

def pow (q : RawRat) : ℕ → RawRat
  | 0 => ofNat 1
  | n+1 => mul (pow q n) q
@[simp] lemma value_pow (q : RawRat) (n : ℕ) : (pow q n).value=q.value^n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp only [pow,value_mul,ih,pow_succ]
lemma primrec_pow : Primrec₂ pow := by
  have h : Primrec₂ (fun q n => Nat.rec (motive:=fun _=>RawRat) (ofNat 1) (fun _ r=>mul r q) n) :=
    Primrec.nat_rec (Primrec.const (ofNat 1)) ((primrec_mul.comp (Primrec.snd.comp Primrec.snd) Primrec.fst).to₂)
  apply h.of_eq
  intro q n
  induction n with
  | zero => rfl
  | succ n ih => simp only [ih,pow]

def ceil (q : RawRat) : ℕ := (q.1-q.2.1+q.2.2)/(q.2.2+1)
lemma primrec_ceil : Primrec ceil :=
  Primrec.nat_div.comp
    (Primrec.nat_add.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd))
    (Primrec.succ.comp (Primrec.snd.comp Primrec.snd))

end RawRat
end MinUncut.Preprocess

namespace MinUncut.Preprocess.RawRat
lemma ceil_eq (q : RawRat) : q.ceil=⌈q.value⌉₊ := by
  apply Nat.le_antisymm
  · unfold ceil
    rw [Nat.div_le_iff_le_mul_add_pred (by omega : 0<q.2.2+1)]
    have h := Nat.le_ceil q.value
    rw [value,div_le_iff₀ (by positivity : (0:ℚ)<q.2.2+1)] at h
    change (q.1:ℚ)-q.2.1≤(⌈q.value⌉₊:ℚ)*(q.2.2+1) at h
    have hn : q.1-q.2.1≤(q.2.2+1)*⌈q.value⌉₊ := by
      by_cases hp : q.2.1≤q.1
      · have he : ((q.1-q.2.1:ℕ):ℚ)≤((q.2.2+1)*⌈q.value⌉₊:ℕ) := by
          rw [Nat.cast_sub hp]
          push_cast
          nlinarith
        exact_mod_cast he
      · have he : q.1-q.2.1=0 := by omega
        rw [he]; exact Nat.zero_le _
    omega
  · apply Nat.ceil_le.mpr
    rw [value,div_le_iff₀ (by positivity : (0:ℚ)<q.2.2+1)]
    have hm := Nat.mod_lt (q.1-q.2.1+q.2.2) (by omega : 0<q.2.2+1)
    have he := Nat.div_add_mod (q.1-q.2.1+q.2.2) (q.2.2+1)
    have hn : q.1-q.2.1≤(q.2.2+1)*q.ceil := by unfold ceil; omega
    have hh : (q.1:ℚ)-q.2.1≤(q.1-q.2.1:ℕ) := by
      by_cases hp : q.2.1≤q.1
      · rw [Nat.cast_sub hp]
      · have hq : q.1≤q.2.1 := by omega
        have hq' : (q.1:ℚ)≤q.2.1 := by exact_mod_cast hq
        exact le_trans (sub_nonpos.mpr hq') (by positivity)
    have hn' : ((q.1-q.2.1:ℕ):ℚ)≤((q.2.2+1)*q.ceil:ℕ) := by exact_mod_cast hn
    push_cast at hn'
    nlinarith

def represent (q : ℚ) : RawRat := (q.num.toNat,(-q.num).toNat,q.den-1)
@[simp] lemma value_represent (q : ℚ) : (represent q).value=q := by
  have hp : 1≤q.den := Rat.den_pos q
  have hd : ((q.den-1:ℕ):ℚ)+1=q.den := by rw [Nat.cast_sub hp]; simp
  unfold value represent
  dsimp only
  rw [hd]
  have hn : (q.num.toNat:ℚ)-(-q.num).toNat=q.num := by
    exact_mod_cast Int.toNat_sub_toNat_neg q.num
  rw [hn,Rat.num_div_den]
end MinUncut.Preprocess.RawRat

namespace MinUncut.Preprocess

lemma primrec_represent : Primrec RawRat.represent :=
  (primrec_intToNat.comp primrec_ratNum).pair
    ((primrec_intNegToNat.comp primrec_ratNum).pair
      (Primrec.nat_sub.comp primrec_ratDen (Primrec.const 1)))

open Encodable

attribute [local instance] OAI.MinUncut.Preprocess.instEncodableRat_solutions
def candidate (q : RawRat) (n : ℕ) : Option ℚ :=
  (decode n).filter (fun r=>decide (RawRat.le q (RawRat.represent r) ∧ RawRat.le (RawRat.represent r) q))

lemma candidate_eq {q : RawRat} {n : ℕ} {r : ℚ} (h : r ∈ candidate q n) : r=q.value := by
  have hh : RawRat.le q (RawRat.represent r) ∧ RawRat.le (RawRat.represent r) q := by
    cases hn : decode (α:=ℚ) n with
    | none => simp [candidate,hn] at h
    | some s =>
      have ht : s=r ∧ RawRat.le q (RawRat.represent r) ∧ RawRat.le (RawRat.represent r) q := by
        simpa [candidate,hn] using h
      exact ht.2
  have h₁ := (RawRat.le_iff q (RawRat.represent r)).mp hh.1
  have h₂ := (RawRat.le_iff (RawRat.represent r) q).mp hh.2
  simpa only [RawRat.value_represent] using le_antisymm h₂ h₁

lemma candidate_exists (q : RawRat) : ∃ n, q.value ∈ candidate q n := by
  refine ⟨encode q.value,?_⟩
  simp only [candidate,encodek,Option.filter_some,Option.mem_def]
  have h₁ : RawRat.le q (RawRat.represent q.value) := by
    rw [RawRat.le_iff,RawRat.value_represent]
  have h₂ : RawRat.le (RawRat.represent q.value) q := by
    rw [RawRat.le_iff,RawRat.value_represent]
  simp [h₁,h₂]

lemma candidate_primrec : Primrec₂ candidate := by
  have hc : PrimrecPred (fun p : RawRat × ℚ=> RawRat.le p.1 (RawRat.represent p.2) ∧
      RawRat.le (RawRat.represent p.2) p.1) :=
    (RawRat.primrec_le.comp Primrec.fst (primrec_represent.comp Primrec.snd)).and
      (RawRat.primrec_le.comp (primrec_represent.comp Primrec.snd) Primrec.fst)
  apply (Primrec.option_bind (Primrec.decode.comp Primrec.snd)
    (Primrec.ite (hc.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
      (Primrec.option_some.comp Primrec.snd) (Primrec.const none)).to₂).to₂.of_eq
  intro q n
  unfold candidate
  cases decode (α:=ℚ) n <;> simp [Option.filter]

lemma computable_value : Computable RawRat.value := by
  apply (Partrec.rfindOpt candidate_primrec.to_comp).of_eq
  intro q
  apply Part.eq_some_iff.mpr
  obtain ⟨n,hn⟩ := candidate_exists q
  have hd := Nat.rfindOpt_dom.mpr ⟨n,q.value,hn⟩
  obtain ⟨r,hr⟩ := Part.dom_iff_mem.mp hd
  obtain ⟨m,hm⟩ := Nat.rfindOpt_spec hr
  rw [candidate_eq hm] at hr
  exact hr

lemma computable_ratAdd : Computable₂ (fun q r : ℚ=>q+r) := by
  have h : Computable (fun p : ℚ × ℚ=>RawRat.add (RawRat.represent p.1) (RawRat.represent p.2)) :=
    RawRat.primrec_add.to_comp.comp (primrec_represent.to_comp.comp Computable.fst)
      (primrec_represent.to_comp.comp Computable.snd)
  exact (computable_value.comp h).of_eq (by intro p; simp only [RawRat.value_add,RawRat.value_represent])
lemma computable_ratMul : Computable₂ (fun q r : ℚ=>q*r) := by
  have h : Computable (fun p : ℚ × ℚ=>RawRat.mul (RawRat.represent p.1) (RawRat.represent p.2)) :=
    RawRat.primrec_mul.to_comp.comp (primrec_represent.to_comp.comp Computable.fst)
      (primrec_represent.to_comp.comp Computable.snd)
  exact (computable_value.comp h).of_eq (by intro p; simp only [RawRat.value_mul,RawRat.value_represent])
lemma computable_ratNeg : Computable (fun q : ℚ=>-q) := by
  exact (computable_value.comp (RawRat.primrec_neg.to_comp.comp primrec_represent.to_comp)).of_eq
    (by intro q; simp only [RawRat.value_neg,RawRat.value_represent])
lemma computable_ratInv : Computable (fun q : ℚ=>q⁻¹) := by
  exact (computable_value.comp (RawRat.primrec_inv.to_comp.comp primrec_represent.to_comp)).of_eq
    (by intro q; simp only [RawRat.value_inv,RawRat.value_represent])
lemma computable_ratSub : Computable₂ (fun q r : ℚ=>q-r) :=
  (computable_ratAdd.comp Computable.fst (computable_ratNeg.comp Computable.snd)).of_eq
    (by intro p; exact (sub_eq_add_neg p.1 p.2).symm)
lemma computable_ratDiv : Computable₂ (fun q r : ℚ=>q/r) :=
  (computable_ratMul.comp Computable.fst (computable_ratInv.comp Computable.snd)).of_eq
    (by intro p; exact (div_eq_mul_inv p.1 p.2).symm)
lemma computable_ratPow : Computable₂ (fun (q : ℚ) (n : ℕ)=>q^n) := by
  have h : Computable (fun p : ℚ × ℕ=>RawRat.pow (RawRat.represent p.1) p.2) :=
    RawRat.primrec_pow.to_comp.comp (primrec_represent.to_comp.comp Computable.fst) Computable.snd
  exact (computable_value.comp h).of_eq (by intro p; simp only [RawRat.value_pow,RawRat.value_represent])
lemma computable_ratNat : Computable (fun n : ℕ=>(n:ℚ)) :=
  (computable_value.comp RawRat.primrec_ofNat.to_comp).of_eq (by intro n; simp only [RawRat.value_nat])
lemma primrec_ratLe : PrimrecRel (fun q r : ℚ=>q ≤ r) :=
  (RawRat.primrec_le.comp (primrec_represent.comp Primrec.fst)
    (primrec_represent.comp Primrec.snd)).of_eq (by intro p; simp [RawRat.le_iff])
lemma primrec_ratLt : PrimrecRel (fun q r : ℚ=>q < r) :=
  (RawRat.primrec_lt.comp (primrec_represent.comp Primrec.fst)
    (primrec_represent.comp Primrec.snd)).of_eq (by intro p; simp [RawRat.lt_iff])
lemma primrec_ratCeil : Primrec (fun q : ℚ=>⌈q⌉₊) :=
  (RawRat.primrec_ceil.comp primrec_represent).of_eq (by intro q; rw [RawRat.ceil_eq,RawRat.value_represent])

end MinUncut.Preprocess

section
attribute [fun_prop] Computable ComputablePred

namespace MinUncut.Preprocess
variable {α : Type} [Primcodable α]

@[fun_prop] lemma ca_choose {f g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>(f x).choose (g x)) :=
  primrec_choose.to_comp.comp hf hg
@[fun_prop] lemma ca_ratCast {f : α → ℕ} (hf : Computable f) : Computable (fun x=>(f x:ℚ)) :=
  computable_ratNat.comp hf
@[fun_prop] lemma ca_ratAdd {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x+g x) := computable_ratAdd.comp hf hg
@[fun_prop] lemma ca_ratSub {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x-g x) := computable_ratSub.comp hf hg
@[fun_prop] lemma ca_ratMul {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x*g x) := computable_ratMul.comp hf hg
@[fun_prop] lemma ca_ratDiv {f g : α → ℚ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x/g x) := computable_ratDiv.comp hf hg
@[fun_prop] lemma ca_ratInv {f : α → ℚ} (hf : Computable f) : Computable (fun x=>(f x)⁻¹) := computable_ratInv.comp hf
@[fun_prop] lemma ca_ratPow {f : α → ℚ} {g : α → ℕ} (hf : Computable f) (hg : Computable g) : Computable (fun x=>f x^g x) := computable_ratPow.comp hf hg
@[fun_prop] lemma ca_ratCeil {f : α → ℚ} (hf : Computable f) : Computable (fun x=>⌈f x⌉₊) := primrec_ratCeil.to_comp.comp hf

@[fun_prop] lemma ca_ratLe {f g : α → ℚ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x≤g x) :=
  (primrec_ratLe.computablePred.decide.comp (hf.pair hg)).computablePred
@[fun_prop] lemma ca_ratLt {f g : α → ℚ} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun x=>f x<g x) :=
  (primrec_ratLt.computablePred.decide.comp (hf.pair hg)).computablePred

end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_GaussianSmallBall
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

open scoped BigOperators Topology
open MeasureTheory Set
namespace MinUncut.FiniteGaussian

open scoped BigOperators
open MeasureTheory

def midpoint (T : ℚ) (L i : ℕ) : ℚ := (endpoint T L i+endpoint T L (i+1))/2

def cellWeight (r : ℕ) (T : ℚ) (L : ℕ) (i : Fin L) : ℚ :=
  qIntegral r (endpoint T L i) (endpoint T L (i+1))/qIntegral r (-T) T

open scoped BigOperators
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.propDecidable

open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
attribute [local instance] Classical.propDecidable

open scoped BigOperators RealInnerProductSpace NNReal
open MeasureTheory ProbabilityTheory Set
open GaussianBudget
attribute [local instance] Classical.propDecidable

end MinUncut.FiniteGaussian

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Basic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
namespace MinUncut.GaussianHermite

variable {ι : Type*} [Fintype ι]

lemma continuous_psi (a : ι → ℕ) : Continuous (psi a) := by
  unfold psi H he
  fun_prop

end MinUncut.GaussianHermite
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Convolution
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology

namespace MinUncut.RowNoise
open BinaryFourier
variable {R W : Type*} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]
  [AddCommGroup W] [Module F₂ W]

def density (a : ℝ) (B C : R → W) : ℝ := ∏ r, rowDensity a (B r) (C r)

end MinUncut.RowNoise

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_HonestRows
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open BinaryFourier RowNoise GaussianBudget
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

def codeVector (z : Code m n) : Point m n → ℝ :=
  fun x => (Real.sqrt (n^m:ℕ))⁻¹ * BinaryFourier.sign (z.val x)

end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_LiteralGaussian
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

abbrev TestCoordinates (m n : ℕ) := Coordinates (Point m n) (Code m n)
abbrev ScoreIndex (m n : ℕ) := Bool × Code m n

def scoreFamily (σ η : ℝ) (s : ScoreIndex m n) : TestCoordinates m n → ℝ :=
  liftVector (codeVector s.2) (if s.1 then σ else 0) (if s.1 then η else 0) s.2

def qSign (b : F₂) : ℚ := if b=0 then 1 else -1

def rationalScoreTable (σ η : ℚ) (x : TestCoordinates m n → ℚ) (s : ScoreIndex m n) : Bool :=
  algebraicNonneg (∑ i, (x (.inl i)+(if s.1 then σ else 0)*x (.inr (.inl i)))*qSign (s.2.val i))
    ((if s.1 then η else 0)*x (.inr (.inr s.2))) (n^m)

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Analysis_FiniteGaussianLaw
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory
namespace MinUncut.FiniteGaussian
open GaussianBudget MinUncut.Inner
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}
local instance coordsDecEq (m n : ℕ) : DecidableEq (TestCoordinates m n) :=
  fun a b => Classical.propDecidable (a=b)

def tableGrid (m n : ℕ) (ε : ℚ) (hε : 0<ε) : GridData :=
  GridData.select (Fintype.card (TestCoordinates m n)) (Fintype.card (ScoreIndex m n))
    (2*(n^m:ℕ)+1) ε (by positivity) hε

def gridWeight (g : GridData) (j : TestCoordinates m n → Fin g.L) : ℚ :=
  ∏ i, cellWeight g.r g.T g.L (j i)

attribute [local irreducible] tableGrid scoreFamily

end MinUncut.FiniteGaussian

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeComputability
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed
open Turing.ToPartrec

theorem CodeRun.complete {c : Code} {v w : List ℕ} (h : w ∈ c.eval v) :
    ∃ t, CodeRun c v w t := by
  induction c generalizing v w with
  | zero' =>
    have hw : w=0::v := by simpa using h
    subst w
    exact ⟨_, .zero _⟩
  | succ =>
    have hw : w=[v.headI+1] := by simpa using h
    subst w
    exact ⟨_, .succ _⟩
  | tail =>
    have hw : w=v.tail := by simpa using h
    subst w
    exact ⟨_, .tail _⟩
  | cons f fs ih ih' =>
    rcases (Part.mem_bind_iff.mp h) with ⟨u,hu,hrest⟩
    rcases (Part.mem_bind_iff.mp hrest) with ⟨w',hw',hw⟩
    have he : w=u.headI::w' := by simpa using hw
    subst w
    obtain ⟨t,ht⟩ := ih hu
    obtain ⟨t',ht'⟩ := ih' hw'
    exact ⟨_, .cons ht ht'⟩
  | comp f g ih ih' =>
    obtain ⟨u,hu,hw⟩ := Part.mem_bind_iff.mp h
    obtain ⟨t,ht⟩ := ih' hu
    obtain ⟨t',ht'⟩ := ih hw
    exact ⟨_, .comp ht ht'⟩
  | case f g ih ih' =>
    cases v with
    | nil =>
      obtain ⟨t,ht⟩ := ih (by simpa using h)
      exact ⟨_, .caseZero rfl ht⟩
    | cons a v =>
      cases a with
      | zero =>
        obtain ⟨t,ht⟩ := ih (by simpa using h)
        exact ⟨_, .caseZero rfl ht⟩
      | succ a =>
        obtain ⟨t,ht⟩ := ih' (by simpa using h)
        exact ⟨_, .caseSucc ht⟩
  | fix f ih =>
    rw [Code.fix_eval] at h
    refine PFun.fixInduction' h ?_ ?_
    · intro v h
      obtain ⟨u,hu,he⟩ := (Part.mem_map_iff _).mp h
      by_cases hz : u.headI=0
      · rw [ite_eq_left hz] at he
        have he' : u.tail=w := Sum.inl.inj he
        subst w
        obtain ⟨t,ht⟩ := ih hu
        exact ⟨_, .fixDone ht hz⟩
      · rw [ite_eq_right hz] at he
        cases he
    · intro v u _ h hr
      obtain ⟨z,hz,he⟩ := (Part.mem_map_iff _).mp h
      by_cases hh : z.headI=0
      · rw [ite_eq_left hh] at he
        cases he
      · rw [ite_eq_right hh] at he
        have he' : z.tail=u := Sum.inr.inj he
        cases z with
        | nil => simp at hh
        | cons a z =>
          cases a with
          | zero => simp at hh
          | succ a =>
            simp only [List.tail_cons] at he'
            subst u
            obtain ⟨t,ht⟩ := ih hz
            obtain ⟨t',ht'⟩ := hr
            exact ⟨_, .fixMore ht ht'⟩

open _root_.Turing.PartrecToTM2 Turing.ToPartrec

lemma magnitude_length (v : List ℕ) : v.length≤ magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.length_cons,magnitude_cons]; omega

open Turing.ToPartrec

open Turing.ToPartrec

open Turing.ToPartrec

end MinUncut.Costed

noncomputable section
namespace MinUncut.Costed
open Turing.ToPartrec Polynomial

namespace PolyProgram
variable {f g : List ℕ → List ℕ}

def zero : PolyProgram (fun v=>0::v) where
  code := .zero'
  bound := X+1
  run v := (run_zero v).mono (by simp)
  size v := by simp; omega

open Turing.ToPartrec Polynomial

end PolyProgram
end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_PolynomialRecursor
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.PolyProgram
open Turing.ToPartrec Polynomial

def prec {f g : List ℕ → List ℕ} (F : PolyProgram f) (G : PolyProgram g)
    (p : Polynomial ℕ)
    (hs : ∀n v i,i≤n → scalarRec f g v i≤p.eval (magnitude (n::v))) :
    PolyProgram (fun v=>[scalarRec f g v.tail v.headI]) := by
  let F' := head.comp F
  let G' := head.comp G
  let P : PolyProgram (fun v=>v.headI::v.tail) := head.cons tail
  let W := X+1+p
  let B := F'.bound+(X+2)*(G'.bound.comp (C 3*W+3)+C 50000*(W+1))
  refine ⟨.comp (.prec F'.code G'.code) P.code,
    P.bound+B.comp P.bound+1+p.comp P.bound+1,?_,?_⟩
  · intro v
    let n := v.headI
    let u := v.tail
    let s := magnitude (n::u)
    let M := W.eval s
    have hn : n≤M := by simp [M,W,s,magnitude_cons]; omega
    have hu : magnitude u≤M := by simp [M,W,s,magnitude_cons]; omega
    have hr : ∀i≤n,scalarRec f g u i≤M := by
      intro i hi
      have h : scalarRec f g u i≤p.eval s := hs n u i hi
      simp only [M,W,eval_add,eval_X,eval_one]
      omega
    have hf : Runs F'.code u [scalarRec f g u 0] (F'.bound.eval s) :=
      (F'.run u).mono (evalNat_mono _ (by simp only [s,magnitude_cons]; omega))
    have hg : ∀i<n,Runs G'.code (i::scalarRec f g u i::u)
        [scalarRec f g u (i+1)] (G'.bound.eval (3*M+3)) := by
      intro i hi
      apply (G'.run _).mono
      apply evalNat_mono
      have h := hr i (by omega)
      simp only [magnitude_cons]; omega
    have hh := run_prec F'.code G'.code n (scalarRec f g u) u M
      (F'.bound.eval s) (G'.bound.eval (3*M+3)) hn hr hu hf hg
    have hh' : Runs (.prec F'.code G'.code) (n::u) [scalarRec f g u n] (B.eval s) := by
      apply hh.mono
      simp only [B,eval_add,eval_mul,eval_comp,eval_C,eval_X,eval_ofNat,eval_one]
      have hn' : n ≤ s := by simp only [s,magnitude_cons]; omega
      gcongr
    have hx := run_comp (P.run v) hh'
    apply hx.mono
    have hb := evalNat_mono B (P.size v)
    simp only [eval_add,eval_comp,eval_one]
    change B.eval s≤B.eval (P.bound.eval (magnitude v)) at hb
    omega
  · intro v
    have h := (hs v.headI v.tail v.headI le_rfl).trans
      (evalNat_mono p (P.size v))
    simp only [magnitude_cons,magnitude_nil,eval_add,eval_comp,eval_one]
    omega

end MinUncut.Costed.PolyProgram

end
namespace MinUncut.Costed

def Expr.or (a b : Expr) : Expr := .cond a b (.const 1)
def Expr.edge (u v a b : Expr) : Expr :=
  (Expr.mul (.eq u a) (.eq v b)).or (.mul (.eq u b) (.eq v a))

lemma Expr.eval_or (a b : Expr) (v : List ℕ) :
    (a.or b).eval v=if a.eval v=0 then b.eval v else 1 := rfl
lemma Expr.eval_cond (e a b : Expr) (v : List ℕ) :
    (Expr.cond e a b).eval v=if e.eval v=0 then a.eval v else b.eval v := rfl
lemma Expr.eval_add (a b : Expr) (v : List ℕ) :
    (Expr.add a b).eval v=a.eval v+b.eval v := rfl
lemma Expr.eval_mul (a b : Expr) (v : List ℕ) :
    (Expr.mul a b).eval v=a.eval v*b.eval v := rfl
lemma Expr.eval_reg (i : ℕ) (v : List ℕ) : (Expr.reg i).eval v=(v.drop i).headI := rfl
lemma Expr.eval_const (n : ℕ) (v : List ℕ) : (Expr.const n).eval v=n := rfl

lemma Expr.eval_or_le_one (a b : Expr) (v : List ℕ) (hb : b.eval v≤1) :
    (a.or b).eval v≤1 := by simp only [Expr.or,Expr.eval]; split_ifs <;> omega
lemma Expr.eval_edge_le_one (u v a b : Expr) (w : List ℕ) :
    (Expr.edge u v a b).eval w≤1 := by
  apply Expr.eval_or_le_one
  simp only [Expr.eval]
  split_ifs <;> omega

lemma Expr.eval_edge (u v a b : Expr) (w : List ℕ) :
    (Expr.edge u v a b).eval w=
      if (u.eval w=a.eval w ∧ v.eval w=b.eval w) ∨
         (u.eval w=b.eval w ∧ v.eval w=a.eval w) then 1 else 0 := by
  simp only [Expr.edge,Expr.or,Expr.eval]
  split_ifs <;> omega

end MinUncut.Costed

namespace MinUncut.Costed.Arena

open Turing.ToPartrec

lemma get_le_maximum (v : List ℕ) (a : Expr) (j : Fin 4) :
    (g a j).eval v≤ maximum v := by
  by_cases hz : a.eval v=0
  · simp only [g,readExpr,Expr.eval,hz,ite_true,show (1:ℕ)≠0 by omega,ite_false]
    exact Nat.zero_le _
  · simp only [g,readExpr,Expr.eval,hz,ite_false,ite_true]
    exact (head_le_maximum _).trans (maximum_drop v _)

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_SignedGraph
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.PathRealization
attribute [local instance] Classical.propDecidable

variable {V D : Type*}

def failure (e : Demand V) (s : V → Bool) : ℕ :=
  if (s e.left == s e.right) = e.equal then 0 else 1

end MinUncut.PathRealization

end
namespace MinUncut.FiniteProof

variable {Q : Type*} {A : Q → Type*} (base : ∀ q, A q)

def QueryDemand.signed (d : QueryDemand (A := A)) : PathRealization.Demand (Variable base) where
  left := vertex base d.left
  right := vertex base d.right
  equal := if d.equal then (d.left.2 (base d.left.1)==d.right.2 (base d.right.1))
    else !(d.left.2 (base d.left.1)==d.right.2 (base d.right.1))

end MinUncut.FiniteProof

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalPathGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open MinUncut.Costed.Expr

def demandOffset : Expr := .add (.const 11) (.add (.reg 8) (.mul (.const 3) (.reg 0)))
def demandLeft : Expr := .at demandOffset
def demandRight : Expr := .at (.add demandOffset (.const 1))
def demandEqual : Expr := .at (.add demandOffset (.const 2))
def privateBase : Expr := .add (.reg 2) (.mul (.const 3) (.reg 0))
def localEdge : Expr :=
  (Expr.edge (.reg 6) (.reg 7) demandLeft privateBase).or
  ((Expr.edge (.reg 6) (.reg 7) privateBase (.add privateBase (.const 1))).or
    (.cond demandEqual
      (Expr.edge (.reg 6) (.reg 7) (.add privateBase (.const 1)) demandRight)
      ((Expr.edge (.reg 6) (.reg 7) (.add privateBase (.const 1))
        (.add privateBase (.const 2))).or
       (Expr.edge (.reg 6) (.reg 7) (.add privateBase (.const 2)) demandRight))))
def accumulatedEdge : Expr := (Expr.reg 1).or localEdge

lemma localEdge_le_one (v : List ℕ) : localEdge.eval v≤1 := by
  apply Expr.eval_or_le_one
  apply Expr.eval_or_le_one
  simp only [Expr.eval]
  split_ifs
  · exact Expr.eval_edge_le_one ..
  · exact Expr.eval_or_le_one _ _ _ (Expr.eval_edge_le_one ..)

lemma accumulatedEdge_le_one (v : List ℕ) : accumulatedEdge.eval v≤1 :=
  Expr.eval_or_le_one _ _ _ (localEdge_le_one v)

open PolyProgram Polynomial

def cumulative (v : List ℕ) : ℕ → ℕ :=
  scalarRec (fun _=>[0]) (fun w=>[accumulatedEdge.eval w]) v

lemma cumulative_le_one (v : List ℕ) (n : ℕ) : cumulative v n≤1 := by
  cases n with
  | zero => simp only [cumulative,scalarRec,List.headI_cons]; omega
  | succ n => exact accumulatedEdge_le_one _

open PolyProgram Polynomial

def RenderState.tick (s : RenderState) : RenderState :=
  {s with row := if s.col=0 then s.row-1 else s.row
          col := if s.col=0 then s.V-1 else s.col-1
          q := s.q+1
          tape := cumulative s.encode s.M::s.tape}

def renderTick (v : List ℕ) : List ℕ := (parseState v).tick.encode

lemma renderTick_encode (s : RenderState) : renderTick s.encode=s.tick.encode := by
  simp only [renderTick,parse_encode]

def nextRow : Expr := .cond (.reg 5) (.sub (.reg 4) (.const 1)) (.reg 4)
def nextCol : Expr := .cond (.reg 5) (.sub (.reg 3) (.const 1)) (.sub (.reg 5) (.const 1))
def nextCount : Expr := .add (.reg 6) (.const 1)

noncomputable def normalizeProgram : PolyProgram (fun v=>(parseState v).encode) :=
  ((projection 0).cons ((projection 1).cons ((projection 2).cons ((projection 3).cons
    ((projection 4).cons ((projection 5).cons ((projection 6).cons (drop 7)))))))).ofEq (by intro v; rfl)

lemma parse_encode_magnitude (v : List ℕ) : magnitude (parseState v).encode≤8*magnitude v+7 := by
  have h (i : ℕ) := (magnitude_head (v.drop i)).trans (magnitude_drop i v)
  have h₀ := h 0; have h₁ := h 1; have h₂ := h 2; have h₃ := h 3
  have h₄ := h 4; have h₅ := h 5; have h₆ := h 6
  have ht := magnitude_drop 7 v
  simp only [parseState,RenderState.encode,magnitude_cons]
  simp only [List.drop_zero] at h₀
  omega

lemma tick_V (s : RenderState) : s.tick.V=s.V := rfl

lemma tick_magnitude (s : RenderState) :
    magnitude s.tick.encode≤ magnitude s.encode+s.V+3 := by
  have h := cumulative_le_one s.encode s.M
  simp only [RenderState.encode] at h
  have hr : (if s.col=0 then s.row-1 else s.row)≤ s.row := by split_ifs <;> omega
  have hc : (if s.col=0 then s.V-1 else s.col-1)≤ s.col+s.V := by split_ifs <;> omega
  simp only [RenderState.encode,RenderState.tick,magnitude_cons]
  omega

lemma tick_iter_V (n : ℕ) (s : RenderState) : (RenderState.tick^[n] s).V=s.V := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Function.iterate_succ_apply',tick_V] using ih

lemma tick_iter_magnitude (n : ℕ) (s : RenderState) :
    magnitude (RenderState.tick^[n] s).encode≤ magnitude s.encode+n*(s.V+3) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := tick_magnitude (RenderState.tick^[n] s)
    rw [tick_iter_V] at h
    simp only [Function.iterate_succ_apply']
    simp only [Nat.succ_mul] at *
    omega

lemma renderTick_iter_encode (n : ℕ) (s : RenderState) :
    renderTick^[n] s.encode=(RenderState.tick^[n] s).encode := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply',ih,renderTick_encode]

lemma renderTick_iter_succ (n : ℕ) (v : List ℕ) :
    renderTick^[n+1] v=(RenderState.tick^[n+1] (parseState v)).encode := by
  rw [Function.iterate_succ_apply,renderTick,renderTick_iter_encode,Function.iterate_succ_apply]

lemma renderTick_iter_bound (n : ℕ) (v : List ℕ) (i : ℕ) (hi : i≤n) :
    magnitude (renderTick^[i] v)≤(C 20*(X+1)^2:Polynomial ℕ).eval (magnitude (n::v)) := by
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one, magnitude_cons]
  let s := n+1+magnitude v+1
  have hs : 1≤ s := by dsimp [s]; omega
  have hm : magnitude v≤ s := by dsimp [s]; omega
  have hn : n≤ s := by dsimp [s]; omega
  have hsq : s≤ s^2 := Nat.le_self_pow (by omega) _
  cases i with
  | zero => simp only [Function.iterate_zero,Function.id_def]; nlinarith
  | succ i =>
    rw [renderTick_iter_succ]
    have h := tick_iter_magnitude (i+1) (parseState v)
    have h₀ := parse_encode_magnitude v
    have hv : (parseState v).V≤ magnitude v :=
      (magnitude_head (v.drop 3)).trans (magnitude_drop 3 v)
    have hprod : (i+1)*((parseState v).V+3)≤ s*(3*s) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hh : magnitude (RenderState.tick^[i+1] (parseState v)).encode≤8*s+7+3*s^2 := by
      nlinarith
    change _≤20*s^2
    nlinarith

open MinUncut.PathRealization
open PolyProgram

lemma localEdge_query (N M k V u v d a : ℕ) (acc data : List ℕ) :
    localEdge.eval (d::a::(queryState N M k V u v acc data).encode)=
      if rawLocal N d data u v then 1 else 0 := by
  have hL : demandLeft.eval (d::a::(queryState N M k V u v acc data).encode)=
      (data.drop (3*d)).headI := by
        simpa only [demandLeft,demandOffset,Expr.eval,queryState,RenderState.encode,
          List.drop_succ_cons,List.drop_zero,List.headI_cons,Nat.add_zero,Nat.add_assoc]
          using data_address N M k V u v d a 0 acc data
  have hR : demandRight.eval (d::a::(queryState N M k V u v acc data).encode)=
      (data.drop (3*d+1)).headI  := by
        simpa only [demandRight,demandOffset,Expr.eval,queryState,RenderState.encode,
          List.drop_succ_cons,List.drop_zero,List.headI_cons,Nat.add_assoc]
          using data_address N M k V u v d a 1 acc data
  have hE : demandEqual.eval (d::a::(queryState N M k V u v acc data).encode)=
      (data.drop (3*d+2)).headI  := by
        simpa only [demandEqual,demandOffset,Expr.eval,queryState,RenderState.encode,
          List.drop_succ_cons,List.drop_zero,List.headI_cons,Nat.add_assoc]
          using data_address N M k V u v d a 2 acc data
  simp only [localEdge,Expr.eval_or,Expr.eval_edge,Expr.eval_cond,hL,hR,hE]
  simp only [privateBase,Expr.eval_add,Expr.eval_mul,Expr.eval_const,Expr.eval_reg,
    queryState,RenderState.encode,List.drop_succ_cons,List.drop_zero,List.headI_cons]
  simp only [rawLocal,localAdj,endpoint]
  by_cases he : (data.drop (3*d+2)).headI=0 <;>
    simp only [he,ite_true,ite_false,bit_or]

lemma cumulative_query (N M k V u v n : ℕ) (acc data : List ℕ) :
    cumulative (queryState N M k V u v acc data).encode n=
      if ∃d<n,rawLocal N d data u v then 1 else 0 := by
  induction n with
  | zero => simp [cumulative,scalarRec]
  | succ n ih =>
    change (if cumulative (queryState N M k V u v acc data).encode n=0 then
      localEdge.eval (n::cumulative (queryState N M k V u v acc data).encode n::
        (queryState N M k V u v acc data).encode) else 1)=_
    rw [localEdge_query,ih,bit_or]
    congr 1
    apply propext
    constructor
    · rintro (⟨d,hd,h⟩|h)
      · exact ⟨d,by omega,h⟩
      · exact ⟨n,by omega,h⟩
    · rintro ⟨d,hd,h⟩
      by_cases he : d<n
      · exact Or.inl ⟨d,he,h⟩
      · have heq : d=n := by omega
        exact Or.inr (heq ▸ h)

def rawRow (N M : ℕ) (data : List ℕ) (u c : ℕ) : List ℕ :=
  (List.range c).map (rawCell N M data u)

def rawTable (N M : ℕ) (data : List ℕ) (r c : ℕ) : List ℕ :=
  (List.range r).flatMap (fun u=>rawRow N M data u c)

lemma tick_query (N M k V u v : ℕ) (acc data : List ℕ) :
    (queryState N M k V u v acc data).tick=
      queryState N M k V (if v=0 then u-1 else u) (if v=0 then V-1 else v-1)
        (rawCell N M data u v::acc) data := by
  simp only [RenderState.tick,cumulative_query]
  unfold queryState rawCell
  simp only [List.length_cons,List.cons_append]

lemma tick_row (N M k V r c : ℕ) (acc data : List ℕ) :
    RenderState.tick^[c+1] (queryState N M k V r c acc data)=
      queryState N M k V (r-1) (V-1) (rawRow N M data r (c+1)++acc) data := by
  induction c generalizing acc with
  | zero =>
    simp only [Nat.zero_add,Function.iterate_one,tick_query]
    simp [rawRow]
  | succ c ih =>
    rw [Function.iterate_succ_apply,tick_query]
    simp only [Nat.succ_ne_zero,ite_false,Nat.add_sub_cancel]
    rw [ih]
    simp only [rawRow,List.range_succ,List.map_append,List.map_cons,List.map_nil,List.append_assoc,List.cons_append,List.nil_append]

lemma tick_rows (N M k V r : ℕ) (hV : 0<V) (acc data : List ℕ) :
    RenderState.tick^[(r+1)*V] (queryState N M k V r (V-1) acc data)=
      queryState N M k V 0 (V-1) (rawTable N M data (r+1) V++acc) data := by
  have hV' : V-1+1=V := by omega
  have hrow (r : ℕ) (acc : List ℕ) :
      RenderState.tick^[V] (queryState N M k V r (V-1) acc data)=
        queryState N M k V (r-1) (V-1) (rawRow N M data r V++acc) data := by
    simpa only [hV'] using tick_row N M k V r (V-1) acc data
  induction r generalizing acc with
  | zero =>
    simpa only [Nat.zero_add,Nat.one_mul,Nat.zero_sub,rawTable,List.range_one,
      List.flatMap_cons,List.flatMap_nil,List.append_nil] using hrow 0 acc
  | succ r ih =>
    rw [show (r+1+1)*V=(r+1)*V+V by ring,Function.iterate_add_apply,hrow]
    simp only [Nat.add_sub_cancel]
    rw [ih]
    simp only [rawTable,List.range_succ,List.flatMap_append,
      List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

lemma tick_table (N M k V : ℕ) (acc data : List ℕ) :
    (RenderState.tick^[V^2] (queryState N M k V (V-1) (V-1) acc data)).tape=
      rawTable N M data V V++(acc++2::k::data) := by
  by_cases hV : V=0
  · subst V
    simp [rawTable,queryState]
  · have hp : 0<V := by omega
    have he : (V-1+1)*V=V^2 := by rw [Nat.sub_add_cancel hp]; ring
    rw [←he,tick_rows N M k V (V-1) hp,show V-1+1=V by omega]
    simp only [queryState,List.append_assoc]

end MinUncut.Costed.GraphRegisters

open scoped BigOperators
namespace MinUncut.PathRealization
open MinUncut.FiniteProof MinUncutGames.Foundations.Hastad.SourceOccurrences

def Demand.map {V W : Type*} (f : V → W) (d : Demand V) : Demand W :=
  ⟨f d.left,f d.right,d.equal⟩

end MinUncut.PathRealization

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_RawGraphEncoding
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.GraphRegisters
open MinUncut.PathRealization

lemma packed_addresses {N : ℕ} (ds : List (Demand (Fin N))) (d : ℕ) (hd : d<ds.length) :
    ((packDemands ds).drop (3*d)).headI=ds[d].left.val ∧
    ((packDemands ds).drop (3*d+1)).headI=ds[d].right.val ∧
    ((packDemands ds).drop (3*d+2)).headI=ds[d].equal.toNat := by
  induction ds generalizing d with
  | nil => simp at hd
  | cons e ds ih =>
    cases d with
    | zero => simp [packDemands,packDemand]
    | succ d =>
      have hh : d<ds.length := by simpa using hd
      simpa only [packDemands,List.flatMap_cons,packDemand,List.cons_append,List.nil_append,
        Nat.mul_add,Nat.mul_one,Nat.add_assoc,List.drop_succ_cons,List.getElem_cons_succ,
        Nat.succ_eq_add_one] using ih d hh

lemma rawLocal_pack {N : ℕ} (ds : List (Demand (Fin N))) (d : Fin ds.length) (u v : ℕ) :
    rawLocal N d.val (packDemands ds) u v=
      localAdj N d.val ds[d].left.val ds[d].right.val ds[d].equal.toNat u v := by
  obtain ⟨hL,hR,hE⟩ := packed_addresses ds d.val d.isLt
  simp only [rawLocal,hL,hR,hE,Fin.getElem_fin]

lemma rawCell_canonical {N : ℕ} (ds : List (Demand (Fin N))) (u v : Fin (N+ds.length*3)) :
    rawCell N ds.length (packDemands ds) u.val v.val=
      (canonicalAdjacent (fun d:Fin ds.length=>ds[d]) u v).toNat := by
  have he : (∃d<ds.length,rawLocal N d (packDemands ds) u.val v.val) ↔
      (∃d:Fin ds.length,∃j:Fin 4,j.val<(if ds[d].equal then 4 else 3) ∧
        ((u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
          v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2) ∨
         (v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
          u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2))) := by
    constructor
    · rintro ⟨d,hd,h⟩
      refine ⟨⟨d,hd⟩,(canonicalLocal_iff (fun d:Fin ds.length=>ds[d]) ⟨d,hd⟩ u v).mpr ?_⟩
      exact (rawLocal_pack ds ⟨d,hd⟩ u.val v.val).mp h
    · rintro ⟨d,h⟩
      refine ⟨d.val,d.isLt,?_⟩
      have hx := (canonicalLocal_iff (fun d:Fin ds.length=>ds[d]) d u v).mp h
      simpa only [←rawLocal_pack] using hx
  unfold rawCell canonicalAdjacent
  simp only [he]
  by_cases hh : ∃ d:Fin ds.length,∃j:Fin 4,j.val<(if ds[d].equal then 4 else 3) ∧
      ((u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
        v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2) ∨
       (v=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).1 ∧
        u=number N ds.length (ends (fun d:Fin ds.length=>ds[d]) (d,j)).2)) <;>
    simp only [hh,ite_true,ite_false,decide_true,decide_false,Bool.toNat_true,Bool.toNat_false]

end MinUncut.Costed.GraphRegisters

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CoupledAnswer
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local irreducible] query pullQuery
variable {m n : ℕ}
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def secondFailure (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) (p : (Point m n → ℝ) × (Code m n → ℝ)) : ℝ :=
  if f.answer (pullQuery B (c+σ•p.1) (η•p.2)) =
    f.answer (pullQuery C (c+σ•p.1) (η•p.2)) then 0 else 1

def secondRejection (f : FoldedProof A) (B C : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : ℝ :=
  ∫ p, secondFailure f B C σ η c p ∂(gauss (Point m n)).prod (gauss (Code m n))

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_ActualBoxBound
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

variable {m n : ℕ}
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators

namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]

def firstFailure (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c g : Point m n → ℝ) (l : Code m n → ℝ) : ℝ :=
  if f.answer (pullQuery B c 0) = f.answer (pullQuery B (c+σ•g) (η•l)) then 0 else 1

def firstRejection (f : FoldedProof A) (B : FaceArray A m n) (σ η : ℝ)
    (c : Point m n → ℝ) : ℝ :=
  ∫ g, ∫ l, firstFailure f B σ η c g l ∂gauss (Code m n) ∂gauss (Point m n)

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FirstError
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory Polynomial Filter
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory WithLp
open scoped BigOperators RealInnerProductSpace
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory GaussianHermite RowNoise
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
  {m n : ℕ}

def firstError (f : FoldedProof A) (σ η : ℝ) : ℝ :=
  𝔼 B : FaceArray A m n, ∫ c, firstRejection f B σ η c ∂gauss (Point m n)

def secondError (f : FoldedProof A) (a σ η : ℝ) : ℝ :=
  𝔼 B : FaceArray A m n, 𝔼 C : FaceArray A m n,
    RowNoise.density a B C*(∫ c, secondRejection f B C σ η c ∂gauss (Point m n))

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_Assembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox BoxGaussian
attribute [local instance] Classical.propDecidable
attribute [local irreducible] gradient selectedProject retainedClass Slice.centeredClip
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] classField pairSlice Slice.processed gaussianSlice
variable {V A : Type*} [AddCommGroup V] [Module F₂ V] [AddTorsor V A] [Fintype A]
variable {m n : ℕ}

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
attribute [local irreducible] oddAtom rowAtom pairAtomMean lowGradient
variable {Ξ : Type*} [Fintype Ξ] (V A : Ξ → Type*)
  [∀ ξ, AddCommGroup (V ξ)] [∀ ξ, Module F₂ (V ξ)] [∀ ξ, AddTorsor (V ξ) (A ξ)]
  [∀ ξ, Fintype (A ξ)] {m n : ℕ}

open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

def classTarget (T : ℝ) (m : ℕ) : ℝ := 1/(4*T*(Fintype.card (Option (PairClass m)):ℝ))

end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_InnerParameters
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Inner
open MeasureTheory ProbabilityTheory BinaryFourier RowNoise GaussianHermite Subbox

structure InnerParameters (J : ℝ) where
  s : ℕ
  m : ℕ
  k : ℕ
  n : ℕ
  H : ℕ
  A₀ : ℕ
  γ : ℚ
  p : ℚ
  θ : ℚ
  hm : 2 ≤ m
  hn : k+2 ≤ n
  hk : 1 ≤ k
  hs : ∀ t : ℕ, s+2 ≤ t → (t:ℝ)*(smoothingRho (sourceSigma J))^(2*t) ≤ 1/16
  hroom : sourceR J*m < (m-s).choose 2
  hH : 0 < H
  hA : 0 < A₀
  hγ : 0 < (γ:ℝ)
  hp : 0 < (p:ℝ)
  hp1 : (p:ℝ) < 1
  hθ : 0 < (θ:ℝ)
  hθ1 : (θ:ℝ) < 1
  hloc : (sourceSigma J)⁻¹*Real.sqrt (((s+sourceR J*m:ℕ):ℝ)*((k:ℝ)/((n:ℝ)-1))) <
    classTarget (sourceT J) m/10
  henergy : (sourceSigma J)⁻¹^2/(H:ℝ) < classTarget (sourceT J) m/10
  hclip : 2*((sourceSigma J)⁻¹^2)/(A₀:ℝ) < classTarget (sourceT J) m/10
  hcollision : 2*(A₀:ℝ)*((m:ℝ)/((k:ℝ)+1))^(((2^m:ℕ):ℝ)⁻¹) < classTarget (sourceT J) m/10
  hfourth : Real.sqrt ((H:ℝ)*((γ:ℝ)+(H:ℝ)^2/(A₀:ℝ))) < classTarget (sourceT J) m/10
  hatom : Real.sqrt ((sourceSigma J)⁻¹^2)*Real.sqrt
    (((4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ)*
      Real.sqrt ((θ:ℝ)^2+(m:ℝ)*(p:ℝ)*(n^m:ℕ)/(sourceSigma J)^2))/(γ:ℝ)) <
    classTarget (sourceT J) m/10

end MinUncut.Inner

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_OuterParameters
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner

structure OuterParameters (J : ℝ) (P : InnerParameters J) where
  u : ℚ
  b4 : ℚ
  k : ℕ
  t : ℕ
  hu : 0<(u:ℝ)
  hb4 : 0<(b4:ℝ)
  ht : 1≤t
  hk : k≤t
  hgap : listTerm (Real.sqrt (P.n^P.m:ℕ)/sourceSigma J) u P.θ
      (Fintype.card (Row P.m P.n)-1) k +
    (64/(P.θ^2*(sourceSigma J)^2))*J*b4 +
    remainderTerm (Real.sqrt (P.n^P.m:ℕ)/sourceSigma J) u P.θ
      (Fintype.card (Row P.m P.n)-1) k t < P.p

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_WeightedTestLaw
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] {m n k : ℕ}

abbrev OuterSample (I S : Type*) [Fintype I] (k : ℕ) :=
  FixedSets I k × (I → S) × (I → Fin 3)

def sampleHidden (o : OuterSample I S k) : I → Bool := hiddenSet o.1.val

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalBasics
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Inner
open scoped BigOperators
open GaussianHermite RowNoise

lemma pairClass_card_le (m : ℕ) : Fintype.card (Option (PairClass m)) ≤ m^2+1 := by
  have h := Fintype.card_le_of_injective (fun p : PairClass m => p.val) Subtype.val_injective
  simpa only [Fintype.card_option,Fintype.card_prod,Fintype.card_fin,pow_two] using Nat.add_le_add_right h 1

lemma row_card (m n : ℕ) : Fintype.card (Row m n)=m*n^(m-1) := by
  classical
  simp only [Row,Fintype.card_sigma,Fintype.card_fun,Fintype.card_fin]
  have he (i : Fin m) : Fintype.card {j : Fin m // j ≠ i}=m-1 := by
    rw [Fintype.card_subtype_compl]
    simp
  simp only [he,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
end MinUncut.Inner

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_RationalInner
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Inner
open GaussianHermite

namespace InnerData

lemma epsilon_le {J : ℕ} (hJ : 1 ≤ J) (m : ℕ) :
    (epsilon J m:ℝ) ≤ classTarget (sourceT J) m/10 := by
  have hT : (0:ℝ) < sourceT J := by exact_mod_cast sourceT_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  have hc := pairClass_card_le m
  have hc' : (Fintype.card (Option (PairClass m)):ℝ) ≤ (m:ℝ)^2+1 := by exact_mod_cast hc
  have hp : (0:ℝ) < Fintype.card (Option (PairClass m)) := by positivity
  unfold epsilon classTarget
  push_cast
  rw [rationalT_eq]
  calc
    _ ≤ 1/(40*(sourceT J:ℝ)*(Fintype.card (Option (PairClass m)):ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hc' (by positivity))
    _ = _ := by ring

lemma atomConstant_cast (s m n : ℕ) : (atomConstant s m n:ℝ)=
    (4:ℝ)^Fintype.card (Row m n)*((Fintype.card (Point m n)+s).choose s:ℝ) := by
  simp [atomConstant,Point]

def realize {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) (h : d.Check J) : InnerParameters J := by
  have hm := h.1
  have hn := h.2.1
  have hk := h.2.2.1
  have hH := h.2.2.2.1
  have hA := h.2.2.2.2.1
  have hγ := h.2.2.2.2.2.1
  have hp := h.2.2.2.2.2.2.1
  have hp1 := h.2.2.2.2.2.2.2.1
  have hθ := h.2.2.2.2.2.2.2.2.1
  have hθ1 := h.2.2.2.2.2.2.2.2.2.1
  have hstep := h.2.2.2.2.2.2.2.2.2.2.1
  have hbase := h.2.2.2.2.2.2.2.2.2.2.2.1
  have hroom := h.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hloc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have he := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hc := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hcol := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hfour := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hat := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hJr : (1:ℝ) ≤ J := by exact_mod_cast hJ
  have hσ := sourceSigma_pos hJr
  have hε := epsilon_pos hJ d.m
  have hb := epsilon_le hJ d.m
  have hγr : (0:ℝ) < d.γ := by exact_mod_cast hγ
  have hAr : (0:ℝ) < d.A := by exact_mod_cast hA
  have hn0 : (1:ℝ) < d.n := by exact_mod_cast (by omega : 1 < d.n)
  refine ⟨d.s,d.m,d.k,d.n,d.H,d.A,d.γ,d.p,d.θ,hm,hn,hk,?_,?_,hH,hA,hγr,
    by exact_mod_cast hp,by exact_mod_cast hp1,by exact_mod_cast hθ,by exact_mod_cast hθ1,
    ?_,?_,?_,?_,?_,?_⟩
  · have hs' : ((d.s:ℝ)+3)*(1+(sourceSigma J)^2)⁻¹ ≤ (d.s:ℝ)+2 := by
      simpa only [Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_inv,
        Rat.cast_one,Rat.cast_pow,rationalSigma_cast] using (Rat.cast_le.mpr hstep : (_:ℝ) ≤ _)
    have hb' : ((d.s:ℝ)+2)*((1+(sourceSigma J)^2)⁻¹)^(d.s+2) ≤ 1/16 := by
      simpa only [Rat.cast_mul,Rat.cast_add,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_inv,
        Rat.cast_one,Rat.cast_pow,Rat.cast_div,rationalSigma_cast] using (Rat.cast_le.mpr hbase : (_:ℝ) ≤ _)
    intro t ht
    rw [rho_even]
    exact cutoff_tail (by positivity) hs' hb' t ht
  · simpa only [rationalR_eq] using hroom
  · have hl : ((d.s+sourceR J*d.m:ℕ):ℝ)*((d.k:ℝ)/((d.n:ℝ)-1)) <
        ((epsilon J d.m:ℝ)*sourceSigma J)^2 := by
      have hh := (Rat.cast_lt.mpr hloc : (_:ℝ) < _)
      push_cast at hh
      simpa only [rationalSigma_cast,rationalR_eq,mul_div_assoc,Nat.cast_add,Nat.cast_mul] using hh
    have hh := (Real.sqrt_lt' (show 0 < (epsilon J d.m:ℝ)*sourceSigma J by positivity)).mpr hl
    apply lt_of_lt_of_le _ hb
    rw [mul_comm,← div_eq_mul_inv]
    exact (div_lt_iff₀ hσ).mpr hh
  · apply lt_of_lt_of_le _ hb
    simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_inv,Rat.cast_natCast,rationalSigma_cast]
      using (Rat.cast_lt.mpr he : (_:ℝ) < _)
  · apply lt_of_lt_of_le _ hb
    simpa only [Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_inv,Rat.cast_natCast,
      Rat.cast_ofNat,rationalSigma_cast] using (Rat.cast_lt.mpr hc : (_:ℝ) < _)
  · have hh : (d.m:ℝ)/((d.k:ℝ)+1) < ((epsilon J d.m:ℝ)/(2*(d.A:ℝ)))^(2^d.m) := by
      simpa only [Rat.cast_div,Rat.cast_add,Rat.cast_mul,Rat.cast_natCast,Rat.cast_pow,
        Rat.cast_one,Rat.cast_ofNat] using (Rat.cast_lt.mpr hcol : (_:ℝ) < _)
    have hr := (Real.rpow_inv_lt_iff_of_pos (by positivity : (0:ℝ) ≤ (d.m:ℝ)/((d.k:ℝ)+1))
      (by positivity : 0 ≤ (epsilon J d.m:ℝ)/(2*(d.A:ℝ))) (by positivity : (0:ℝ) < (2^d.m:ℕ))).mpr
      (by simpa only [Real.rpow_natCast] using hh)
    apply lt_of_lt_of_le _ hb
    simpa only [mul_comm] using (lt_div_iff₀ (show 0 < 2*(d.A:ℝ) by positivity)).mp hr
  · apply lt_of_lt_of_le ((Real.sqrt_lt' hε).mpr _) hb
    simpa only [Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_pow,Rat.cast_natCast]
      using (Rat.cast_lt.mpr hfour : (_:ℝ) < _)
  · have hC : 0 < (atomConstant d.s d.m d.n:ℝ) := by
      rw [atomConstant_cast]
      have hh : 0 < (Fintype.card (Point d.m d.n)+d.s).choose d.s := Nat.choose_pos (by omega)
      positivity
    have hh : (d.θ:ℝ)^2+(d.m:ℝ)*(d.p:ℝ)*(d.n^d.m:ℕ)/(sourceSigma J)^2 <
        ((epsilon J d.m:ℝ)^2*(sourceSigma J)^2*(d.γ:ℝ)/(atomConstant d.s d.m d.n:ℝ))^2 := by
      have hh := (Rat.cast_lt.mpr hat : (_:ℝ) < _)
      push_cast at hh
      simpa only [rationalSigma_cast,Nat.cast_pow] using hh
    apply lt_of_lt_of_le _ hb
    have h := nested_atom_lt hσ hε hγr hC hh
    simpa only [atomConstant_cast] using h
end InnerData
end MinUncut.Inner

end
section
namespace MinUncut.Outer
open MinUncut.Inner

namespace OuterData

@[simp] lemma hints_eq (d : InnerData) : hints d=Fintype.card (Row d.m d.n)-1 := by rw [hints,row_card]

lemma amplitude_ge {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) :
    Real.sqrt (d.n^d.m:ℕ)/sourceSigma J ≤ (amplitude J d:ℝ) := by
  have hσ := sourceSigma_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
  have hroot : Real.sqrt (d.n^d.m:ℕ) ≤ (d.n^d.m:ℕ)+1 := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hN := Nat.cast_nonneg (α := ℝ) (d.n^d.m)
      nlinarith
  unfold amplitude
  push_cast
  rw [rationalSigma_cast]
  apply div_le_div_of_nonneg_right _ hσ.le
  simpa only [Nat.cast_pow] using hroot

lemma listBound_cast (J : ℕ) (d : InnerData) (o : OuterData) :
    (listBound J d o:ℝ)=listTerm (amplitude J d) o.u d.θ (hints d) o.k := by
  unfold listBound listTerm
  push_cast
  rw [rate_cast]
  rw [← ceil_rat_real (amplitude J d^2/o.u^2),← ceil_rat_real (amplitude J d^2/d.θ^2)]
  push_cast
  rfl

def realize {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) (hd : d.Check J)
    (o : OuterData) (ho : o.Check J d) : OuterParameters J (d.realize hJ hd) := by
  have hu := ho.1
  have hb := ho.2.1
  have hv := ho.2.2.1
  have ht := ho.2.2.2.1
  have hk := ho.2.2.2.2.1
  have hl := ho.2.2.2.2.2.1
  have hbud := ho.2.2.2.2.2.2.1
  have hrad := ho.2.2.2.2.2.2.2.1
  have hrem := ho.2.2.2.2.2.2.2.2
  have hu' : (0:ℝ) < o.u := by exact_mod_cast hu
  have hb' : (0:ℝ) < o.b4 := by exact_mod_cast hb
  have hv' : (0:ℝ) < o.v := by exact_mod_cast hv
  let P := d.realize hJ hd
  have hθ := P.hθ
  have hM : (0:ℝ) ≤ Real.sqrt (d.n^d.m:ℕ)/sourceSigma J := by
    have := sourceSigma_pos (by exact_mod_cast hJ : (1:ℝ) ≤ J)
    positivity
  have hm := amplitude_ge hJ d
  have hL : listTerm (amplitude J d) o.u d.θ (hints d) o.k < (d.p:ℝ)/4 := by
    rw [← listBound_cast]
    exact_mod_cast hl
  have hB : (64/((d.θ:ℝ)^2*(sourceSigma J)^2))*(J:ℝ)*(o.b4:ℝ) < (d.p:ℝ)/4 := by
    have h := (Rat.cast_lt.mpr hbud : (_:ℝ) < _)
    push_cast at h
    simpa only [rationalSigma_cast] using h
  have hRad : Real.sqrt (((2:ℝ)^(4*(hints d+3)*o.k)-1)*(o.k:ℝ)^2/(o.t:ℝ)) < (o.v:ℝ) := by
    apply (Real.sqrt_lt' hv').mpr
    have h := (Rat.cast_lt.mpr hrad : (_:ℝ) < _)
    simpa only [radicand,Rat.cast_div,Rat.cast_mul,Rat.cast_sub,Rat.cast_pow,
      Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one] using h
  have hR : remainderTerm (amplitude J d) o.u d.θ (hints d) o.k o.t < (d.p:ℝ)/2 := by
    have h := (Rat.cast_lt.mpr hrem : (_:ℝ) < _)
    push_cast at h
    apply lt_of_le_of_lt _ h
    unfold remainderTerm
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add le_rfl
    exact mul_le_mul_of_nonneg_right hRad.le (by positivity)
  have hL' := (listTerm_mono hM hm (hints d) o.k).trans_lt hL
  have hR' := (remainderTerm_mono hM hm hu' (hints d) o.k o.t).trans_lt hR
  refine ⟨o.u,o.b4,o.k,o.t,hu',hb',ht,hk,?_⟩
  change listTerm (Real.sqrt (d.n^d.m:ℕ)/sourceSigma J) o.u d.θ
    (Fintype.card (Row d.m d.n)-1) o.k +
    (64/((d.θ:ℝ)^2*(sourceSigma J)^2))*(J:ℝ)*o.b4 +
    remainderTerm (Real.sqrt (d.n^d.m:ℕ)/sourceSigma J) o.u d.θ
      (Fintype.card (Row d.m d.n)-1) o.k o.t < d.p
  rw [← hints_eq]
  linarith
end OuterData
end MinUncut.Outer

end
section
namespace MinUncut.Outer.OuterData
open MinUncut.Inner

lemma check_exists {J : ℕ} (hJ : 1 ≤ J) (d : InnerData) (hd : d.Check J) :
    ∃ o : OuterData, o.Check J d := by
  have hJq : (1:ℚ) ≤ J := by exact_mod_cast hJ
  have hJ0 : (0:ℚ) < J := by linarith
  have hσ : 0 < rationalSigma J := by unfold rationalSigma; positivity
  have hp : 0 < d.p := by
    have hh : (0:ℝ) < d.p := (d.realize hJ hd).hp
    exact_mod_cast hh
  have hθ : 0 < d.θ := by
    have hh : (0:ℝ) < d.θ := (d.realize hJ hd).hθ
    exact_mod_cast hh
  let M : ℚ := amplitude J d
  let C : ℚ := 256/d.θ^4
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨u,hu,hub⟩ := exists_between (show (0:ℚ) < min 1 (d.p/(8*C*(M^2+1))) by positivity)
  obtain ⟨hu1,huB⟩ := lt_min_iff.mp hub
  have hsmall : C*u^2*M^2 < d.p/8 := by
    have hb := (lt_div_iff₀ (show (0:ℚ) < 8*C*(M^2+1) by positivity)).mp huB
    have hs : u^2 ≤ u := by nlinarith
    have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ C*M^2 by positivity)
    nlinarith
  let R : ℚ := (M+M^2/u)^4
  have hR : 0 ≤ R := by dsimp [R]; positivity
  obtain ⟨v,hv,hvB⟩ := exists_between (show (0:ℚ) < d.p/(8*C*(R+1)) by positivity)
  have hlarge : C*v*R < d.p/8 := by
    have hx := (lt_div_iff₀ (show 0 < 8*C*(R+1) by positivity)).mp hvB
    nlinarith
  obtain ⟨b,hb,hbB⟩ := exists_between (show (0:ℚ) < d.p*d.θ^2*(rationalSigma J)^2/(256*J) by positivity)
  have hbudget : (64/(d.θ^2*(rationalSigma J)^2))*(J:ℚ)*b < d.p/4 := by
    have hx := (lt_div_iff₀ (show (0:ℚ) < 256*J by positivity)).mp hbB
    have he : (64/(d.θ^2*(rationalSigma J)^2))*(J:ℚ)*b = (64*J*b)/(d.θ^2*(rationalSigma J)^2) := by ring
    rw [he]
    apply (div_lt_iff₀ (show 0 < d.θ^2*(rationalSigma J)^2 by positivity)).mpr
    nlinarith
  obtain ⟨k,hk⟩ := exists_list_scale (M:ℝ) u d.θ (hints d)
    (show (0:ℝ) < (d.p:ℝ)/4 by exact_mod_cast (show (0:ℚ) < d.p/4 by positivity))
  let B : ℚ := ((2:ℚ)^(4*(hints d+3)*k)-1)*(k:ℚ)^2
  obtain ⟨t,ht⟩ := exists_nat_gt (max (k+1:ℚ) (B/v^2))
  have htk : (k:ℚ)+1 < t := lt_of_le_of_lt (le_max_left _ _) ht
  have ht0 : (0:ℚ) < t := by have := Nat.cast_nonneg (α := ℚ) k; linarith
  have hrad : B/(t:ℚ) < v^2 := by
    apply (div_lt_iff₀ ht0).mpr
    have hx := (div_lt_iff₀ (show 0 < v^2 by positivity)).mp (lt_of_le_of_lt (le_max_right _ _) ht)
    nlinarith
  let o : OuterData := ⟨u,b,v,k,t⟩
  refine ⟨o,hu,hb,hv,by exact_mod_cast (show (1:ℚ) ≤ t by have := Nat.cast_nonneg (α := ℚ) k; linarith),
    by exact_mod_cast (show (k:ℚ) ≤ t by linarith),?_,hbudget,hrad,?_⟩
  · apply (Rat.cast_lt (K := ℝ)).mp
    rw [listBound_cast]
    simpa only [Rat.cast_div,Rat.cast_ofNat] using hk
  · change C*(u^2*M^2+v*R) < d.p/2
    nlinarith

end MinUncut.Outer.OuterData

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerCost
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S]

def rationalRate (J : ℕ) (d : InnerData) : ℚ := (rationalEta J)^2/d.m

end MinUncut.Outer

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_FiniteAlphabetBounds
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteProof
attribute [local instance] Classical.propDecidable
variable {Name I : Type*} [Fintype I]

def faceCardBound (t m n : ℕ) := (2^(2^(3*t)))^Fintype.card (Row m n)

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_SamplerAssembly
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer
open MinUncut.Inner MinUncut.FiniteGaussian MinUncut.FiniteProof OuterSmoothness
attribute [local instance] Classical.propDecidable coordsDecEq
variable {Name I S : Type*} [Fintype I] [Fintype S] [Nonempty S]

structure Parameters (J : ℕ) where
  hJ : 1≤J
  d : InnerData
  hd : d.Check J
  o : OuterData
  ho : o.Check J d

end MinUncut.Outer

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_Runtime
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineComposition

theorem liftSuccessfulTrace {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    (n : Nat) (start finish : σ)
    (trace : (advance source)^[n] (some start) = some finish) :
    (advance target)^[n] (some (embed start)) = some (embed finish) := by
  induction n generalizing start with
  | zero =>
      have same := Option.some.inj trace
      cases same
      rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply] at trace ⊢
      change (advance source)^[n] (source start) = some finish at trace
      change (advance target)^[n] (target (embed start)) = some (embed finish)
      cases firstStep : source start with
      | none =>
          rw [firstStep, advance_iterate_none] at trace
          contradiction
      | some intermediate =>
          rw [firstStep] at trace
          rw [simulation start intermediate firstStep]
          exact ih intermediate trace

def liftExecutionInTime {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    StateTransition.EvalsToInTime target (embed start) (some (embed finish)) budget where
  steps := execution.steps
  evals_in_steps := by
    have sourceTrace := execution.evals_in_steps
    change (advance source)^[execution.steps] (some start) = some finish at sourceTrace
    change (advance target)^[execution.steps] (some (embed start)) = some (embed finish)
    exact liftSuccessfulTrace source target embed simulation execution.steps start finish sourceTrace
  steps_le_m := execution.steps_le_m

@[simp] theorem liftExecutionInTime_steps {σ τ : Type} (source : σ → Option σ)
    (target : τ → Option τ) (embed : σ → τ)
    (simulation : ∀ a b, source a = some b → target (embed a) = some (embed b))
    {start finish : σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime source start (some finish) budget) :
    (liftExecutionInTime source target embed simulation execution).steps = execution.steps := rfl

def embeddedExecution {K E Λ Λextra σ τ : Type} {Γ : K → Type} {Δ : E → Type}
    [DecidableEq K] [DecidableEq E]
    (haltTarget : Option (Λ ⊕ Λextra)) (extraState : τ)
    (extraTapes : ∀ e, List (Δ e))
    (source : Λ → Turing.TM2.Stmt Γ Λ σ)
    (extra : Λextra → Turing.TM2.Stmt (MachineEmbedding.Alphabet Γ Δ)
      (Λ ⊕ Λextra) (σ × τ))
    {start finish : Turing.TM2.Cfg Γ Λ σ} {budget : Nat}
    (execution : StateTransition.EvalsToInTime (Turing.TM2.step source)
      start (some finish) budget) :
    StateTransition.EvalsToInTime (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
      (MachineEmbedding.configuration haltTarget extraState extraTapes start)
      (some (MachineEmbedding.configuration haltTarget extraState extraTapes finish)) budget :=
  liftExecutionInTime (Turing.TM2.step source)
    (Turing.TM2.step (MachineEmbedding.program haltTarget source extra))
    (MachineEmbedding.configuration haltTarget extraState extraTapes)
    (MachineEmbedding.step_simulation haltTarget extraState extraTapes source extra) execution

end MinUncutGames.Foundations.Complexity.MachineComposition

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineSubroutine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineStateFrame

open _root_.Turing

variable {K Λ Λ' σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem frame_advance (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (c : Option (TM2.Cfg Γ Λ σ)) :
    MachineComposition.advance (TM2.step (frameProgram source))
        (c.map (frameConfiguration ambient)) =
      (MachineComposition.advance (TM2.step source) c).map (frameConfiguration ambient) := by
  cases c with
  | none => rfl
  | some c => exact frame_step source ambient c

theorem frame_iterate (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    (steps : ℕ) (c : Option (TM2.Cfg Γ Λ σ)) :
    (MachineComposition.advance (TM2.step (frameProgram source)))^[steps]
        (c.map (frameConfiguration ambient)) =
      ((MachineComposition.advance (TM2.step source))^[steps] c).map
        (frameConfiguration ambient) := by
  induction steps with
  | zero => rfl
  | succ steps ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    exact frame_advance source ambient _

def frameExecution (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    StateTransition.EvalsToInTime (TM2.step (frameProgram source))
      (frameConfiguration ambient start) (finish.map (frameConfiguration ambient)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (TM2.step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (TM2.step (frameProgram source)))^[run.steps]
      ((some start).map (frameConfiguration ambient)) = finish.map (frameConfiguration ambient)
    rw [frame_iterate, h]
  steps_le_m := run.steps_le_m

@[simp] theorem frameExecution_steps (source : Λ → TM2.Stmt Γ Λ σ) (ambient : τ)
    {start : TM2.Cfg Γ Λ σ} {finish : Option (TM2.Cfg Γ Λ σ)} {budget : ℕ}
    (run : StateTransition.EvalsToInTime (TM2.step source) start finish budget) :
    (frameExecution source ambient run).steps = run.steps := rfl

end MinUncutGames.Foundations.Complexity.MachineStateFrame

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineCompare
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncutGames.Foundations.Complexity.MachineFieldProfile

open _root_.Turing

section Transport
variable {K Λ σ τ : Type} [DecidableEq K]

def copyStateEquiv (σ : Type) :
    ((σ × Bool × Option Bool) × Option Bool) ≃ MachineCompare.State σ where
  toFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  invFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def copyStatement (q : TM2.Stmt (fun _ : K => Bool) Λ
    ((σ × Bool × Option Bool) × Option Bool)) :
    TM2.Stmt (fun _ : K => Bool) Λ (MachineCompare.State σ) :=
  MachineControl.statement id (copyStateEquiv σ) q

end Transport

end MinUncutGames.Foundations.Complexity.MachineFieldProfile

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineSubstitution
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineSequential

open _root_.Turing

theorem firstTransfer_tapes (first second : FinTM2)
    (relabel : first.Γ first.k₁ → second.Γ second.k₀)
    (word : List (first.Γ first.k₁)) :
    Reduction.MachineTransfer.tapesAt (.inl first.k₁) (.inr (.inr ()))
      (firstConfiguration first second (haltList first word)).stk [] (word.reverse.map relabel) =
        temporaryTapes first second (word.reverse.map relabel) := by
  funext k
  rcases k with k | k | k
  · by_cases h : k = first.k₁
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
        MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes,
        haltList, h]
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, firstConfiguration,
      MachineControl.configuration, MachineEmbedding.configuration, MachineEmbedding.tapes]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, temporaryTapes]

theorem secondTransfer_tapes (first second : FinTM2) (word : List (second.Γ second.k₀)) :
    Reduction.MachineTransfer.tapesAt (Γ := Symbols first second)
      (.inr (.inr ())) (.inr (.inl second.k₀))
      (temporaryTapes first second word) [] word.reverse =
        (secondConfiguration first second (initList second word.reverse)).stk := by
  funext k
  rcases k with k | k | k
  · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]
  · by_cases h : k = second.k₀
    · subst k
      simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList]
    · simp [Reduction.MachineTransfer.tapesAt, temporaryTapes, secondConfiguration,
        MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
        MachineEmbedding.configuration, MachineEmbedding.tapes, initList, h]
  · cases k
    simp [Reduction.MachineTransfer.tapesAt, secondConfiguration,
      MachineControl.configuration, MachineStackSwap.configuration, MachineStackSwap.tapes,
      MachineEmbedding.configuration, MachineEmbedding.tapes]

end MinUncutGames.Foundations.Complexity.MachineSequential

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_RuntimeModel2
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.RuntimeModel

open _root_.Turing
open MinUncutGames.Foundations.Complexity

def compareEquiv (q : Nat) : State q ≃
    MachineCompare.State (GenericGraphTables.RelationTable q × Bool) where
  toFun s := ((s.1.2, s.1.1.1), s.1.1.2.1, s.1.1.2.2, s.2)
  invFun s := (((s.1.2, s.2.1, s.2.2.1), s.1.1), s.2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem compareEquiv_normal {q : Nat}
    (relation : GenericGraphTables.RelationTable q) (selfLoop : Bool) :
    compareEquiv q (normal relation selfLoop) =
      ((relation, selfLoop), false, none, none) := rfl

def emitterEquiv (q : Nat) : ((Ambient q × Unit) × Option Bool) ≃ State q where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv s := by rcases s with ⟨⟨s, u⟩, r⟩; cases u; rfl
  right_inv _ := rfl

variable {Λ : Type} {q : Nat}

def compareStatement (stmt : TM2.Stmt Alphabet Λ
    (MachineCompare.State (GenericGraphTables.RelationTable q × Bool))) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (compareEquiv q).symm stmt

def emitterStatement (stmt : TM2.Stmt Alphabet Λ ((Ambient q × Unit) × Option Bool)) :
    TM2.Stmt Alphabet Λ (State q) :=
  MachineControl.statement id (emitterEquiv q) stmt

def storeLoop (value : Bool) (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .load (fun state => (((value, false, none), state.1.2), none)) (.goto fun _ => next)

def nextRow (next : Λ) : TM2.Stmt Alphabet Λ (State q) :=
  .push .edge (fun _ => true)
    (.load (fun state => (state.1, none)) (.goto fun _ => next))

end MinUncutGames.Foundations.PCP.AlphabetTable.RuntimeModel

end
section
namespace MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

open _root_.Turing
open MinUncutGames.Foundations.Complexity
open RuntimeModel

variable {q : Nat} {Λ : Type}

def statement (labels : Label → Λ) (next : Λ) :
    Label → TM2.Stmt Alphabet Λ (State q)
  | .leftFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .tail .scratch id false
        (labels .leftFirst) (some (labels .leftSecond))))
  | .leftSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .tail .compareLeft false
        (labels .leftSecond) (some (labels .rightFirst))))
  | .rightFirst => compareStatement (MachineFieldProfile.copyStatement
      (Reduction.MachineTransfer.loopAt .head .scratch id false
        (labels .rightFirst) (some (labels .rightSecond))))
  | .rightSecond => compareStatement (MachineFieldProfile.copyStatement
      (MachineCopy.forkLoop .scratch .head .compareRight false
        (labels .rightSecond) (some (labels .compare))))
  | .compare => compareStatement (MachineCompare.loop .compareLeft .compareRight
      (labels .compare) (some (labels .equalStore)) (some (labels .differentStore)))
  | .equalStore => storeLoop true next
  | .differentStore => storeLoop false next

end MinUncutGames.Foundations.PCP.AlphabetTable.CompareLoop

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineFiniteAlphabet
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineStateEquiv

open Turing.TM2

variable {K Λ σ τ : Type} {Γ : K → Type}

variable [DecidableEq K]

theorem advance_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    (c : Option (Cfg Γ Λ σ)) :
    MachineComposition.advance (step (program e source)) (c.map (configuration e)) =
      (MachineComposition.advance (step source) c).map (configuration e) := by
  cases c with
  | none => rfl
  | some c => exact step_transport e source c

theorem iterate_transport (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ) (n : Nat)
    (c : Option (Cfg Γ Λ σ)) :
    (MachineComposition.advance (step (program e source)))^[n]
        (c.map (configuration e)) =
      ((MachineComposition.advance (step source))^[n] c).map (configuration e) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, advance_transport,
        Function.iterate_succ_apply']

def execution (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    StateTransition.EvalsToInTime (step (program e source))
      (configuration e start) (finish.map (configuration e)) budget where
  steps := run.steps
  evals_in_steps := by
    have h := run.evals_in_steps
    change (MachineComposition.advance (step source))^[run.steps] (some start) = finish at h
    change (MachineComposition.advance (step (program e source)))^[run.steps]
      ((some start).map (configuration e)) = finish.map (configuration e)
    rw [iterate_transport, h]
  steps_le_m := run.steps_le_m

@[simp] theorem execution_steps (e : σ ≃ τ) (source : Λ → Stmt Γ Λ σ)
    {start : Cfg Γ Λ σ} {finish : Option (Cfg Γ Λ σ)} {budget : Nat}
    (run : StateTransition.EvalsToInTime (step source) start finish budget) :
    (execution e source run).steps = run.steps := rfl

end MinUncutGames.Foundations.Complexity.MachineStateEquiv

end
section
namespace MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

open _root_.Turing
open MachineComposition

variable {K Λ A : Type} [DecidableEq K]

def compareStateEquiv (A : Type) : MachineCompare.State A ≃ State A where
  toFun s := ((s.1, s.2.1, s.2.2.1), s.2.2.2)
  invFun s := (s.1.1, s.1.2.1, s.1.2.2, s.2)
  left_inv := by rintro ⟨a, b, c, d⟩; rfl
  right_inv := by rintro ⟨⟨a, b, c⟩, d⟩; rfl

end MinUncutGames.Foundations.Complexity.MachineUnaryEqualityBit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_MachineRegularTableRuntime
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.MachineTableSplit

open _root_.Turing MachineComposition


def tapes (original work vertices darts : List Bool) : Tape → List Bool :=
  fun k => if k = 0 then original else if k = 1 then work
    else if k = 3 then vertices else if k = 4 then darts else []

end MinUncutGames.Foundations.Complexity.MachineTableSplit

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_PCP_RawInitialTables
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncutGames.Foundations.PCP.VerifierToCNF

open Target

def liftLiteral {q : Nat} (V : FiniteVerifier q) (l : Literal V.«variables») :
    Literal (outputVariables V) := ⟨oldIndex V l.variableIndex, l.positive⟩

def forbiddenLiteral {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) (i : Fin q) : Literal V.«variables» :=
  ⟨V.query e i, !(patternAt q p i)⟩

def forbiddenClause {q : Nat} (V : FiniteVerifier q) (e : Fin V.events)
    (p : PatternIndex q) : List (Literal (outputVariables V)) :=
  List.ofFn (fun i => liftLiteral V (forbiddenLiteral V e p i))

end MinUncutGames.Foundations.PCP.VerifierToCNF

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Encoding_SignatureEncoding
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Outer.LocalTemplate
open MinUncut.Inner MinUncut.Costed
open MinUncutGames.Foundations.Hastad.SourceOccurrences

lemma bool_code (b : Bool) : (Encoding.bool.code b).val=b.toNat := by cases b <;> rfl

end MinUncut.Outer.LocalTemplate

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_TemplateArithmetic
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction.CloneGap
open MinUncut.Costed
open scoped BigOperators

def inputTuple (F : Formula) {u : ℕ} (c : ClauseContext F u) : List ℕ :=
  ((clauseEncoding F u).code c).val::Complexity.formulaWords F

end MinUncut.SourceTemplate

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Games_QuestionExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction

variable {t : ℕ}

def tupleDigit (j : ℕ) : AExpr := .mod (.div (.reg 0) ((AExpr.reg 2).pow j)) (.reg 2)
def slotExpr (j p : ℕ) : AExpr := .at (.add (.add (.const 3) (.mul (.const 4) (tupleDigit j))) (.const p))

def equationExpr (j : ℕ) : AExpr := .add (slotExpr j 3) (.mul (.const 2)
  (AExpr.sum (List.ofFn (fun p : Fin 3=>.mul (slotExpr j p.val) ((AExpr.reg 1).pow p.val)))))

def firstExpr (t : ℕ) : AExpr := AExpr.sum (List.ofFn (fun i : Fin t=>
  .mul (equationExpr i.val) ((AExpr.mul ((AExpr.reg 1).pow 3) (.const 2)).pow i.val)))

def secondExpr {t : ℕ} (h : Fin t → Bool) (pos : Fin t → Fin 3) : AExpr :=
  AExpr.sum (List.ofFn (fun i : Fin t=>
    .mul (if h i then slotExpr i.val (pos i).val else .add (.reg 1) (equationExpr i.val))
      ((AExpr.add (.reg 1) (.mul ((AExpr.reg 1).pow 3) (.const 2))).pow i.val)))

end MinUncut.Costed.SourceWords

end
end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ParameterFields
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian
def innerDataEquiv : InnerData ≃ InnerDataRaw where
  toFun d := (d.s,d.m,d.k,d.n,d.H,d.A,d.γ,d.p,d.θ)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2.1,x.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.1,x.2.2.2.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance innerDataPrimcodable : Primcodable InnerData := Primcodable.ofEquiv InnerDataRaw innerDataEquiv
@[fun_prop] lemma c_innerData_s : Computable (InnerData.s) :=
  (Primrec.fst.comp (Primrec.of_equiv (e:=innerDataEquiv))).to_comp
@[fun_prop] lemma c_innerData_m : Computable (InnerData.m) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))).to_comp
@[fun_prop] lemma c_innerData_k : Computable (InnerData.k) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv))))).to_comp
@[fun_prop] lemma c_innerData_n : Computable (InnerData.n) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))).to_comp
@[fun_prop] lemma c_innerData_H : Computable (InnerData.H) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv))))))).to_comp
@[fun_prop] lemma c_innerData_A : Computable (InnerData.A) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))))).to_comp
@[fun_prop] lemma c_innerData_γ : Computable (InnerData.γ) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv))))))))).to_comp
@[fun_prop] lemma c_innerData_p : Computable (InnerData.p) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))))))).to_comp
@[fun_prop] lemma c_innerData_θ : Computable (InnerData.θ) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=innerDataEquiv)))))))))).to_comp
instance outerDataPrimcodable : Primcodable OuterData := Primcodable.ofEquiv OuterDataRaw outerDataEquiv
@[fun_prop] lemma c_outerData_u : Computable (OuterData.u) :=
  (Primrec.fst.comp (Primrec.of_equiv (e:=outerDataEquiv))).to_comp
@[fun_prop] lemma c_outerData_b4 : Computable (OuterData.b4) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv)))).to_comp
@[fun_prop] lemma c_outerData_v : Computable (OuterData.v) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv))))).to_comp
@[fun_prop] lemma c_outerData_k : Computable (OuterData.k) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv)))))).to_comp
@[fun_prop] lemma c_outerData_t : Computable (OuterData.t) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=outerDataEquiv)))))).to_comp
def gridDataEquiv : GridData ≃ GridDataRaw where
  toFun d := (d.T,d.L,d.r)
  invFun x := ⟨x.1,x.2.1,x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
instance gridDataPrimcodable : Primcodable GridData := Primcodable.ofEquiv GridDataRaw gridDataEquiv
@[fun_prop] lemma c_gridData_T : Computable (GridData.T) :=
  (Primrec.fst.comp (Primrec.of_equiv (e:=gridDataEquiv))).to_comp
@[fun_prop] lemma c_gridData_L : Computable (GridData.L) :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e:=gridDataEquiv)))).to_comp
@[fun_prop] lemma c_gridData_r : Computable (GridData.r) :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e:=gridDataEquiv)))).to_comp

@[fun_prop] lemma c_sigma : Computable rationalSigma := by unfold rationalSigma; fun_prop
@[fun_prop] lemma c_eta : Computable rationalEta := by unfold rationalEta; fun_prop
@[fun_prop] lemma c_R : Computable rationalR := by unfold rationalR; fun_prop
@[fun_prop] lemma c_T : Computable rationalT := by unfold rationalT; fun_prop
end MinUncut.Preprocess

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformGrid
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction

def signatureExpr (t : ℕ) : AExpr :=
  AExpr.add
    (AExpr.sum (List.ofFn fun i : Fin t =>
      AExpr.mul
        (AExpr.sum (List.ofFn fun p : Fin 3 =>
          AExpr.mul
            (AExpr.sum (List.ofFn fun q : Fin 3 =>
              AExpr.mul (.eq (slotExpr i.val p.val) (slotExpr i.val q.val))
                (.const (2^q.val))))
            (.const ((2^3)^p.val))))
        (.const (((2^3)^3)^i.val))))
    (.mul (.const (((2^3)^3)^t))
      (.sum (List.ofFn fun i : Fin t=> .mul (slotExpr i.val 3) (.const (2^i.val)))))

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandExpressions
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncutGames.Reduction

variable {t : ℕ} {h : Fin t → Bool}

def secondAddress (h : Fin t → Bool) (pos : Fin t → Fin 3) : AExpr :=
  .add ((AExpr.mul ((AExpr.reg 1).pow 3) (.const 2)).pow t) (secondExpr h pos)

end MinUncut.Costed.SourceWords

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_CanonicalSamplerGraph
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open MinUncut.PathRealization

lemma rawRow_pack {N : ℕ} (ds : List (Demand (Fin N))) (u : Fin (N+ds.length*3)) :
    rawRow N ds.length (packDemands ds) u.val (N+ds.length*3)=
      ((List.finRange (N+ds.length*3)).map fun v=>
        canonicalAdjacent (fun d:Fin ds.length=>ds[d]) u v).map Bool.toNat := by
  rw [rawRow,←finRange_vals,List.map_map,List.map_map]
  congr 1
  funext v
  exact rawCell_canonical ds u v

lemma rawTable_pack {N : ℕ} (ds : List (Demand (Fin N))) :
    rawTable N ds.length (packDemands ds) (N+ds.length*3) (N+ds.length*3)=
      (canonicalTable ds).map Bool.toNat := by
  rw [rawTable,←finRange_vals,List.flatMap_map,canonicalTable,List.map_flatMap]
  congr 1
  funext u
  exact rawRow_pack ds u

end MinUncut.Costed.GraphRegisters

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_UniformEquationOutput
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.SourceTemplate
open MinUncutGames.Foundations MinUncutGames.Foundations.Target
open PCP Hastad Hastad.SourceContexts Hastad.SourceOccurrences
open MinUncutGames.Reduction MinUncut.Costed
noncomputable section

def sourceVariableExpr (u : ℕ) : AExpr :=
  .add (.mul ((AExpr.reg 0).pow u) (.const (2^(2^u))))
    (.add (.mul ((AExpr.reg 1).pow u) (.const (2^(8^u)))) (.const 1))
end
end MinUncut.SourceTemplate

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CodeContinuations
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.Arena
open Turing.ToPartrec

open Turing.ToPartrec

def OutputState.tick (s : OutputState) : OutputState :=
  if s.ptr=0 then s else ⟨read s.heap s.ptr 1,s.heap,read s.heap s.ptr 0::s.acc⟩

def outRead (j : Fin 4) : Expr :=
  .at (.add (.add (.const (4+j.val)) (.reg 2))
    (.mul (.const 4) (.sub (.reg 1) (.reg 0))))

def outputStep (v : List ℕ) : List ℕ :=
  if v.headI=0 then v else
    [(outRead 1).eval v,(r 1).eval v,(r 2).eval v+1,(outRead 0).eval v]++v.drop 3

@[simp] lemma out_encode_reg2 (s : OutputState) : (r 2).eval s.encode=s.acc.length := rfl

lemma output_null_iter (h : Heap) (acc : List ℕ) (i : ℕ) :
    OutputState.tick^[i] ⟨0,h,acc⟩=⟨0,h,acc⟩ := by
  induction i with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply',ih]; rfl

end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_FiberPrefix
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MinUncut.Costed.FiberPrefix
open Turing.ToPartrec Polynomial
lemma run_args (i K : ℕ) (rest : List ℕ) :
    Runs args (i::K::rest) [K,i] (2000*(magnitude (i::K::rest)+1)) := by
  have h:=run_cons (run_comp (run_tail (i::K::rest)) (run_head (K::rest))) (run_head (i::K::rest))
  apply h.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

lemma run_step (cell : Code) (i K z C : ℕ) (rest : List ℕ)
    (hc : Runs cell [K,i] [z] C) :
    Runs (step cell) (i::K::rest) ((i+1)::K::z::rest)
      (C+10000*(magnitude (i::K::rest)+z+1)) := by
  have hp:=run_comp (run_args i K rest) hc
  have ht:=run_comp (run_tail (i::K::rest)) (run_tail (K::rest))
  have hk:=run_comp (run_tail (i::K::rest)) (run_head (K::rest))
  have hh:=run_cons (run_succ (i::K::rest)) (run_cons hk (run_cons hp ht))
  apply hh.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

lemma magnitude_append (v w : List ℕ) : magnitude (v++w)=magnitude v+magnitude w := by
  induction v with
  | nil => simp only [List.nil_append,magnitude_nil,Nat.zero_add]
  | cons a v ih => simp only [List.cons_append,magnitude_cons,ih]; omega
lemma magnitude_reverse (v : List ℕ) : magnitude v.reverse=magnitude v := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.reverse_cons,magnitude_append,magnitude_cons,magnitude_nil,ih]; omega
lemma magnitude_take (i : ℕ) (v : List ℕ) : magnitude (v.take i)≤ magnitude v := by
  induction i generalizing v with
  | zero => simp [magnitude]
  | succ i ih => cases v with
    | nil => rfl
    | cons a v => simpa only [List.take_succ_cons,magnitude_cons] using Nat.add_le_add_left (ih v) (a+1)
lemma state_size (f : ℕ → List ℕ) (K i : ℕ) (v : List ℕ) :
    magnitude (state f K i v)≤ i + K + 2 + magnitude (f K) + magnitude v := by
  have ht:=magnitude_take i (f K).reverse
  simp only [state,List.cons_append,magnitude_cons,magnitude_append,magnitude_reverse] at *
  omega

lemma run_init (len : Code) (K n C : ℕ) (v : List ℕ)
    (hc : Runs len [K] [n] C) :
    Runs (init len) (K::v) (n::0::K::K::v)
      (C+3000*(magnitude (K::v)+n+1)) := by
  have h:=run_cons (run_comp (run_head (K::v)) hc)
    (run_cons (run_const_zero (K::v)) (run_cons (run_head (K::v)) (run_id (K::v))))
  apply h.mono
  simp only [magnitude_cons,magnitude_nil,List.headI_cons]
  omega

def code (len cell : Code) : Code :=
  .comp (.comp .tail .tail) (.comp (iterCode (step cell)) (init len))
lemma run_code {f : ℕ → List ℕ} {len cell : Code}
    (hlen : ∀K,[((f K).length)]∈len.eval [K])
    (hcell : ∀K i,[(f K).reverse[i]?.getD 0]∈cell.eval [K,i]) (K : ℕ) :
    ∃p : Polynomial ℕ,∀v,Runs (code len cell) (K::v) (f K++K::v)
      (p.eval (magnitude (K::v))) ∧
      magnitude (f K++K::v)≤p.eval (magnitude (K::v)) := by
  obtain ⟨A,hA⟩:=CodeRun.complete (hlen K)
  have ht:∀i,∃T,CodeRun cell [K,i] [(f K).reverse[i]?.getD 0] T :=
    fun i=>CodeRun.complete (hcell K i)
  let n:=(f K).length
  let C:=((Finset.range (n+1)).sum (fun i=>Classical.choose (ht i)+(f K).reverse[i]?.getD 0))
  have hc (i : ℕ) (hi : i≤n) :
      Runs cell [K,i] [(f K).reverse[i]?.getD 0] C ∧ (f K).reverse[i]?.getD 0≤C := by
    have hs:=Finset.single_le_sum (f:=fun i=>Classical.choose (ht i)+(f K).reverse[i]?.getD 0)
      (fun j _=>Nat.zero_le _) (show i∈Finset.range (n+1) by simp; omega)
    exact ⟨⟨_,by dsimp [C]; omega,Classical.choose_spec (ht i)⟩,by dsimp [C]; omega⟩
  let q : Polynomial ℕ := X+Polynomial.C (n+K+2+magnitude (f K))
  let b : Polynomial ℕ := Polynomial.C C+Polynomial.C 10000*(q+Polynomial.C C+1)
  let p : Polynomial ℕ := Polynomial.C A+Polynomial.C 3000*(X+Polynomial.C n+1)+
    Polynomial.C (n+1)*(b+Polynomial.C 5000*(Polynomial.C n+q+4))+
    Polynomial.C 100*(q+1)+Polynomial.C (magnitude (f K))+X+2
  refine ⟨p,fun v=>?_⟩
  have hs (i : ℕ) (hi : i≤n) : magnitude ((transition f)^[i] (0::K::K::v))≤q.eval (magnitude (K::v)) := by
    rw [iterate_state f K i (K::v) hi]
    have hh:=state_size f K i (K::v)
    simp only [q,eval_add,eval_X,eval_C]
    omega
  have hh:=run_iter (c:=step cell) (transition f) n (0::K::K::v)
    (q.eval (magnitude (K::v))) (b.eval (magnitude (K::v))) hs (by
      intro i hi
      rw [iterate_state f K i (K::v) (by omega),iterate_state f K (i+1) (K::v) (by omega)]
      rw [state_step f K i (K::v) hi]
      have hr:=run_step cell i K ((f K).reverse[i]?.getD 0) C
        (((f K).reverse.take i).reverse++K::v) (hc i (by omega)).1
      apply hr.mono
      have hsize:=hs i (by omega)
      rw [iterate_state f K i (K::v) (by omega)] at hsize
      have hz:=(hc i (by omega)).2
      simp only [b,eval_add,eval_mul,eval_C,eval_one]
      change C+10000*(magnitude (state f K i (K::v))+_+1)≤_
      omega)
  have hend : (transition f)^[n] (0::K::K::v)=n::K::(f K++K::v) := by
    rw [iterate_state f K n (K::v) le_rfl]
    simp only [state,n,List.cons_append]
    rw [show (f K).length=(f K).reverse.length from List.length_reverse.symm,
      List.take_length,List.reverse_reverse]
  rw [hend] at hh
  have hinit:=run_init len K n A v ⟨A,le_rfl,hA⟩
  have htail:=run_comp (run_tail (n::K::(f K++K::v))) (run_tail (K::(f K++K::v)))
  have hr:=run_comp (run_comp hinit hh) htail
  constructor
  · apply hr.mono
    have hlast:=hs n le_rfl
    rw [hend] at hlast
    simp only [p,eval_add,eval_mul,eval_C,eval_X,eval_one,eval_ofNat]
    simp only [magnitude_cons] at hlast ⊢
    omega
  · simp only [p,eval_add,eval_mul,eval_C,eval_X,eval_one,eval_ofNat,magnitude_append]
    omega

lemma exists_code {f : ℕ → List ℕ} (hf : Computable f) :
    ∃c : Code,∀K,∃p : Polynomial ℕ,∀v,
      Runs c (K::v) (f K++K::v) (p.eval (magnitude (K::v))) ∧
      magnitude (f K++K::v)≤p.eval (magnitude (K::v)) := by
  have hl:Computable (fun K=>(f K).length) := Primrec.list_length.to_comp.comp hf
  have hg:Computable₂ (fun K i=>(f K).reverse[i]?.getD 0) :=
    Primrec.option_getD.to_comp.comp
      (Primrec.list_getElem?.to_comp.comp (Primrec.list_reverse.to_comp.comp (hf.comp Computable.fst)) Computable.snd)
      (Computable.const 0)
  obtain ⟨l,hl⟩:=scalar_code hl
  obtain ⟨g,hg⟩:=scalar₂_code hg
  exact ⟨code l g,run_code hl hg⟩
end MinUncut.Costed.FiberPrefix

end

namespace MinUncut.Costed
open Polynomial

lemma quadruple_spec (v : List ℕ) : quadrupleWords (v.length::v)=quadruple v := by
  have hr := reversePrefix_spec v []
  simp only [List.append_nil] at hr
  simp only [quadrupleWords,List.headI_cons,List.tail_cons,hr]
  have hs := reversePrefix_spec (v.reverse++v) []
  simp only [List.append_nil,List.length_append,List.length_reverse] at hs
  rw [show 2*v.length=v.length+v.length by omega,hs]
  simp only [List.reverse_append,List.reverse_reverse,quadruple,List.append_assoc]
end MinUncut.Costed

namespace MinUncut.Costed.UnaryWords
open Turing.ToPartrec Polynomial Arena

lemma step_safe (v : List ℕ) :
    (step v).length≤v.length+4 ∧ maximum (step v)≤ maximum v+1 := by
  have h0:=head_le_maximum v
  have h1:=(head_le_maximum (v.drop 1)).trans (maximum_drop v 1)
  have h2:=(head_le_maximum (v.drop 2)).trans (maximum_drop v 2)
  have h3:=maximum_drop v 3
  have hl:=(show (v.drop 3).length ≤ v.length from by simp only [List.length_drop]; omega)
  unfold step
  split_ifs <;> simp only [List.length_cons,maximum_cons] <;>
    exact ⟨by omega,by omega⟩

lemma iterate_state (input pre suffix : List ℕ) (c : ℕ) (acc : List ℕ)
    (he : input=pre++suffix) :
    step^[count suffix] (state pre.length c acc input)=
      state (pre.length+count suffix) (lastCounter c suffix) (decodeAux c acc suffix) input := by
  induction suffix generalizing pre c acc with
  | nil => simp only [count,Function.iterate_zero_apply,lastCounter,decodeAux,Nat.add_zero]
  | cons a as ih =>
    by_cases h0 : a=0
    · simp only [count,h0,ite_true,Function.iterate_zero_apply,lastCounter,decodeAux,Nat.add_zero]
    · have hs : (input.drop pre.length).headI=a := by rw [he,List.drop_left]; rfl
      rw [count,ite_eq_right h0,Function.iterate_succ_apply,step_state,hs]
      have he' : input=(pre++[a])++as := by simpa only [List.append_assoc,List.singleton_append] using he
      have hp : (pre++[a]).length=pre.length+1 := by simp
      by_cases h1 : a=1
      · rw [ite_eq_left h1,←hp,ih _ _ _ he']
        simp only [lastCounter,decodeAux,h1,ite_true,List.length_append,List.length_singleton]
        congr 1
        omega
      · rw [ite_eq_right h1,←hp,ih _ _ _ he']
        simp only [lastCounter,decodeAux,h0,h1,ite_false,List.length_append,List.length_singleton]
        congr 1
        omega

lemma iterate_size (v : List ℕ) (i : ℕ) (hi : i ≤ count v) :
    magnitude (step^[i] (state 0 0 [] v))≤parseSize.eval (magnitude v) := by
  have hh:=iterate_length_maximum 4 1 step_safe (state 0 0 [] v) i
  have hl:=count_le v
  have hv:=length_le_magnitude v
  have hm:=maximum_le_magnitude v
  have hs:=magnitude_le_length_maximum (step^[i] (state 0 0 [] v))
  simp only [state,List.cons_append,List.nil_append,List.length_nil,List.length_cons,
    maximum_cons,Nat.zero_max,Nat.one_mul] at hh
  change (step^[i] (state 0 0 [] v)).length≤v.length+3+4*i ∧
    maximum (step^[i] (state 0 0 [] v))≤ maximum v+i at hh
  simp only [parseSize,eval_mul,eval_C,eval_pow,eval_add,eval_X,eval_one]
  have hlen : (step^[i] (state 0 0 [] v)).length≤5*(magnitude v+1) := by omega
  have hmax : maximum (step^[i] (state 0 0 [] v))+1≤2*(magnitude v+1) := by omega
  have hh:=Nat.mul_le_mul hlen hmax
  nlinarith

end MinUncut.Costed.UnaryWords

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_TM2Costed
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace Turing.PartrecToTM2
open scoped _root_.Turing _root_.Turing.PartrecToTM2
open Function
open MinUncut.Costed
open _root_.Turing.PartrecToTM2.K'

theorem head_main_steps {q s L} {c d : List _root_.Turing.PartrecToTM2.Γ'} :
    Steps (_root_.Turing.TM2.step _root_.Turing.PartrecToTM2.tr) (2*(_root_.Turing.PartrecToTM2.trNat L.headI).length+(_root_.Turing.PartrecToTM2.trList L.tail).length+6)
      ⟨some (_root_.Turing.PartrecToTM2.head main q), s, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList L) [] c d⟩
      ⟨some q, none, _root_.Turing.PartrecToTM2.K'.elim (_root_.Turing.PartrecToTM2.trList [L.headI]) [] c d⟩ := by
  let o : Option _root_.Turing.PartrecToTM2.Γ' := List.casesOn L none fun _ _ => some _root_.Turing.PartrecToTM2.Γ'.cons
  have heq : 2*(_root_.Turing.PartrecToTM2.trNat L.headI).length+(_root_.Turing.PartrecToTM2.trList L.tail).length+6 =
      ((_root_.Turing.PartrecToTM2.trNat L.headI).length+1) +
        ((((_root_.Turing.PartrecToTM2.trList L.tail).length+1)+((_root_.Turing.PartrecToTM2.trNat L.headI).length+2)+1)+1) := by omega
  rw [heq]
  refine steps_trans
    (move_steps (by decide)
      (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ (_root_.Turing.PartrecToTM2.trNat L.headI) o (_root_.Turing.PartrecToTM2.trList L.tail) (_root_.Turing.PartrecToTM2.trNat_natEnd _) ?_))
      (steps_head rfl (steps_head rfl ?_))
  · cases L <;> simp [o]
  rw [_root_.Turing.PartrecToTM2.tr]
  simp only [_root_.Turing.TM2.stepAux, elim_update_main, elim_rev, elim_update_rev,
    Function.update_self, _root_.Turing.PartrecToTM2.trList]
  rw [ite_eq_right (show o ≠ some _root_.Turing.PartrecToTM2.Γ'.consₗ by cases L <;> simp [o])]
  refine steps_trans (clear_steps (_root_.Turing.PartrecToTM2.splitAtPred_eq _ _ _ none [] ?_ ⟨rfl,rfl⟩)) ?_
  · exact fun x h => Bool.decide_false (_root_.Turing.PartrecToTM2.trList_ne_consₗ _ _ h)
  simpa [List.reverseAux_eq] using
    (unrev_steps (q := q) (s := none) (S := _root_.Turing.PartrecToTM2.K'.elim [] (_root_.Turing.PartrecToTM2.Γ'.cons :: (_root_.Turing.PartrecToTM2.trNat L.headI).reverse) c d))

end Turing.PartrecToTM2

end

namespace MinUncut.Costed
open _root_.Turing _root_.Turing.ToPartrec _root_.Turing.PartrecToTM2
  _root_.OAI.Turing.PartrecToTM2 Function
open _root_.Turing.PartrecToTM2.K'

theorem head_tail_length (v : List ℕ) :
    (trNat v.headI).length+(trList v.tail).length ≤ bitsize v := by
  cases v <;> simp [bitsize,trList]

theorem head_length (v : List ℕ) : (trNat v.headI).length ≤ bitsize v :=
  (Nat.le_add_right _ _).trans (head_tail_length v)

theorem save_steps (f fs : Code) (k : Cont') (v : List ℕ) (s : Option Γ') (S : List Γ') :
    Steps (TM2.step tr) (2*bitsize v+3)
      ⟨some (trNormal (.cons f fs) k),s,K'.elim (trList v) [] [] S⟩
      ⟨some (trNormal f (.cons₁ fs k)),none,
        K'.elim (trList v) [] [] (trList v ++ Γ'.consₗ::S)⟩ := by
  have he : 2*bitsize v+3=((trList v).length+1)+((trList v).length+1)+1 := by
    simp only [bitsize]; omega
  rw [he]
  refine steps_head rfl (steps_trans (move_steps (by decide) (splitAtPred_false _)) ?_)
  simp only [elim_stack,elim_update_stack,elim_update_main,elim_rev,elim_update_rev]
  simpa [List.reverseAux_eq] using
    (copy_steps (trNormal f (.cons₁ fs k)) none [] (trList v).reverse [] (Γ'.consₗ::S))

theorem swap_steps (fs : Code) (k : Cont') (v u : List ℕ) (s : Option Γ') (S : List Γ') :
    Steps (TM2.step tr) (4*bitsize u+2*bitsize v+10)
      ⟨some (Λ'.ret (.cons₁ fs k)),s,
        K'.elim (trList u) [] [] (trList v ++ Γ'.consₗ::S)⟩
      ⟨some (trNormal fs (.cons₂ k)),none,
        K'.elim (trList v) [] [] (trList u ++ Γ'.consₗ::S)⟩ := by
  have he : 4*bitsize u+2*bitsize v+10 =
      (2*(trList u).length+3)+((2*(trList v).length+3)+(2*(trList u).length+3))+1 := by
    simp only [bitsize]; omega
  rw [he]
  refine steps_head rfl (steps_trans (move₂_steps (by decide) rfl (splitAtPred_false _)) ?_)
  simp only [Option.elim,id_eq,elim_update_main,elim_aux,
    List.append_nil,elim_update_aux]
  refine steps_trans (move₂_steps (o := some Γ'.consₗ) (L₂ := S) (by decide) rfl ?_) ?_
  · exact splitAtPred_eq _ _ (trList v) (some Γ'.consₗ) S
      (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl,rfl⟩
  simpa only [Option.elim,List.append_nil,elim_update_stack,elim_main,
    elim_update_main,id_eq,elim_update_aux,elim_aux,elim_stack] using
    (move₂_steps (q := trNormal fs (.cons₂ k)) (s := none)
      (p := fun _ => false) (k₁ := aux) (k₂ := stack)
      (S := K'.elim (trList v) [] (trList u) (Γ'.consₗ::S))
      (by decide) rfl (splitAtPred_false _))

theorem CodeRun.compiled {c v w t} (h : CodeRun c v w t)
    (k : Cont') (s : Option Γ') (S : List Γ') : ∃ s',
    Within (TM2.step tr) t
      ⟨some (trNormal c k),s,K'.elim (trList v) [] [] S⟩
      ⟨some (Λ'.ret k),s',K'.elim (trList w) [] [] S⟩ := by
  induction h generalizing k s S with
  | zero v => exact ⟨s,within_one (by simp [TM2.step])⟩
  | succ v =>
    refine ⟨none,?_⟩
    have hh := (head_main_steps (q := Λ'.succ (.ret k)) (s := s) (L := v)
      (c := []) (d := S)).within.trans (succ_time (n := v.headI))
    exact hh.mono (by have hv := head_tail_length v; dsimp [bitsize] at *; omega)
  | tail v =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine ⟨o,?_⟩
    have hh : Steps (TM2.step tr) ((trNat v.headI).length+1)
        ⟨some (trNormal .tail k),s,K'.elim (trList v) [] [] S⟩
        ⟨some (.ret k),o,K'.elim (trList v.tail) [] [] S⟩ := by
      convert! (clear_steps (q := .ret k) (s := s) (k := main)
        (S := K'.elim (trList v) [] [] S)
        (splitAtPred_eq _ _ (trNat v.headI) o (trList v.tail) (trNat_natEnd _) ?_)) using 2
      · simp
      · dsimp [o]
        cases v <;> exact ⟨rfl,rfl⟩
    exact hh.within.mono (by have hv := head_length v; omega)
  | @cons f fs v u w t t' hf hfs ih ih' =>
    obtain ⟨s₁,h₁⟩ := ih (.cons₁ fs k) none (trList v ++ Γ'.consₗ::S)
    obtain ⟨s₂,h₂⟩ := ih' (.cons₂ k) none (trList u ++ Γ'.consₗ::S)
    have h₃ := (save_steps f fs k v s S).within.trans h₁
    have h₄ := h₃.trans (swap_steps fs k v u s₁ S).within
    have h₅ := h₄.trans h₂
    have h₆ : Within (TM2.step tr) (2*bitsize u+6+1)
        ⟨some (.ret (.cons₂ k)),s₂,K'.elim (trList w) [] [] (trList u ++ Γ'.consₗ::S)⟩
        ⟨some (.ret k),none,K'.elim (trList (u.headI::w)) [] [] S⟩ :=
      (head_stack_time (q := .ret k) (s := s₂) (L₁ := w) (L₂ := u) (L₃ := S)).head rfl
    exact ⟨none,(h₅.trans h₆).mono (by omega)⟩
  | @comp f g v u w t t' hg hf ih ih' =>
    obtain ⟨s₁,h₁⟩ := ih (.comp f k) s S
    obtain ⟨s₂,h₂⟩ := ih' k s₁ S
    exact ⟨s₂,(h₁.trans (h₂.head rfl)).mono (by omega)⟩
  | @caseZero f g v w t hz hf ih =>
    obtain ⟨s₁,h₁⟩ := pred_time (trNormal f k) (trNormal g k) s v [] S
    simp only [hz,Nat.rec_zero] at h₁
    obtain ⟨s₂,h₂⟩ := ih k s₁ S
    exact ⟨s₂,(h₁.trans h₂).mono (by dsimp [bitsize]; omega)⟩
  | @caseSucc f g v a w t hg ih =>
    obtain ⟨s₁,h₁⟩ := pred_time (trNormal f k) (trNormal g k) s ((a+1)::v) [] S
    simp only [List.headI_cons,List.tail_cons] at h₁
    obtain ⟨s₂,h₂⟩ := ih k s₁ S
    exact ⟨s₂,(h₁.trans h₂).mono (by dsimp [bitsize]; omega)⟩
  | @fixDone f v u t hf hu ih =>
    obtain ⟨s₁,h₁⟩ := ih (.fix f k) s S
    exact ⟨(trList u).head?,h₁.trans (fix_done_steps f k u s₁ S hu).within⟩
  | @fixMore f v u a w t t' hf hr ih ih' =>
    obtain ⟨s₁,h₁⟩ := ih (.fix f k) s S
    obtain ⟨s₂,h₂⟩ := ih' k (some Γ'.cons) S
    exact ⟨s₂,((h₁.trans (fix_more_steps f k a u s₁ S).within).trans h₂).mono
      (by dsimp [bitsize]; simp only [List.length_append,List.length_cons]; omega)⟩

open _root_.Turing
end MinUncut.Costed

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphWordCodec
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable _root_.OAI.MinUncut.Preprocess.rationalPrimcodable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncut.Costed.GraphCodec
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2
open MinUncutGames.BinaryEncoding

def outputsInTime (n k : ℕ) (v : List Bool) (rest : List ℕ) :
    TM2OutputsInTime machine (trList (n::(v.map Bool.toNat++2::k::rest)))
      (some (nameBits n++v++nameBits k))
      (2*bitsize (n::(v.map Bool.toNat++2::k::rest))+
        (nameBits n++v++nameBits k).length+2) := by
  have hh := WordTransducer.outputsInTime .header next emit (trList (n::(v.map Bool.toNat++2::k::rest)))
  exact (congrArg (fun w : List Bool =>
    TM2OutputsInTime machine (trList (n :: (v.map Bool.toNat ++ 2 :: k :: rest)))
      (some w) (2 * bitsize (n :: (v.map Bool.toNat ++ 2 :: k :: rest)) + w.length + 2))
    (output n k v rest)).mp hh

end MinUncut.Costed.GraphCodec

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_FramedWordDecoder
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MinUncut.Costed.FrameDecode
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 MinUncutGames.BinaryEncoding
lemma magnitude_symbols (v : List Bool) : magnitude (v.map symbol)≤3*v.length := by
  induction v with
  | nil => rfl
  | cons b v ih =>
    have hb : b.toNat≤1 := by cases b <;> decide
    simp only [List.map_cons,magnitude_cons,List.length_cons,symbol]
    omega
end MinUncut.Costed.FrameDecode

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Estimates_CountedWordParser
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.UnaryWords
open Turing.ToPartrec Polynomial Arena
lemma finishCounted_iterate (v : List ℕ) :
    finishCounted (step^[count v] (state 0 0 [] v))=parsedCounted v := by
  have h:=iterate_state v [] v 0 [] (by rfl)
  simpa only [List.length_nil,Nat.zero_add,finishCounted,finish,state,List.cons_append,List.nil_append,
    List.drop_succ_cons,List.drop_zero,List.headI_cons,parsedCounted,parsed] using congrArg finishCounted h

open MinUncutGames.Foundations.Complexity
end MinUncut.Costed.UnaryWords

namespace MinUncut.Costed.Arena
open Turing.ToPartrec Polynomial
noncomputable section

def stopExpr : Expr := .sub (.const 1) (.eq (.reg 0) (.const 2))
lemma stop_zero (v : List ℕ) : stopExpr.eval v=0 ↔ v.headI=2 := by
  simp only [stopExpr,Expr.eval,List.drop_zero]
  split_ifs <;> simp_all

def prepareUnbounded (v : List ℕ) : List ℕ :=
  [(r 2).eval v,(r 4).eval v,0,2]++v.drop 5

end

open Turing.ToPartrec Polynomial
end MinUncut.Costed.Arena

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_DemandOrder
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open PolyProgram

def vertexExpr : Expr := .add (.reg 0) (.mul (.reg 1) (.const 3))
def lastVertexExpr : Expr := .sub vertexExpr (.const 1)

def rawGraphWords (N M k : ℕ) (data : List ℕ) : List ℕ :=
  let V := N+M*3
  V::(rawTable N M data V V++2::k::data)

def renderRaw (v : List ℕ) : List ℕ :=
  rawGraphWords v.headI (v.drop 1).headI (v.drop 2).headI (v.drop 3)

lemma renderRaw_encode (N M k : ℕ) (data : List ℕ) :
    renderRaw (N::M::k::data)=rawGraphWords N M k data := rfl

open MinUncut.PathRealization

lemma rawTable_append (N M : ℕ) (data rest : List ℕ) (r c : ℕ) (h : 3*M≤data.length) :
    rawTable N M (data++rest) r c=rawTable N M data r c := by
  unfold rawTable rawRow
  have hh : rawCell N M (data++rest)=rawCell N M data := by
    funext u v
    exact rawCell_append N M data rest u v h
  rw [hh]

lemma renderer_pack {N : ℕ} (ds : List (Demand (Fin N))) (k : ℕ) (rest : List ℕ) :
    renderRaw (N::ds.length::k::(packDemands ds++rest))=
      (N+ds.length*3)::((canonicalTable ds).map Bool.toNat++2::k::(packDemands ds++rest)) := by
  rw [renderRaw_encode,rawGraphWords,rawTable_append N ds.length _ rest _ _ (by rw [length_packDemands]),
    rawTable_pack]
end MinUncut.Costed.GraphRegisters

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Graphs_GraphSize
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.SourceWords
open MinUncut.Inner MinUncut.Outer MinUncut.Outer.LocalTemplate
open MinUncut.PathRealization MinUncutGames.Reduction
open MinUncutGames.Foundations.Hastad.SourceOccurrences
noncomputable section

def tupleCountExpr (t : ℕ) : AExpr := (AExpr.reg 1).pow t

def variableCountExpr (t : ℕ) : AExpr :=
  .mul (.add ((AExpr.mul ((AExpr.reg 0).pow 3) (.const 2)).pow t)
      ((AExpr.add (.reg 0) (.mul ((AExpr.reg 0).pow 3) (.const 2))).pow t))
    (.const (2^((2^3)^t)))

def unitCountExpr (es : List AExpr) (t : ℕ) : AExpr :=
  .div (.mul (tupleCountExpr t) (.const es.length)) (.const 3)

def thresholdExpr (t D : ℕ) : AExpr :=
  .mul (.const (5*D)) (tupleCountExpr t)

def demandStageWords (es : List AExpr) (t D : ℕ) (v : List ℕ) : List ℕ :=
  (variableCountExpr t).eval v::(unitCountExpr es t).eval v::(thresholdExpr t D).eval v::
    (Blocks.emitted es ((tupleCountExpr t).eval v) v++Blocks.retained es ((tupleCountExpr t).eval v) v)

end
end MinUncut.Costed.SourceWords

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_CodeFiniteMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace MinUncut.Costed
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Turing.ToPartrec
noncomputable section

def CodeRun.finiteMachine {c v w t} (h : CodeRun c v w t) :
    TM2OutputsInTime (codeMachine c) (trList v) (some (trList w)) (t+1) := by
  apply Classical.choice
  obtain ⟨s,ht⟩ := h.compiled .halt none []
  have he : Within (TM2.step tr) (t+1)
      ⟨some (trNormal c .halt),none,K'.elim (trList v) [] [] []⟩
      ⟨none,none,K'.elim (trList w) [] [] []⟩ :=
    ht.trans (within_one rfl)
  obtain ⟨n,hn,hsteps⟩ := he
  have hi := FiniteControl.projected_iterate (codeMachine c).step (TM2.step tr)
    (FiniteControl.project (codeSupp c .halt))
    (FiniteControl.project_step _ _ (fun _ h => codeSupp_supports (Finset.Subset.refl _) _ h)) n (some (initList (codeMachine c) (trList v)))
  have hs : Steps (codeMachine c).step n
      (initList (codeMachine c) (trList v)) (haltList (codeMachine c) (trList w)) := by
    apply Option.map_injective (FiniteControl.project_injective (codeSupp c .halt))
    dsimp only [Steps] at hsteps ⊢
    exact hi.trans ((congrArg
      (fun cfg : Option (TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')) =>
        (fun x => x.bind (TM2.step tr))^[n] cfg)
      (congrArg some (codeMachine_init c v))).trans
      (hsteps.trans (congrArg some (codeMachine_halt c w)).symm))
  exact ⟨steps_timed hs hn⟩

end
end MinUncut.Costed

end

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Machines_GraphRenderMachine
attribute [-instance] _root_.OAI.MinUncut.Preprocess.option_elim_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MinUncut.Costed.GraphRegisters
open _root_.Turing _root_.OAI.Turing _root_.Turing.PartrecToTM2 _root_.OAI.Turing.PartrecToTM2 Polynomial MinUncutGames.Foundations.Complexity
open MinUncut.PathRealization
noncomputable section

lemma codec_length_le (n k : ℕ) (v : List Bool) (rest : List ℕ) :
    (MinUncutGames.BinaryEncoding.nameBits n++v++MinUncutGames.BinaryEncoding.nameBits k).length≤
      2*magnitude (n::(v.map Bool.toNat++2::k::rest)) := by
  have hf (a : ℕ) : (MinUncutGames.BinaryEncoding.nameBits a).length≤2*a+1 := by
    have h := trNat_length_le a
    rw [GraphCodec.trNat_bits,List.length_map] at h
    have hg (w : List Bool) : (MinUncutGames.BinaryEncoding.frame w).length=2*w.length+1 := by
      induction w with
      | nil => rfl
      | cons b w ih => simp only [MinUncutGames.BinaryEncoding.frame,List.length_cons,ih]; omega
    rw [MinUncutGames.BinaryEncoding.nameBits,hg]
    omega
  have hm (w : List Bool) : w.length+k+3≤ magnitude (w.map Bool.toNat++2::k::rest) := by
    induction w with
    | nil => simp only [List.map_nil,List.nil_append,magnitude_cons,List.length_nil]; omega
    | cons b w ih =>
      simp only [List.map_cons,List.cons_append,magnitude_cons,List.length_cons]
      omega
  have hn := hf n; have hk := hf k; have h := hm v
  simp only [List.length_append,magnitude_cons]
  omega

end
end MinUncut.Costed.GraphRegisters

end OAI
end

section
-- module Solutions.OAIQ076_MU.MinUncut_Search_ArithmeticTactic
attribute [-instance] _root_.OAI.MinUncut.CodeEffective.instPrimcodableCode_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

set_option maxHeartbeats 1000000
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian
@[fun_prop] lemma c_epsilon : Computable (fun p : ℕ × ℕ=>InnerData.epsilon p.1 p.2) := by
  unfold InnerData.epsilon
  exact ca_ratDiv (ca_const 1) (ca_ratMul
    (ca_ratMul (ca_const 40) (ca_ratCast (c_T.comp Computable.fst)))
    (ca_ratAdd (ca_ratCast (ca_pow Computable.snd (ca_const 2))) (ca_const 1)))
@[fun_prop] lemma c_atomConstant : Computable (fun p : ℕ × ℕ × ℕ=>InnerData.atomConstant p.1 p.2.1 p.2.2) := by
  unfold InnerData.atomConstant
  apply ca_mul
  · apply ca_pow <;> fun_prop
  · apply ca_choose
    · apply ca_add
      · apply ca_pow <;> fun_prop
      · fun_prop
    · fun_prop

lemma inner_check_0 : ComputablePred (fun p : ℕ × InnerData =>
    2 ≤ p.2.m) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_1 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.k+2 ≤ p.2.n) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_2 : ComputablePred (fun p : ℕ × InnerData =>
    1 ≤ p.2.k) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_3 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.H) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_4 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.A) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_5 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.γ) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_6 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.p) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_7 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.p < 1) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_8 : ComputablePred (fun p : ℕ × InnerData =>
    0 < p.2.θ) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_9 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.θ < 1) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_10 : ComputablePred (fun p : ℕ × InnerData =>
    ((p.2.s:ℚ)+3)*(1+rationalSigma p.1^2)⁻¹ ≤ (p.2.s:ℚ)+2) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_11 : ComputablePred (fun p : ℕ × InnerData =>
    ((p.2.s:ℚ)+2)*((1+rationalSigma p.1^2)⁻¹)^(p.2.s+2) ≤ 1/16) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_12 : ComputablePred (fun p : ℕ × InnerData =>
    rationalR p.1*p.2.m < (p.2.m-p.2.s).choose 2) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_13 : ComputablePred (fun p : ℕ × InnerData =>
    ((p.2.s+rationalR p.1*p.2.m:ℕ):ℚ)*(p.2.k:ℚ)/((p.2.n:ℚ)-1) < (InnerData.epsilon p.1 p.2.m*rationalSigma p.1)^2) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_14 : ComputablePred (fun p : ℕ × InnerData =>
    (rationalSigma p.1)⁻¹^2/(p.2.H:ℚ) < InnerData.epsilon p.1 p.2.m) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_15 : ComputablePred (fun p : ℕ × InnerData =>
    2*(rationalSigma p.1)⁻¹^2/(p.2.A:ℚ) < InnerData.epsilon p.1 p.2.m) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_16 : ComputablePred (fun p : ℕ × InnerData =>
    (p.2.m:ℚ)/((p.2.k:ℚ)+1) < (InnerData.epsilon p.1 p.2.m/(2*(p.2.A:ℚ)))^(2^p.2.m)) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_17 : ComputablePred (fun p : ℕ × InnerData =>
    (p.2.H:ℚ)*(p.2.γ+(p.2.H:ℚ)^2/(p.2.A:ℚ)) < InnerData.epsilon p.1 p.2.m^2) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_18 : ComputablePred (fun p : ℕ × InnerData =>
    p.2.θ^2+(p.2.m:ℚ)*p.2.p*(p.2.n^p.2.m:ℕ)/(rationalSigma p.1)^2 <
    (InnerData.epsilon p.1 p.2.m^2*(rationalSigma p.1)^2*p.2.γ/(InnerData.atomConstant p.2.s p.2.m p.2.n:ℚ))^2) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)

lemma inner_check_computable : ComputablePred (fun p : ℕ × InnerData=>p.2.Check p.1) :=
  ca_and inner_check_0 (ca_and inner_check_1 (ca_and inner_check_2 (ca_and inner_check_3 (ca_and inner_check_4 (ca_and inner_check_5 (ca_and inner_check_6 (ca_and inner_check_7 (ca_and inner_check_8 (ca_and inner_check_9 (ca_and inner_check_10 (ca_and inner_check_11 (ca_and inner_check_12 (ca_and inner_check_13 (ca_and inner_check_14 (ca_and inner_check_15 (ca_and inner_check_16 (ca_and inner_check_17 (inner_check_18))))))))))))))))))

@[fun_prop] lemma c_amplitude : Computable (fun p : ℕ × InnerData=>OuterData.amplitude p.1 p.2) := by
  unfold OuterData.amplitude; iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
@[fun_prop] lemma c_hints : Computable OuterData.hints := by
  unfold OuterData.hints
  apply ca_sub
  · apply ca_mul
    · exact c_innerData_m
    · apply ca_pow
      · exact c_innerData_n
      · apply ca_sub
        · exact c_innerData_m
        · exact ca_const 1
  · exact ca_const 1
@[fun_prop] lemma c_rate : Computable OuterData.rate := by unfold OuterData.rate; fun_prop
lemma c_listBound : Computable (fun p : ℕ × InnerData × OuterData=>OuterData.listBound p.1 p.2.1 p.2.2) := by
  unfold OuterData.listBound; iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma c_radicand : Computable (fun p : InnerData × ℕ × ℕ=>OuterData.radicand p.1 p.2.1 p.2.2) := by
  unfold OuterData.radicand; iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
attribute [fun_prop] c_listBound c_radicand
@[fun_prop] lemma c_oTheta : Computable (fun p : ℕ × InnerData × OuterData=>p.2.1.θ) :=
  c_innerData_θ.comp (Computable.fst.comp Computable.snd)
@[fun_prop] lemma c_oP : Computable (fun p : ℕ × InnerData × OuterData=>p.2.1.p) :=
  c_innerData_p.comp (Computable.fst.comp Computable.snd)
@[fun_prop] lemma c_oB4 : Computable (fun p : ℕ × InnerData × OuterData=>p.2.2.b4) :=
  c_outerData_b4.comp (Computable.snd.comp Computable.snd)
lemma outer_check_0 : ComputablePred (fun p : ℕ × InnerData × OuterData=>0 < p.2.2.u) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_1 : ComputablePred (fun p : ℕ × InnerData × OuterData=>0 < p.2.2.b4) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_2 : ComputablePred (fun p : ℕ × InnerData × OuterData=>0 < p.2.2.v) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_3 : ComputablePred (fun p : ℕ × InnerData × OuterData=>1 ≤ p.2.2.t) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_4 : ComputablePred (fun p : ℕ × InnerData × OuterData=>p.2.2.k ≤ p.2.2.t) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_5 : ComputablePred (fun p : ℕ × InnerData × OuterData=>OuterData.listBound p.1 p.2.1 p.2.2 < p.2.1.p/4) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_6 : ComputablePred (fun p : ℕ × InnerData × OuterData=>(64/(p.2.1.θ^2*rationalSigma p.1^2))*(p.1:ℚ)*p.2.2.b4 < p.2.1.p/4) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_7 : ComputablePred (fun p : ℕ × InnerData × OuterData=>OuterData.radicand p.2.1 p.2.2.k p.2.2.t < p.2.2.v^2) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_8 : ComputablePred (fun p : ℕ × InnerData × OuterData=>(256/p.2.1.θ^4)*(p.2.2.u^2*OuterData.amplitude p.1 p.2.1^2+p.2.2.v*(OuterData.amplitude p.1 p.2.1+OuterData.amplitude p.1 p.2.1^2/p.2.2.u)^4) < p.2.1.p/2) := by iterate 12 (all_goals first | with_reducible exact MinUncut.Preprocess.ca_const _ | with_reducible apply MinUncut.Preprocess.ca_ratAdd | with_reducible apply MinUncut.Preprocess.ca_ratMul | with_reducible apply MinUncut.Preprocess.ca_ratSub | with_reducible apply MinUncut.Preprocess.ca_ratDiv | with_reducible apply MinUncut.Preprocess.ca_ratPow | with_reducible apply MinUncut.Preprocess.ca_ratInv | with_reducible apply MinUncut.Preprocess.ca_ratCast | with_reducible apply MinUncut.Preprocess.ca_ratCeil | with_reducible apply MinUncut.Preprocess.ca_ratLe | with_reducible apply MinUncut.Preprocess.ca_ratLt | with_reducible apply MinUncut.Preprocess.ca_add | with_reducible apply MinUncut.Preprocess.ca_mul | with_reducible apply MinUncut.Preprocess.ca_sub | with_reducible apply MinUncut.Preprocess.ca_div | with_reducible apply MinUncut.Preprocess.ca_mod | with_reducible apply MinUncut.Preprocess.ca_pow | with_reducible apply MinUncut.Preprocess.ca_choose | with_reducible apply MinUncut.Preprocess.ca_factorial | with_reducible apply MinUncut.Preprocess.ca_and | with_reducible apply MinUncut.Preprocess.ca_natLe | with_reducible apply MinUncut.Preprocess.ca_natLt | with_reducible fun_prop | fun_prop)
lemma outer_check_computable : ComputablePred (fun p : ℕ × InnerData × OuterData=>p.2.2.Check p.1 p.2.1) :=
  ca_and outer_check_0 (ca_and outer_check_1 (ca_and outer_check_2 (ca_and outer_check_3 (ca_and outer_check_4 (ca_and outer_check_5 (ca_and outer_check_6 (ca_and outer_check_7 (outer_check_8))))))))
end MinUncut.Preprocess

end
section
namespace MinUncut.Preprocess
open MinUncut.Inner MinUncut.Outer MinUncut.FiniteGaussian

lemma inner_exists (K : ℕ) : ∃d : InnerData,d.Check (parameterJ K) :=
  InnerData.check_exists (parameterJ_pos K)
noncomputable def selectedInner (K : ℕ) : InnerData := search inner_exists K
lemma selectedInner_check (K : ℕ) : (selectedInner K).Check (parameterJ K) :=
  search_spec inner_exists K
lemma c_inner_pred : ComputablePred (fun p : ℕ × InnerData=>p.2.Check (parameterJ p.1)) :=
  (inner_check_computable.decide.comp ((c_parameterJ.comp Computable.fst).pair Computable.snd)).computablePred
@[fun_prop] lemma c_selectedInner : Computable selectedInner :=
  computable_search c_inner_pred inner_exists ⟨0,0,0,0,0,0,0,0,0⟩

attribute [local irreducible] selectedInner

lemma outer_exists (K : ℕ) : ∃o : OuterData,o.Check (parameterJ K) (selectedInner K) :=
  OuterData.check_exists (parameterJ_pos K) _ (selectedInner_check K)
noncomputable def selectedOuter (K : ℕ) : OuterData := search outer_exists K
lemma c_outer_arguments : Computable (fun p : ℕ × OuterData =>
    (parameterJ p.1,selectedInner p.1,p.2)) := by
  exact (c_parameterJ.comp Computable.fst).pair
    ((c_selectedInner.comp Computable.fst).pair Computable.snd)
lemma c_outer_decide : Computable (fun p : ℕ × OuterData =>
    decide (p.2.Check (parameterJ p.1) (selectedInner p.1))) := by
  have hh : Computable (fun p : ℕ × InnerData × OuterData=>decide (p.2.2.Check p.1 p.2.1)) :=
    outer_check_computable.decide
  exact @Computable.comp (ℕ × OuterData) (ℕ × InnerData × OuterData) Bool _ _ _
    (fun p=>decide (p.2.2.Check p.1 p.2.1)) (fun p=>(parameterJ p.1,selectedInner p.1,p.2)) hh c_outer_arguments
lemma c_outer_pred : ComputablePred (fun p : ℕ × OuterData=>p.2.Check (parameterJ p.1) (selectedInner p.1)) :=
  c_outer_decide.computablePred
@[fun_prop] lemma c_selectedOuter : Computable selectedOuter :=
  computable_search c_outer_pred outer_exists ⟨0,0,0,0,0⟩
end MinUncut.Preprocess

end

end OAI
end


