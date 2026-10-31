-- Prove2me | Definitions.Def_OAIQ053K016
-- name    : OAIQ053K016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:55:29.767224+00:00
-- url     : https://prove2.me/theorems/314fae47-5e57-44c0-8b0f-98cb834e8067
-- title:
--   Definitions bundle OAIQ053K016 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 31 declarations of OpenAI's Lean: 14 definitions, 1 inductive type or structure and 16 theorems. The definitions and types are `OAI.MetricKMedian.Gaussian.computedIntegerKernel`, `OAI.MetricKMedian.IntegerBranching.branch`, `OAI.MetricKMedian.IntegerBranching.branchNumerator`, `OAI.MetricKMedian.IntegerLaw.computedAffineKernel`, `OAI.MetricKMedian.RationalLaw.integer`, `OAI.MetricKMedian.RationalLaw.real`, `OAI.MetricKMedian.RationalPhysicalKernel.Payload`, `OAI.MetricKMedian.RationalPhysicalKernel.State`, `OAI.MetricKMedian.SparseIntegerLaw`, `OAI.MetricKMedian.SparseIntegerLaw.branch`, `OAI.MetricKMedian.SparseIntegerLaw.dirac`, `OAI.MetricKMedian.SparseIntegerLaw.map`, `OAI.MetricKMedian.SparseIntegerLaw.moment`, `OAI.MetricKMedian.SparseIntegerLaw.real`, `OAI.MetricKMedian.SparseIntegerLaw.realIndex`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Compression_ComputedAffineKernel`, `KMedian_Compression_ComputedIntegerKernel`, `KMedian_Compression_DependentIntegerKernel`, `KMedian_Compression_FinsetVectorExtension`, `KMedian_Compression_GaussianKernel`, `KMedian_Compression_GramBounds`, `KMedian_Compression_RationalIntegerLaw`, `KMedian_Compression_RationalScaling`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_RationalNearestCopies`, `KMedian_Rounding_RationalPhysicalKernel`, `KMedian_Sparse_SparseAlgorithm`, `KMedian_Sparse_SparseIntegerLaw`, `KMedian_Sparse_SparseMap`, `KMedian_Sparse_SparseMarginalTools`, `KMedian_Sparse_SparseRealLaw`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K002`, `OAIQ053K004` and `OAIQ053K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K029`, `OAIQ053K030`, `OAIQ053K031`, `OAIQ053K032`, `OAIQ053K033`, `OAIQ053K034`, `OAIQ053K036` and `OAIQ053K037`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K004
import Definitions.Def_OAIQ053K005

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GramBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

theorem gram_cramer_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |((A.transpose*A).cramer (A.transpose*ᵥw)) c| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  rw [Matrix.cramer_apply]
  have hentry : ∀ i j, |((A.transpose*A).updateCol c (A.transpose*ᵥw)) i j| ≤
      (Fintype.card R:ℤ)*M^2 := by
    intro i j
    by_cases hj : j=c
    · subst j
      simpa using gram_rhs_bound A w M hM hA hw i
    · simpa [Matrix.updateCol_apply,hj] using gram_entry_bound A M hM hA i j
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hentry)

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_DependentIntegerKernel
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem small_integer_dependence_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ (K : Type) (inst : Fintype K), letI := inst;
      ∃ (a : K → Ω) (z : K → ℤ), Function.Injective a ∧
        Fintype.card K ≤ Fintype.card R+1 ∧ (∃ k, z k ≠ 0) ∧
        (∀ k, |z k| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
        ∀ r, ∑ k, z k*V r (a k)=0 := by
  classical
  let v : Ω → R → ℚ := fun i r => V r i
  obtain ⟨κ,a,ha,hspan,hi⟩ := exists_linearIndependent' ℚ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ ≤ Fintype.card R := by
    simpa using hi.fintype_card_le_finrank
  have hns : ¬ Function.Surjective a := by
    intro hs
    apply hdep
    let e := Equiv.ofBijective a ⟨ha,hs⟩
    have hh := hi.comp e.symm e.symm.injective
    have he : (v ∘ a) ∘ e.symm=v := by
      funext i
      change v (e (e.symm i))=v i
      rw [e.apply_symm_apply]
    rw [he] at hh
    exact hh
  simp only [Function.Surjective,not_forall,not_exists] at hns
  obtain ⟨w,hw⟩ := hns
  let A : Matrix R κ ℤ := fun r c => V r (a c)
  let wv : R → ℤ := fun r => V r w
  let B := A.transpose*A
  let D := B.det
  let b := B.cramer (A.transpose*ᵥwv)
  have hAi : LinearIndependent ℚ (fun c r => (A r c:ℚ)) := hi
  have hwm : (fun r => (wv r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c r => (A r c:ℚ))) := by
    change v w ∈ Submodule.span ℚ (Set.range (v ∘ a))
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self w)
  have hD : D ≠ 0 := gram_det_ne_zero A hAi
  have heq : ∀ r, (A*ᵥb) r=D*wv r := gram_span_relation A wv hAi hwm
  have hbnd := gram_coefficient_bit_bound (Fintype.card R) (Fintype.card κ) L hcard
  have hAb : ∀ r c, |A r c| ≤ (2:ℤ)^L := fun r c => hV r (a c)
  have hwv : ∀ r, |wv r| ≤ (2:ℤ)^L := fun r => hV r w
  have hDb : |D| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    (gram_det_bound A _ (by positivity) hAb).trans hbnd
  have hbb : ∀ c, |b c| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    fun c => (gram_cramer_bound A wv _ (by positivity) hAb hwv c).trans hbnd
  let a' : Option κ → Ω := fun k => k.elim w a
  let z : Option κ → ℤ := fun k => k.elim D (fun c => -b c)
  refine ⟨Option κ,inferInstance,a',z,?_,?_,⟨none,hD⟩,?_,?_⟩
  · intro c d he
    cases c with
    | none =>
      cases d with
      | none => rfl
      | some d => exact False.elim (hw d he.symm)
    | some c =>
      cases d with
      | none => exact False.elim (hw c he)
      | some d => exact congrArg some (ha he)
  · simp only [Fintype.card_option]
    omega
  · intro k
    cases k with
    | none => exact hDb
    | some c => simpa only [z,Option.elim_some,abs_neg] using hbb c
  · intro r
    rw [Fintype.sum_option]
    change D*wv r+(∑ c, (-b c)*A r c)=0
    have hh := heq r
    change (∑ c, A r c*b c)=D*wv r at hh
    simp only [neg_mul,sum_neg_distrib,mul_comm (b _) (A _ _)]
    rw [hh]
    ring

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianKernel
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem lift_nonzero {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) (hz : ∃ j, z j ≠ 0) : ∃ j, lift A p z j ≠ 0 := by
  obtain ⟨j,hj⟩ := hz
  exact ⟨p.succAbove j, by simpa only [lift,Fin.insertNth_apply_succAbove] using hj⟩

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalScaling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalScaling
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem denominator_pos (q : Ω → ℚ) : 0 < denominator q := by
  apply prod_pos
  intro i _
  exact_mod_cast (q i).den_pos

end MetricKMedian.RationalScaling

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedIntegerKernel
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def computedIntegerKernel (r n : ℕ) (V : Fin r → Fin n → ℤ) : Fin n → ℤ :=
  let A := tabulate (fun i j => (V i j:ℚ))
  let q := kernelVector r n A
  let b := Vector.ofFn (RationalScaling.numerator (fun j => q[j.val]))
  fun j => b[j.val]

end MetricKMedian.Gaussian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_FinsetVectorExtension
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset

theorem extendVector_at {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (i : Fin s.card) : extendVector s z ((s.orderIsoOfFin rfl) i).val=z i := by
  have hi := ((s.orderIsoOfFin rfl) i).property
  simp only [extendVector,dite_eq_left hi]
  congr 1
  exact (s.orderIsoOfFin rfl).symm_apply_apply i

theorem extendVector_zero {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (i : Fin n) (hi : i ∉ s) : extendVector s z i=0 := dite_eq_right hi

theorem extendVector_sum {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (g : Fin n → ℤ) :
    (∑ i, extendVector s z i*g i)=∑ j, z j*g ((s.orderIsoOfFin rfl) j).val := by
  let e := (s.orderIsoOfFin rfl).toEquiv
  calc
    _ = ∑ i ∈ s, extendVector s z i*g i := by
      symm
      apply sum_subset (subset_univ _)
      intro i _ hi
      rw [extendVector_zero s z i hi,zero_mul]
    _ = ∑ i : s, extendVector s z i.val*g i.val := by
      exact (sum_coe_sort s (fun i => extendVector s z i*g i)).symm
    _ = ∑ j, extendVector s z (e j).val*g (e j).val := (e.sum_comp _).symm
    _ = _ := by
      apply sum_congr rfl
      intro j _
      rw [show extendVector s z (e j).val=z j from extendVector_at s z j]
      rfl

theorem extendVector_bound {n : ℕ} (s : Finset (Fin n)) (z : Fin s.card → ℤ)
    (H : ℤ) (hH : 0 ≤ H) (hz : ∀ j, |z j| ≤ H) (i : Fin n) :
    |extendVector s z i| ≤ H := by
  by_cases hi : i ∈ s
  · simp only [extendVector,dite_eq_left hi]; exact hz _
  · rw [extendVector_zero s z i hi,abs_zero]; exact hH

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedAffineKernel
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

def computedAffineKernel {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℤ) : Fin n → ℤ :=
  let zi := Gaussian.computedIntegerKernel (d+1) μ.support.card (activeMatrix μ v)
  let z := Vector.ofFn (Compression.extendVector μ.support zi)
  fun i => z[i.val]

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_RationalIntegerLaw
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.eliminateAt_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.RationalLaw
open Finset
variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

def integer (μ : RationalLaw Ω) : IntegerLaw Ω where
  denominator := RationalScaling.denominator μ.weight
  denominator_pos := RationalScaling.denominator_pos μ.weight
  numerator := RationalScaling.numerator μ.weight
  numerator_nonneg i := by
    have hh : (0:ℚ) ≤ (RationalScaling.numerator μ.weight i:ℚ) := by
      rw [RationalScaling.numerator_cast]
      exact mul_nonneg (μ.nonneg i) (by exact_mod_cast (RationalScaling.denominator_pos μ.weight).le)
    exact_mod_cast hh
  total := by
    apply Int.cast_injective (α:=ℚ)
    rw [Int.cast_sum]
    simp only [RationalScaling.numerator_cast,← sum_mul,μ.total,one_mul]

@[simp] theorem integer_weight (μ : RationalLaw Ω) (i : Ω) :
    μ.integer.rational.weight i=μ.weight i := by
  change (RationalScaling.numerator μ.weight i:ℚ)/(RationalScaling.denominator μ.weight:ℚ)=_
  rw [RationalScaling.numerator_cast,mul_div_cancel_right₀]
  exact_mod_cast (RationalScaling.denominator_pos μ.weight).ne'

@[simp] theorem integer_numerator_zero (μ : RationalLaw Ω) (i : Ω) :
    μ.integer.numerator i=0 ↔ μ.weight i=0 := by
  have hD : (RationalScaling.denominator μ.weight:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos μ.weight).ne'
  change RationalScaling.numerator μ.weight i=0 ↔ _
  rw [← Int.cast_eq_zero (α:=ℚ),RationalScaling.numerator_cast,mul_eq_zero,or_iff_left hD]

end MetricKMedian.RationalLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_IntegerBranching
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerBranching
open Finset
variable {n : ℕ}

def branchNumerator (p : Fin n → ℚ) (i : Fin n) (b : Fin 2) : ℤ :=
  if b=0 then RationalScaling.numerator p i
    else RationalScaling.denominator p-RationalScaling.numerator p i

theorem branchNumerator_nonneg (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin n) (b : Fin 2) :
    0 ≤ branchNumerator p i b := by
  have hD : (0:ℚ) < RationalScaling.denominator p := by
    exact_mod_cast RationalScaling.denominator_pos p
  have hA0 : (0:ℤ) ≤ RationalScaling.numerator p i := by
    have hh := mul_nonneg (hp i).1 hD.le
    rw [← RationalScaling.numerator_cast] at hh
    exact_mod_cast hh
  have hA1 : RationalScaling.numerator p i ≤ RationalScaling.denominator p := by
    have hh := mul_le_mul_of_nonneg_right (hp i).2 hD.le
    rw [one_mul,← RationalScaling.numerator_cast] at hh
    exact_mod_cast hh
  dsimp only [branchNumerator]
  split_ifs
  · exact hA0
  · exact sub_nonneg.mpr hA1

def branch (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : IntegerLaw (Fin n × Fin 2) where
  denominator := μ.denominator*RationalScaling.denominator p
  denominator_pos := mul_pos μ.denominator_pos (RationalScaling.denominator_pos p)
  numerator := let v := Vector.ofFn (fun i => Vector.ofFn (fun b =>
    μ.numerator i*branchNumerator p i b))
    fun a => v[a.1.val][a.2.val]
  numerator_nonneg a := by
    simp only [Vector.getElem_ofFn]
    exact mul_nonneg (μ.numerator_nonneg _) (branchNumerator_nonneg p hp _ _)
  total := by
    simp only [Vector.getElem_ofFn,Fin.eta]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,branchNumerator]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    simp only [mul_sub,add_sub_cancel,← sum_mul,μ.total]

end MetricKMedian.IntegerBranching

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalNearestCopies
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                             
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α : Type} [LinearOrder α]

theorem takeNearest_spec (d : α → ℚ) (k : ℕ) (U : Finset α) (hk : k ≤ U.card) :
    takeNearest d k U ⊆ U ∧ (takeNearest d k U).card=k ∧
    ∀ S : Finset α, S ⊆ U → S.card=k → (∑ a∈takeNearest d k U,d a) ≤ ∑ a∈S,d a := by
  induction k generalizing U with
  | zero =>
    simp only [takeNearest,empty_subset,card_empty,true_and,sum_empty]
    intro S _ hS
    simp [card_eq_zero.mp hS]
  | succ k ih =>
    have hU : U.Nonempty := card_pos.mp (by omega)
    let a := least U d hU
    have ha : a∈U := (least_spec U d hU).1
    have hamin : ∀ b∈U, d a ≤ d b := (least_spec U d hU).2
    have hk' : k ≤ (U.erase a).card := by rw [card_erase_of_mem ha]; omega
    obtain ⟨hsub,hcard,hmin⟩ := ih (U.erase a) hk'
    have han : a∉takeNearest d k (U.erase a) := fun h => (mem_erase.mp (hsub h)).1 rfl
    simp only [takeNearest,dite_eq_left hU]
    change insert a (takeNearest d k (U.erase a)) ⊆ U ∧ _
    refine ⟨insert_subset ha (hsub.trans (erase_subset _ _)),?_,?_⟩
    · rw [card_insert_of_notMem han,hcard]
    · intro S hSU hSk
      rw [sum_insert han]
      by_cases haS : a∈S
      · have hsubS : S.erase a ⊆ U.erase a := erase_subset_erase a hSU
        have hSc : (S.erase a).card=k := by rw [card_erase_of_mem haS,hSk]; omega
        have hh := hmin _ hsubS hSc
        have he := sum_erase_add S d haS
        linarith only [hh,he]
      · have hS : S.Nonempty := card_pos.mp (by omega)
        obtain ⟨b,hb⟩ := hS
        have hsubS : S.erase b ⊆ U.erase a := by
          intro z hz
          have hzS := mem_of_mem_erase hz
          exact mem_erase.mpr ⟨fun he => haS (he ▸ hzS),hSU hzS⟩
        have hSc : (S.erase b).card=k := by rw [card_erase_of_mem hb,hSk]; omega
        have hh := hmin _ hsubS hSc
        have he := sum_erase_add S d hb
        have hd := hamin b (hSU hb)
        linarith only [hh,he,hd]

end MetricKMedian.Preparation.RationalNearest
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseIntegerLaw
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
open Finset

structure SparseIntegerLaw (α : Type) where
  length : ℕ
  states : Vector α length
  law : IntegerLaw (Fin length)

namespace SparseIntegerLaw
variable {α : Type}

def moment (μ : SparseIntegerLaw α) (f : α → ℚ) : ℚ :=
  ∑ i : Fin μ.length, μ.law.rational.weight i*f μ.states[i.val]

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseAlgorithm
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

def branch (μ : SparseIntegerLaw α) (p : α → ℚ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) (next : α → Fin 2 → α) : SparseIntegerLaw α where
  length := μ.length*2
  states := Vector.ofFn (fun i => next
    μ.states[(finProdFinEquiv.symm i).1.val] (finProdFinEquiv.symm i).2)
  law := (IntegerBranching.branch μ.law (fun i => p μ.states[i.val])
    (fun i => hp μ.states[i.val])).reindex finProdFinEquiv

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMarginalTools
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α : Type}

 def dirac (a : α) : SparseIntegerLaw α where
  length := 1
  states := Vector.replicate 1 a
  law := {
    denominator := 1
    denominator_pos := by norm_num
    numerator := fun _ => 1
    numerator_nonneg := fun _ => by norm_num
    total := by simp }

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRealLaw
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
namespace RationalLaw
variable {α : Type} [Fintype α]

noncomputable def real (μ : RationalLaw α) : FiniteLaw α where
  weight a := (μ.weight a:ℝ)
  nonneg a := by exact_mod_cast μ.nonneg a
  total := by exact_mod_cast μ.total

@[simp] theorem real_expect (μ : RationalLaw α) (f : α → ℚ) :
    μ.real.expect (fun a => (f a:ℝ))=((∑ a, μ.weight a*f a:ℚ):ℝ) := by
  simp only [FiniteLaw.expect,real,Rat.cast_sum,Rat.cast_mul]

end RationalLaw

namespace SparseIntegerLaw
variable {α : Type}

noncomputable def realIndex (μ : SparseIntegerLaw α) : FiniteLaw (Fin μ.length) :=
  μ.law.rational.real

@[simp] theorem realIndex_expect (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.realIndex.expect (fun i => (f μ.states[i.val]:ℝ))=(μ.moment f:ℝ) := by
  exact μ.law.rational.real_expect (fun i => f μ.states[i.val])

noncomputable def real [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) : FiniteLaw α :=
  μ.realIndex.map (fun i => μ.states[i.val])

@[simp] theorem real_expect [Fintype α] [DecidableEq α] (μ : SparseIntegerLaw α) (f : α → ℚ) :
    μ.real.expect (fun a => (f a:ℝ))=(μ.moment f:ℝ) := by
  rw [real,FiniteLaw.expect_map,realIndex_expect]

end SparseIntegerLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseMap
attribute [-simp] _root_.OAI.MetricKMedian.SparseIntegerLaw.realIndex_expect _root_.OAI.MetricKMedian.SparseIntegerLaw.real_expect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
variable {α β : Type}

def map (μ : SparseIntegerLaw α) (f : α → β) : SparseIntegerLaw β where
  length := μ.length
  law := μ.law
  states := μ.states.map f

@[simp] theorem map_states (μ : SparseIntegerLaw α) (f : α → β) (i : Fin (μ.map f).length) :
    (μ.map f).states[i.val]=f μ.states[i.val] := by
  simp only [map,Vector.getElem_map]

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset
variable {F : Type} [LinearOrder F] [Fintype F] {Δ : ℕ}

local instance instLinearOrderCopy_r69a2ca_1 : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder
abbrev Payload (F : Type) [LinearOrder F] (Δ : ℕ) (g β : ℚ) :=
  (A : Finset (CopyState.Copy (F := F) Δ)) × RationalBatchData.Event A g β

abbrev State (F : Type) [LinearOrder F] (Δ : ℕ) (g β : ℚ) :=
  Finset (CopyState.Copy (F := F) Δ) × Option (Payload F Δ g β)

end MetricKMedian.RationalPhysicalKernel
end
end

end OAI
end


