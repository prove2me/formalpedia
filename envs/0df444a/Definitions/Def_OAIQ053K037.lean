-- Prove2me | Definitions.Def_OAIQ053K037
-- name    : OAIQ053K037
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T06:02:19.046179+00:00
-- url     : https://prove2.me/theorems/588427f0-61d8-4f4f-a4db-9f01f2fda9a1
-- title:
--   Definitions bundle OAIQ053K037 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 29 declarations of OpenAI's Lean: 20 definitions and 9 theorems. The definitions and types are `OAI.MetricKMedian.RationalPhysicalKernel.rationalHistoryValidCopyOrder`, `OAI.MetricKMedian.Reduction.completionBranches`, `OAI.MetricKMedian.Reduction.completionSet`, `OAI.MetricKMedian.Reduction.deleteStep`, `OAI.MetricKMedian.Reduction.deletionEndpoints`, `OAI.MetricKMedian.Reduction.deletionHistory`, `OAI.MetricKMedian.Reduction.deletionValues`, `OAI.MetricKMedian.Reduction.eligible`, `OAI.MetricKMedian.Reduction.localChoice`, `OAI.MetricKMedian.Reduction.localWeight`, `OAI.MetricKMedian.Reduction.rationalDeleteStep`, `OAI.MetricKMedian.Reduction.rationalEligible`, `OAI.MetricKMedian.Reduction.rationalHistory`, `OAI.MetricKMedian.Reduction.rationalRadii`, `OAI.MetricKMedian.Reduction.reductionOutputs`, `OAI.MetricKMedian.Reduction.sparseOutcomes`, `OAI.MetricKMedian.SparseBernoulli.reference`, `OAI.MetricKMedian.SparseIntegerLaw.expectation`, `OAI.MetricKMedian.Taper.physicalGraphData`, `OAI.MetricKMedian.Taper.rationalRadius`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Geometry_RationalHistoryValid`, `KMedian_Probability_BernoulliRealTransfer`, `KMedian_Reduction_BudgetReduction`, `KMedian_Reduction_CompletionEnumeration`, `KMedian_Reduction_DeletionHistory`, `KMedian_Reduction_RationalDeletion`, `KMedian_Reduction_RationalLocalChoice`, `KMedian_Rounding_RationalPhysicalGraph`, `KMedian_Rounding_RationalTaper`, `KMedian_Rounding_RationalTaperAffine`, `KMedian_Rounding_RationalTaperCandidates`, `KMedian_Rounding_RationalTaperData`, `KMedian_Rounding_RationalWeightedInvariants`, `KMedian_Sparse_SparseCardinalRounding`, `KMedian_Sparse_SparseGraphReal`, `KMedian_Sparse_SparseRealExpectation`, `KMedian_Sparse_SparseReduction`.
--
--   **Imports.** It imports the published bundle `Def_KMedianThreshold`; the bundles `OAIQ053K015`, `OAIQ053K016`, `OAIQ053K017`, `OAIQ053K018`, `OAIQ053K021`, `OAIQ053K022`, `OAIQ053K023`, `OAIQ053K026` and `OAIQ053K027` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ053K053`; the statements `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s53`, `OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s53`, `OAI.MetricKMedian.Reduction.completion_branch_exists_s53`, `OAI.MetricKMedian.Reduction.reductionOutputs_success_s53` and `OAI.MetricKMedian.SparseBernoulli.count_variance_s53`; the proofs of `OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_s53`, `OAI.MetricKMedian.FixedBatch.RationalParameters.selectCompleted_spec_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_survival_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.histories_valid_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_count_tail_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53`, `OAI.MetricKMedian.RationalPhysicalKernel.step_survival_s53`, `OAI.MetricKMedian.Reduction.CloseCenters.completionSet_spec_s53`, `OAI.MetricKMedian.Reduction.completion_branch_exists_s53`, `OAI.MetricKMedian.Reduction.reductionOutputs_success_s53`, `OAI.MetricKMedian.SparseBernoulli.conditional_count_tail_s53`, `OAI.MetricKMedian.SparseBernoulli.count_variance_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.erasure_lower_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_error_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.marginal_le_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.prob_eq_s53`, `OAI.MetricKMedian.SparseEnumeratedBatch.relevant_generator_estimate_s53` and `OAI.MetricKMedian.SparseFixedCount.actual_count_tail_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_KMedianThreshold
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K016
import Definitions.Def_OAIQ053K017
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K021
import Definitions.Def_OAIQ053K022
import Definitions.Def_OAIQ053K023
import Definitions.Def_OAIQ053K026
import Definitions.Def_OAIQ053K027

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperAffine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset

variable {I : Type*} [Fintype I]

theorem mass_affine {P g t : ℚ} {d : I → ℚ} {x : ℝ} (hP : 0 < (P:ℝ))
    (ha : ∀ i, (x*(d i:ℝ) ≤ 1-(P:ℝ) ↔ t*d i ≤ 1-P))
    (hb : ∀ i, (1 ≤ x*(d i:ℝ) ↔ 1 ≤ t*d i)) :
    mass g P (fun i => (d i:ℝ)) x=(g:ℝ)*((A P d t:ℝ)-x*(B P d t:ℝ)) := by
  simp only [mass,marginal_affine hP (ha _) (hb _),A,B,Rat.cast_sum]
  simp only [mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperCandidates
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

theorem maximal_root_in_candidates (g P : ℚ) (d : I → ℚ)
    (hg : 0 < (g:ℝ)) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1)
    (r : ℝ) (hr : 0 < r) (hroot : mass g P (fun i => (d i:ℝ)) r=1)
    (hmax : ∀ u, 1 ≤ mass g P (fun i => (d i:ℝ)) u → u ≤ r) :
    ∃ q ∈ candidates g P d, (q:ℝ)=r := by
  classical
  by_cases heq : ∃ q ∈ breakpoints P d, (q:ℝ)=r
  · obtain ⟨q,hq,he⟩ := heq
    exact ⟨q,mem_union_left _ hq,he⟩
  have hnot : ∀ q ∈ breakpoints P d, (q:ℝ) ≠ r := by simpa only [not_exists,not_and] using heq
  have hU : r < (upper d:ℝ) := by
    by_contra hn
    have hh := mass_antitone (d := fun i => (d i:ℝ)) hg.le hP (fun i => by exact_mod_cast hd i) (le_of_not_gt hn)
    rw [hroot,mass_upper g P d hP (by linarith) hd] at hh
    linarith
  obtain ⟨a,ha,b,hb,har,hrb,hgap⟩ := rational_bracket (breakpoints P d) r 0 (upper d)
    (mem_insert_self _ _) (mem_insert_of_mem (mem_insert_self _ _)) (by simpa only [Rat.cast_zero] using hr) hU hnot
  have hab : a < b := by exact_mod_cast har.trans hrb
  let t : ℚ := (a+b)/2
  have ht : a < t ∧ t < b := by dsimp only [t]; constructor <;> linarith
  have hPq : P < 1 := by exact_mod_cast (show (P:ℝ) < 1 by linarith)
  have hcuts := cuts_in_interval hd hPq a b t hgap ht r ⟨har,hrb⟩
  have haff := mass_affine (g := g) hP hcuts.1 hcuts.2
  rw [hroot] at haff
  have hB : B P d t ≠ 0 := by
    intro hz
    let u := (r+(b:ℝ))/2
    have hur : r < u := by dsimp only [u]; linarith
    have hu : (a:ℝ) < u ∧ u < (b:ℝ) := by dsimp only [u]; constructor <;> linarith
    have hcu := cuts_in_interval hd hPq a b t hgap ht u hu
    have hfu := mass_affine (g := g) hP hcu.1 hcu.2
    rw [hz,Rat.cast_zero,mul_zero,sub_zero] at hfu haff
    have hmass : mass g P (fun i => (d i:ℝ)) u=1 := hfu.trans haff.symm
    exact not_le_of_gt hur (hmax u hmass.ge)
  refine ⟨(A P d t-1/g)/B P d t,mem_union_right _ (mem_image.mpr ⟨(a,b),mem_product.mpr ⟨ha,hb⟩,rfl⟩),?_⟩
  have hBR : (B P d t:ℝ) ≠ 0 := by exact_mod_cast hB
  have hgR := hg.ne'
  push_cast
  apply (div_eq_iff hBR).mpr
  have hdiv : (A P d t:ℝ)-r*(B P d t:ℝ)=1/(g:ℝ) := (eq_div_iff hgR).mpr (by nlinarith [haff])
  linarith

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaper
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I]

theorem cast_rationalMass (g P : ℚ) (d : I → ℚ) (r : ℚ) :
    (rationalMass g P d r:ℝ)=mass g P (fun i => (d i:ℝ)) r := by
  simp only [rationalMass,mass,Rat.cast_sum,Rat.cast_mul,cast_rationalMarginal]

theorem inverseRadius_spec (g P : ℚ) (d : I → ℚ)
    (hg : 0 < (g:ℝ)) (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1) :
    0 < inverseRadius g P d ∧ rationalMass g P d (inverseRadius g P d)=1 ∧
      ∀ u : ℝ, 1 ≤ mass g P (fun i => (d i:ℝ)) u → u ≤ (inverseRadius g P d:ℝ) := by
  obtain ⟨r,hr,he,hmax⟩ := exists_minimal_radius (fun i => (d i:ℝ)) hg hP hP1
    (fun i => by exact_mod_cast hd i) htotal hcol
  obtain ⟨q,hq,hqr⟩ := maximal_root_in_candidates g P d hg hP hP1 hd hcol r hr he hmax
  have hqpos : 0 < q := by exact_mod_cast (hqr ▸ hr)
  have hqe : rationalMass g P d q=1 := by
    have hh : (rationalMass g P d q:ℝ)=1 := by rw [cast_rationalMass,hqr,he]
    exact_mod_cast hh
  have hmem : q ∈ rootCandidates g P d := mem_filter.mpr ⟨hq,hqpos,hqe⟩
  have hne : (rootCandidates g P d).Nonempty := ⟨q,hmem⟩
  have hm : inverseRadius g P d ∈ rootCandidates g P d := by
    unfold inverseRadius
    rw [dite_eq_left hne]
    exact max'_mem _ hne
  obtain ⟨_,hpos,hroot⟩ := mem_filter.mp hm
  refine ⟨hpos,hroot,?_⟩
  have hle : q ≤ inverseRadius g P d := by
    unfold inverseRadius
    rw [dite_eq_left hne]
    exact le_max' _ _ hmem
  have hleR : r ≤ (inverseRadius g P d:ℝ) := by rw [← hqr]; exact_mod_cast hle
  intro u hu
  exact (hmax u hu).trans hleR

theorem positive_data (g P : ℚ) (d : I → ℚ) (Δ : ℕ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hcol : colocatedMass g (fun i => (d i:ℝ)) < 1) :
    let r := inverseRadius g P d
    let q := fun i => rationalMarginal P (d i) r
    0 < 1/r ∧ (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∑ i, g*q i=1) ∧ (∑ i, q i=Δ) ∧
      (∀ i, d i=0 → q i=1) ∧
      (∀ i, q i < 1 → (1/r)*(1-P*q i) ≤ d i) ∧
      (∀ i, 0 < q i → d i ≤ (1/r)*(1-P*q i)) ∧
      (∀ R : ℝ, 0 < R → 1 ≤ mass g P (fun i => (d i:ℝ)) (1/R) → (1/r:ℚ) ≤ R) := by
  dsimp only
  let r := inverseRadius g P d
  let q := fun i => rationalMarginal P (d i) r
  obtain ⟨hr,he,hmax⟩ := inverseRadius_spec g P d hg hP hP1 hd htotal hcol
  have hrR : (0:ℝ) < r := by exact_mod_cast hr
  have hq : ∀ i, (q i:ℝ)=marginal P (d i) r := fun i => cast_rationalMarginal P (d i) r
  have hsum : (∑ i, q i)=(Δ:ℚ) := by
    apply mul_left_cancel₀ (show g ≠ 0 by exact_mod_cast hg.ne')
    rw [mul_sum]
    change rationalMass g P d r=g*(Δ:ℚ)
    rw [he]
    exact_mod_cast hunit.symm
  refine ⟨one_div_pos.mpr hr,?_,?_,he,hsum,?_,?_,?_,?_⟩
  · intro i
    have hh := marginal_nonneg (d := (d i:ℝ)) (r := (r:ℝ)) hP
    rw [← hq] at hh
    exact_mod_cast hh
  · intro i
    have hh := marginal_le_one (P:ℝ) (d i:ℝ) (r:ℝ)
    rw [← hq] at hh
    exact_mod_cast hh
  · intro i hi
    have hh : (q i:ℝ)=1 := by
      rw [hq,hi,Rat.cast_zero]
      exact marginal_at_zero_distance hP (by linarith)
    exact_mod_cast hh
  · intro i hi
    have hiR : marginal P (d i) r < 1 := by rw [← hq]; exact_mod_cast hi
    have hh := lower_comparison hP hiR
    have hres : (1/(r:ℝ))*(1-(P:ℝ)*(q i:ℝ)) ≤ (d i:ℝ) := by
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hrR).mpr
      rw [hq]
      nlinarith only [hh]
    exact_mod_cast hres
  · intro i hi
    have hiR : 0 < marginal P (d i) r := by rw [← hq]; exact_mod_cast hi
    have hh := upper_comparison hP hiR
    have hres : (d i:ℝ) ≤ (1/(r:ℝ))*(1-(P:ℝ)*(q i:ℝ)) := by
      rw [one_div_mul_eq_div]
      apply (le_div_iff₀ hrR).mpr
      rw [hq]
      nlinarith only [hh]
    exact_mod_cast hres
  · intro R hR hm
    have hh := (div_le_iff₀ hR).mp (hmax (1/R) hm)
    change ((1/r:ℚ):ℝ) ≤ R
    push_cast
    exact (div_le_iff₀ hrR).mpr (by nlinarith only [hh])

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalTaperData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type*} [Fintype I] [LinearOrder I]

def rationalRadius (g P : ℚ) (d : I → ℚ) : ℚ :=
  if 1 ≤ rationalColocatedMass g d then 0 else 1/inverseRadius g P d

theorem rational_data (g P : ℚ) (d : I → ℚ) (own : Finset I) (Δ : ℕ)
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i, 0 ≤ d i) (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hown : ∀ i ∈ own, d i=0) (howncard : own.card ≤ Δ) :
    let N := rationalRadius g P d
    let q := sourceMarginals g P d own Δ
    0 ≤ N ∧ (∀ i, 0 ≤ q i) ∧ (∀ i, q i ≤ 1) ∧
      (∑ i, g*q i=1) ∧ (∑ i, q i=Δ) ∧ (∀ i ∈ own, q i=1) ∧
      (∀ i, q i < 1 → N*(1-P*q i) ≤ d i) ∧
      (∀ i, 0 < q i → d i ≤ N*(1-P*q i)) ∧
      (∀ R : ℝ, 0 < R → 1 ≤ mass g P (fun i => (d i:ℝ)) (1/R) → (N:ℝ) ≤ R) := by
  by_cases hc : 1 ≤ rationalColocatedMass g d
  · have hcR : 1 ≤ colocatedMass g (fun i => (d i:ℝ)) := by
      rw [← cast_rationalColocatedMass]
      exact_mod_cast hc
    obtain ⟨hq0,hq1,hs,hn,ho,hz⟩ := zero_data g d own Δ hg hunit hcR hown howncard
    dsimp only
    simp only [rationalRadius,sourceMarginals,ite_eq_left hc]
    refine ⟨le_refl _,hq0,hq1,hs,hn,ho,?_,?_,?_⟩
    · intro i _; simpa only [zero_mul] using hd i
    · intro i hi; simp only [hz i hi,zero_mul,le_refl]
    · intro R hR _; simpa only [Rat.cast_zero] using hR.le
  · have hcR : colocatedMass g (fun i => (d i:ℝ)) < 1 := by
      rw [← cast_rationalColocatedMass]
      exact_mod_cast (lt_of_not_ge hc)
    obtain ⟨hN,hq0,hq1,hs,hn,ho,hl,hu,hr⟩ := positive_data g P d Δ hg hunit hP hP1 hd htotal hcR
    dsimp only
    simp only [rationalRadius,sourceMarginals,ite_eq_right hc]
    exact ⟨hN.le,hq0,hq1,hs,hn,fun i hi => ho i (hown i hi),hl,hu,hr⟩

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalWeightedInvariants
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.RationalWeightedStep
open Finset
variable {n : ℕ}

theorem endpoint_pair (β : Fin n → ℚ) (hβ : ∀ i, 0 < β i)
    (p : Vector ℚ n) (k l : Fin n) (hkl : k ≠ l) :
    probability β p*(point (endpoint β p 0) k*point (endpoint β p 0) l)+
      (1-probability β p)*(point (endpoint β p 1) k*point (endpoint β p 1) l) ≤
        point p k*point p l := by
  by_cases h : 1 < (fractional p).card
  · let a := pair p h
    let r := β a.val.1/β a.val.2
    have hr : 0 < r := div_pos (hβ _) (hβ _)
    have hu := up_pos p _ _ r hr a.property.1 a.property.2.1
    have hd := down_pos p _ _ r hr a.property.1 a.property.2.1
    have hrr : (0:ℝ) ≤ r := by exact_mod_cast hr.le
    have hur : (0:ℝ) < up p a.val.1 a.val.2 r := by exact_mod_cast hu
    have hdr : (0:ℝ) < down p a.val.1 a.val.2 r := by exact_mod_cast hd
    have hh := WeightedRounding.endpoint_pair (realPoint p) a.val.1 a.val.2 hkl hrr hur hdr
    simp only [probability,endpoint,dite_eq_left h]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,Rat.cast_div,
      ← real_move,← real_up,← real_down,← Rat.cast_neg,realPoint] using hh
  · simp only [probability,endpoint,dite_eq_right h,zero_mul,sub_zero,one_mul,zero_add,le_refl]

end MetricKMedian.RationalWeightedStep
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseCardinalRounding
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseCardinalRounding
open Finset RationalWeightedStep
variable {n : ℕ}

theorem integral_of_small_fractional (q : Vector ℚ n)
    (hq : ∀ i, 0 ≤ point q i ∧ point q i ≤ 1) (K : ℕ)
    (hs : (∑ i, point q i)=(K:ℚ)) (hf : (fractional q).card ≤ 1) :
    ∀ i, point q i=0 ∨ point q i=1 := by
  have has : MarginalRounding.fractional (realPoint q)=∅ := by
    by_contra h
    obtain ⟨i,hi⟩ := nonempty_iff_ne_empty.mpr h
    have h0 : ∀ i, 0 ≤ realPoint q i := fun i => by
      dsimp only [realPoint]; exact_mod_cast (hq i).1
    have h1 : ∀ i, realPoint q i ≤ 1 := fun i => by
      dsimp only [realPoint]; exact_mod_cast (hq i).2
    have hsum : (∑ i, realPoint q i)=(K:ℝ) := by
      dsimp only [realPoint]; exact_mod_cast hs
    obtain ⟨j,hj,hji⟩ := MarginalRounding.second_fractional h0 h1 hsum hi
    rw [real_fractional] at hi hj
    exact hji (card_le_one.mp hf j hj i hi)
  intro i
  apply RationalLastFraction.nonfractional q hq i
  rw [← real_fractional,has]
  exact notMem_empty i

end MetricKMedian.SparseCardinalRounding
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Rounding_RationalPhysicalGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Taper
open Finset
variable {I : Type} [LinearOrder I] [Fintype I] {n : ℕ} {X : Type*} [PseudoMetricSpace X]

noncomputable def physicalGraphData (Δ : ℕ) (g P : ℚ) (d : I → I → ℚ)
    (location : I → X) (own : I → Finset (I))
    (hg : 0 < (g:ℝ)) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : 0 < (P:ℝ)) (hP1 : (P:ℝ) ≤ 1/2)
    (hd : ∀ i h, 0 ≤ d i h) (hdist : ∀ i h, dist (location i) (location h)=(d i h:ℝ))
    (htotal : 1 ≤ ∑ _i : I, (g:ℝ))
    (hown : ∀ i h, h∈own i → d i h=0) (howncard : ∀ i, (own i).card ≤ Δ) :
    GraphData Δ (g:ℝ) (P:ℝ) location own where
  radius i := (rationalRadius g P (d i):ℝ)
  marginal h i := (sourceMarginals g P (d i) (own i) Δ h:ℝ)
  radius_nonneg i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).1
  marginal_nonneg h i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.1 h
  marginal_le_one h i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.1 h
  incoming_mass i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.1
  incoming_count i := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.1
  own_certain i h he := by
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.1 h he
  lower h i he := by
    rw [hdist]
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.1 h (by exact_mod_cast he)
  upper h i he := by
    rw [hdist]
    exact_mod_cast (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.2.1 h (by exact_mod_cast he)
  minimal i R hR he := by
    simp only [hdist] at he
    exact (rational_data g P (d i) (own i) Δ hg hunit hP hP1 (hd i) htotal (hown i) (howncard i)).2.2.2.2.2.2.2.2 R hR he

end MetricKMedian.Taper
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliRealTransfer
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n : ℕ}

noncomputable def reference (p : Fin n → ℚ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    FiniteLaw (Fin n → Bool) :=
  FiniteLaw.bernoulli (fun i => (p i:ℝ))
    (fun i => by exact_mod_cast (hp i).1) (fun i => by exact_mod_cast (hp i).2)

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseRealExpectation
attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.AlphabetReduction.paddedNodeFintype _root_.OAI.MetricKMedian.PCP.AlphabetReduction.positionFintype _root_.OAI.MetricKMedian.PCP.LocalRelation.sampleFintype _root_.OAI.MetricKMedian.PCP.Tableau.BoundedList.instFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseIntegerLaw
open Finset
variable {α β : Type}

noncomputable def expectation (μ : SparseIntegerLaw α) (f : α → ℝ) : ℝ :=
  μ.realIndex.expect (fun i => f μ.states[i.val])

end MetricKMedian.SparseIntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_RationalHistoryValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential
variable {F J X : Type} [LinearOrder F] [Fintype F] [Fintype J] [DecidableEq J]
  [PseudoMetricSpace X] {Δ : ℕ}
local instance rationalHistoryValidCopyOrder : LinearOrder (CopyState.Copy (F := F) Δ) := copyOrder

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalLocalChoice
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def localWeight (I : Instance) (r : Fin I.n → ℚ) (B : Finset (Fin I.n))
    (t a : Fin I.n) : ℚ :=
  ∑ j ∈ rationalRegion I r t, rationalNearest I j (insert a B)

def localChoice (I : Instance) (F B : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) (t : Fin I.n) : Finset (Fin I.n) :=
  pickSingleton (rationalCandidates I F r δ t) (localWeight I r B t)

def completionSet (I : Instance) (F B G : Finset (Fin I.n)) (r : Fin I.n → ℚ)
    (δ : ℚ) : Finset (Fin I.n) :=
  B ∪ G.biUnion (localChoice I F B r δ)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_CompletionEnumeration
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalRadii (I : Instance) (U : Finset (Fin I.n)) (t : Fin I.n) : ℚ :=
  rationalNearest I t (U.erase t)

def completionBranches (I : Instance) (F U : Finset (Fin I.n)) (δ : ℚ) (b : ℕ) :
    Finset (Finset (Fin I.n)) :=
  ((deletionChoices U b) ×ˢ (deletionChoices F b)).image
    (fun p => completionSet I F p.2 (U \ p.1) (rationalRadii I U) δ)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_DeletionHistory
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def deletionValues (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : Finset ℚ :=
  (deletionChoices T c).biUnion (fun D => T.image (fun i =>
    rationalCost I ((T \ D).erase i)-rationalCost I (T \ D)))

noncomputable def eligible (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) : Finset (Fin I.n) := by
  classical
  exact U.filter (fun i => ((rationalCost I (U.erase i)-rationalCost I U:ℚ):ℝ) ≤ B)

noncomputable def deleteStep (I : Instance) (B : ℝ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  if I.k < U.card then
    if h : (eligible I B U).Nonempty then U.erase ((eligible I B U).min' h) else U
  else U

noncomputable def deletionHistory (I : Instance) (B : ℝ) (T : Finset (Fin I.n)) :
    ℕ → Finset (Fin I.n)
  | 0 => T
  | t+1 => deleteStep I B (deletionHistory I B T t)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_RationalDeletion
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def rationalEligible (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  U.filter (fun i => rationalCost I (U.erase i)-rationalCost I U ≤ B)

def rationalDeleteStep (I : Instance) (B : ℚ) (U : Finset (Fin I.n)) : Finset (Fin I.n) :=
  if I.k < U.card then
    if h : (rationalEligible I B U).Nonempty then U.erase ((rationalEligible I B U).min' h) else U
  else U

def rationalHistory (I : Instance) (B : ℚ) (T : Finset (Fin I.n)) : ℕ → Finset (Fin I.n)
  | 0 => T
  | t+1 => rationalDeleteStep I B (rationalHistory I B T t)

def deletionEndpoints (I : Instance) (T : Finset (Fin I.n)) (c : ℕ) : Finset (Finset (Fin I.n)) :=
  (insert 0 (deletionValues I T c)).image (fun r => rationalHistory I r T c)

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseReduction
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Reduction
open Finset

def sparseOutcomes (I : Instance) (F T : Finset (Fin I.n)) (δ : ℚ) (c b : ℕ) :
    Finset (Finset (Fin I.n)) :=
  insert T ((deletionEndpoints I T c).biUnion (fun U => insert U (completionBranches I F U δ b)))

end MetricKMedian.Reduction
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Reduction_BudgetReduction
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

namespace Reduction

def reductionOutputs (pseudo : (I : Instance) → Finset (Fin I.n)) (I : Instance)
    (δ : ℚ) (c a b : ℕ) : Finset (Finset (Fin I.n)) :=
  (sparseBranches I I.facilities a).biUnion (fun F =>
    if hF : I.k ≤ F.card then sparseOutcomes I F (pseudo (I.restrictFacilities F hF)) δ c b
    else ∅)

end Reduction
end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseGraphReal
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqEqs _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
attribute [-simp] _root_.OAI.MetricKMedian.SparseEnumeratedGraph.mem_lift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseGraph
open Finset
variable {n m : ℕ}

@[simp] theorem cast_edge (G : Graph n m) (h : Fin n) (i : Fin m) :
    (edge G h i:ℝ)=GraphLaw.edge G h i := by
  by_cases he : h∈G i <;> simp [edge,GraphLaw.edge,he]

end MetricKMedian.SparseGraph
end
end

end OAI
end


