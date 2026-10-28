-- Prove2me | Definitions.Def_OAIQ035K004
-- name    : OAIQ035K004
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:53:29.979572+00:00
-- url     : https://prove2.me/theorems/26833d51-86c2-4cea-b8e6-4bb874727b55
-- title:
--   Definitions bundle OAIQ035K004 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 57 declarations of OpenAI's Lean: 30 definitions, 2 inductive types or structures, 2 instances and 23 theorems. The definitions and types are `OAI.MetricKMedian.CopyState.selectedSources`, `OAI.MetricKMedian.CountGeometry.overlap`, `OAI.MetricKMedian.CountStatistic.bit`, `OAI.MetricKMedian.CountStatistic.statistic`, `OAI.MetricKMedian.FiniteComparison.average`, `OAI.MetricKMedian.FiniteComparison.d`, `OAI.MetricKMedian.FiniteComparison.endpoint`, `OAI.MetricKMedian.FiniteComparison.kappa`, `OAI.MetricKMedian.FiniteComparison.psi`, `OAI.MetricKMedian.FiniteComparison.rawRow`, `OAI.MetricKMedian.FiniteGraph.conflicts`, `OAI.MetricKMedian.FiniteGraph.incoming`, `OAI.MetricKMedian.FiniteGraph.touching`, `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.bernoulli`, `OAI.MetricKMedian.FiniteLaw.bind`, `OAI.MetricKMedian.FiniteLaw.coinWeight`, `OAI.MetricKMedian.FiniteLaw.expect`, `OAI.MetricKMedian.FiniteLaw.prob`, `OAI.MetricKMedian.FiniteLaw.variance`, `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram.Raw`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.heavyParent`, `OAI.MetricKMedian.FixedBatch.internal`, `OAI.MetricKMedian.FixedBatch.nextAliveAt`, `OAI.MetricKMedian.FixedBatch.physical`, `OAI.MetricKMedian.FixedBatch.relevant`, `OAI.MetricKMedian.PhysicalPotential.retained`, `OAI.MetricKMedian.ScalarTransfer.bit`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_FiniteAverages`, `KMedian_Analysis_RowComparison`, `KMedian_Analysis_ScalarTransfer`, `KMedian_Compression_GramDependence`, `KMedian_Geometry_FixedBatchTransition`, `KMedian_Geometry_SortedListEncoding`, `KMedian_Preparation_PreparationMoments`, `KMedian_Probability_BernoulliBatches`, `KMedian_Probability_FiniteClipping`, `KMedian_Probability_FiniteKernels`, `KMedian_Probability_FiniteLaws`, `KMedian_Probability_FiniteVariance`, `KMedian_Probability_ProbabilitySupport`, `KMedian_Process_CopyRound`, `KMedian_Process_CountGeometry`, `KMedian_Process_FiniteGraph`, `KMedian_Process_ForceBatchBound`, `KMedian_Process_HeavyActions`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_QuadraticCount`, `KMedian_Process_RoundCountsProgram`, `KMedian_Process_SourceGenerator`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K015`, `OAIQ035K016`, `OAIQ035K017`, `OAIQ035K019`, `OAIQ035K020`, `OAIQ035K021`, `OAIQ035K024`, `OAIQ035K025`, `OAIQ035K026`, `OAIQ035K036` and `OAIQ035K044`; the statements `OAI.MetricKMedian.CountStatistic.variance_bound`, `OAI.MetricKMedian.FiniteLaw.restricted_moments`, `OAI.MetricKMedian.FixedBatch.full_relevant_bound`, `OAI.MetricKMedian.FixedBatch.heavy_relevant_bound`, `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift`, `OAI.MetricKMedian.Preparation.bundle_subset_moments`, `OAI.MetricKMedian.Preparation.support_repaired_cost` and `OAI.MetricKMedian.WeightedRounding.exact_law`; the proofs of `OAI.MetricKMedian.CountStatistic.variance_bound`, `OAI.MetricKMedian.FixedBatch.full_relevant_bound`, `OAI.MetricKMedian.FixedBatch.heavy_relevant_bound`, `OAI.MetricKMedian.Preparation.bundle_subset_moments` and `OAI.MetricKMedian.Preparation.support_repaired_cost`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_FiniteAverages
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

noncomputable def psi (p q : ℝ) : ℝ := (1 - q) / (1 - p * q)

noncomputable def kappa (p s q : ℝ) : ℝ :=
  (1 - p * s) * psi p q - (1 - q)

end MetricKMedian.FiniteComparison

namespace MetricKMedian.FiniteComparison

noncomputable def average {I : Type*} [Fintype I] (π f : I → ℝ) : ℝ :=
  ∑ i, π i * f i

noncomputable def d (s : Bool) : ℝ := if s then 2 / 5 else 13 / 25

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_RowComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FiniteComparison

noncomputable def rawRow {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m y s D R : ℝ) : ℝ :=
  (1 - p * s) * (1 - average π q) * R +
    average π q * (m * D + (2 - s) * p * y * (D + 1)) -
    (1 - p * s) * (D + 1) -
    average π (fun t => (1 - q t) * max (Z t - (1 + m + 2 * p * y) * D) 0)

noncomputable def endpoint (s : Bool) : ℝ := if s then 1 else 0

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_ScalarTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ScalarTransfer

noncomputable def bit (s : Bool) : ℝ := if s then 1 else 0

end MetricKMedian.ScalarTransfer


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Compression_GramDependence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

theorem gram_det_ne_zero (A : Matrix R C ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ))) :
    (A.transpose*A).det ≠ 0 := by
  intro hz
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hzero : A*ᵥv=0 := by
    have hh := congrArg (dotProduct v) hker
    rw [← mulVec_mulVec,dotProduct_mulVec,dotProduct_zero,vecMul_transpose,
      dotProduct_self_eq_zero] at hh
    exact hh
  have hlin : Function.Injective ((fun r c => (A r c:ℚ)) *ᵥ ·) :=
    Matrix.mulVec_injective_iff.mpr hi
  have hcast : (fun r c => (A r c:ℚ))*ᵥ(fun c => (v c:ℚ))=0 := by
    ext r
    have hh := congrFun hzero r
    change (∑ c, A r c*v c)=0 at hh
    change (∑ c, (A r c:ℚ)*(v c:ℚ))=0
    exact_mod_cast hh
  have hvQ := hlin (hcast.trans (mulVec_zero _).symm)
  apply hv
  ext c
  have hh := congrFun hvQ c
  change (v c:ℚ)=0 at hh
  change v c=0
  exact_mod_cast hh

theorem gram_span_relation (A : Matrix R C ℤ) (w : R → ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ)))
    (hc : (fun r => (w r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c => fun r => (A r c:ℚ)))) :
    let B := A.transpose*A
    let z := B.cramer (A.transpose*ᵥw)
    ∀ r, (A*ᵥz) r=B.det*w r := by
  let AQ : Matrix R C ℚ := fun r c => A r c
  have hc' : (fun r => (w r:ℚ)) ∈ LinearMap.range AQ.mulVecLin := by
    rwa [Matrix.range_mulVecLin]
  obtain ⟨x,hx⟩ := hc'
  change AQ*ᵥx=(fun r => (w r:ℚ)) at hx
  let B := A.transpose*A
  let z := B.cramer (A.transpose*ᵥw)
  have hz := Matrix.mulVec_cramer B (A.transpose*ᵥw)
  have hdet : B.det ≠ 0 := gram_det_ne_zero A hi
  have hB : Function.Injective ((fun c d => (B c d:ℚ))*ᵥ ·) := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit (((Int.castRingHom ℚ).mapMatrix B).det)
    rw [← RingHom.map_det (Int.castRingHom ℚ)]
    apply isUnit_iff_ne_zero.mpr
    change (B.det:ℚ) ≠ 0
    exact_mod_cast hdet
  have hBcast : (fun c d => (B c d:ℚ))=AQ.transpose*AQ := by
    exact Matrix.map_mul (L:=A.transpose) (M:=A) (f:=Int.castRingHom ℚ)
  have hzQ : (AQ.transpose*AQ)*ᵥ(fun c => (z c:ℚ))=(B.det:ℚ) •
      (AQ.transpose*ᵥ(fun r => (w r:ℚ))) := by
    rw [← hBcast]
    ext c
    have hh := congrFun hz c
    simp only [mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] at hh ⊢
    change (∑ d, (B c d:ℚ)*(z d:ℚ))=(B.det:ℚ)*∑ r, (A r c:ℚ)*(w r:ℚ)
    change (∑ d, B c d*z d)=B.det*∑ r, A r c*w r at hh
    exact_mod_cast hh
  have he : (fun c => (z c:ℚ))=(B.det:ℚ) • x := by
    apply hB
    change ((fun c d => (B c d:ℚ))*ᵥ(fun c => (z c:ℚ))) =
      (fun c d => (B c d:ℚ))*ᵥ((B.det:ℚ) • x)
    rw [hBcast,hzQ,mulVec_smul,← mulVec_mulVec,hx]
  change ∀ r, (A*ᵥz) r=B.det*w r
  intro r
  have heq : (AQ*ᵥ(fun c => (z c:ℚ))) r=(B.det:ℚ)*(w r:ℚ) := by
    rw [he,mulVec_smul,hx]
    rfl
  simp only [mulVec,dotProduct,AQ] at heq ⊢
  exact_mod_cast heq

end MetricKMedian.Compression

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

variable {I : Type*}

noncomputable def retained (a dh : ℝ) (d : I → ℝ) (physicalSurvivors : Finset I) : Finset I :=
  physicalSurvivors.filter (fun i => a * d i < dh)

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FixedBatchTransition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

structure Actions (I E : Type*) [DecidableEq I] [DecidableEq E] where
  source : E → I
  erase : E → Finset I
  ordinary : Finset E

noncomputable def relevant (D : Actions I E) (S : Finset I) : Finset E :=
  univ.filter (fun e => (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty)

noncomputable def physical (D : Actions I E) (S : Finset I) (A : Finset E) : Finset I :=
  S \ A.biUnion D.erase

noncomputable def internal (D : Actions I E) (S : Finset I) (A : Finset E) : Finset E :=
  (A ∩ relevant D S).filter (fun e => e ∈ D.ordinary ∧ D.source e ∈ S)

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_SortedListEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.EncodingLists
open Finset

theorem sorted_enum {α : Type} [LinearOrder α] (s : Finset α) :
    List.ofFn (fun i : Fin s.card => (s.orderIsoOfFin rfl i).val)=s.sort := by
  rw [List.ofFn_eq_map]
  exact s.listMap_orderEmbOfFin_finRange rfl

theorem filter_range {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    (List.finRange n).filter (fun i => decide (p i))=(univ.filter p).sort := by
  apply List.SortedLT.eq_of_mem_iff
  · exact ((List.sortedLT_finRange n).pairwise.filter _).sortedLT
  · exact (univ.filter p).sortedLT_sort
  · intro i
    simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,mem_sort,mem_filter,mem_univ]

theorem map_filter_enum {n : ℕ} {α : Type} (f : Fin n → α) (p : Fin n → Prop) [DecidablePred p] :
    ((List.finRange n).filter (fun i => decide (p i))).map f =
      List.ofFn (fun i : Fin (univ.filter p).card => f ((univ.filter p).orderIsoOfFin rfl i).val) := by
  rw [filter_range,← sorted_enum,List.map_ofFn]
  rfl

end MetricKMedian.EncodingLists
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
noncomputable def expect (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ := ∑ ω, μ.weight ω * f ω
noncomputable def prob (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : ℝ :=
  μ.expect (fun ω => if E ω then 1 else 0)

theorem expect_mono (μ : FiniteLaw Ω) {f h : Ω → ℝ} (hfh : ∀ ω, f ω ≤ h ω) :
    μ.expect f ≤ μ.expect h := by
  exact Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hfh ω) (μ.nonneg ω))

theorem expect_nonneg (μ : FiniteLaw Ω) {f : Ω → ℝ} (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ μ.expect f := by
  exact Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) (hf ω))

theorem expect_const (μ : FiniteLaw Ω) (c : ℝ) : μ.expect (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, μ.total, one_mul]

theorem expect_add (μ : FiniteLaw Ω) (f h : Ω → ℝ) :
    μ.expect (fun ω => f ω + h ω) = μ.expect f + μ.expect h := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem expect_sub (μ : FiniteLaw Ω) (f h : Ω → ℝ) :
    μ.expect (fun ω => f ω - h ω) = μ.expect f - μ.expect h := by
  simp only [expect, mul_sub, Finset.sum_sub_distrib]

theorem expect_mul (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => c * f ω) = c * μ.expect f := by
  simp only [expect, ← Finset.mul_sum, mul_left_comm]

theorem expect_sum (μ : FiniteLaw Ω) {I : Type*} (s : Finset I) (f : Ω → I → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f ω i) = ∑ i ∈ s, μ.expect (fun ω => f ω i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteVariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def variance (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  μ.expect (fun ω => (f ω-μ.expect f)^2)

omit [Fintype Ξ] in
theorem variance_eq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f=μ.expect (fun ω => (f ω)^2)-(μ.expect f)^2 := by
  unfold variance
  have hp : ∀ ω, (f ω-μ.expect f)^2=(f ω)^2-2*μ.expect f*f ω+(μ.expect f)^2 := by
    intro ω; ring
  simp_rw [hp, expect_add, expect_sub, expect_mul, expect_const]
  ring

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_ProbabilitySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

omit [Fintype Ξ] in
 theorem expect_mono_support (μ : FiniteLaw Ω) {f h : Ω → ℝ}
    (hfh : ∀ ω, 0 < μ.weight ω → f ω ≤ h ω) : μ.expect f ≤ μ.expect h := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : 0 < μ.weight ω
  · exact mul_le_mul_of_nonneg_left (hfh ω hp) (μ.nonneg ω)
  · rw [le_antisymm (le_of_not_gt hp) (μ.nonneg ω), zero_mul, zero_mul]

omit [Fintype Ξ] in
 theorem expect_congr_support (μ : FiniteLaw Ω) {f h : Ω → ℝ}
    (hfh : ∀ ω, 0 < μ.weight ω → f ω=h ω) : μ.expect f=μ.expect h := by
  exact le_antisymm (μ.expect_mono_support (fun ω hω => (hfh ω hω).le))
    (μ.expect_mono_support (fun ω hω => (hfh ω hω).ge))

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_PreparationMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

omit [Fintype I] in
 theorem adjacent_variance (μ : FiniteLaw Ω) (X : Ω → ℝ) {m q : ℝ}
    (hm : 0 ≤ m) (hx : ∀ ω, 0 < μ.weight ω → X ω=m ∨ X ω=m+1)
    (hmean : μ.expect X=q) : μ.variance X ≤ q := by
  have hsq : μ.expect (fun ω => (X ω)^2)=(2*m+1)*q-m*(m+1) := by
    calc
      _ = μ.expect (fun ω => (2*m+1)*X ω-m*(m+1)) := by
        apply μ.expect_congr_support
        intro ω hω
        rcases hx ω hω with h | h <;> rw [h] <;> ring
      _ = _ := by rw [expect_sub, expect_mul, expect_const, hmean]
  rw [variance_eq, hsq, hmean]
  nlinarith only [sq_nonneg (q-m), hm]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliBatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
namespace FiniteLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

def coinWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

@[simp] theorem coinWeight_true (p : ℝ) : coinWeight p true = p := rfl
@[simp] theorem coinWeight_false (p : ℝ) : coinWeight p false = 1-p := rfl

theorem coinWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (b : Bool) :
    0 ≤ coinWeight p b := by cases b <;> simp [hp, hp1, sub_nonneg]

@[simp] theorem coinWeight_total (p : ℝ) : ∑ b : Bool, coinWeight p b = 1 := by
  simp

noncomputable def bernoulli (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    FiniteLaw (I → Bool) where
  weight ω := ∏ i, coinWeight (p i) (ω i)
  nonneg ω := Finset.prod_nonneg (fun i _ => coinWeight_nonneg (hp i) (hp1 i) (ω i))
  total := by rw [← Fintype.prod_sum]; simp

end FiniteLaw
end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteClipping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω I : Type*} [Fintype Ω] [Fintype I]

theorem half_clip_point {z m : ℝ} (hm : m ≤ 1/4) :
    z-min z (1/2) ≤ 4*(z-m)^2 := by
  by_cases hz : z ≤ 1/2
  · rw [min_eq_left hz, sub_self]
    positivity
  · rw [min_eq_right (le_of_not_ge hz)]
    nlinarith only [hm, sq_nonneg (2*(z-m)-1/4)]

omit [Fintype I] in
 theorem expected_half_clip (μ : FiniteLaw Ω) (Z : Ω → ℝ)
    {v : ℝ} (hmean : μ.expect Z ≤ 1/4) (hvar : μ.variance Z ≤ v) :
    μ.expect (fun ω => Z ω-min (Z ω) (1/2)) ≤ 4*v := by
  have he := μ.expect_mono (fun ω => half_clip_point (z := Z ω) hmean)
  rw [expect_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left hvar (by norm_num))

theorem abs_clip_le {z c b : ℝ} (hcb : c ≤ b) : |c-min z b| ≤ |c-z| := by
  by_cases hz : z ≤ b
  · rw [min_eq_left hz]
  · rw [min_eq_right (le_of_not_ge hz), abs_of_nonpos (sub_nonpos.mpr hcb),
      abs_of_nonpos (sub_nonpos.mpr (hcb.trans (le_of_not_ge hz)))]
    linarith only [hz]

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) : FiniteLaw Ξ where
  weight ξ := ∑ ω, μ.weight ω*(κ ω).weight ξ
  nonneg ξ := Finset.sum_nonneg (fun ω _ => mul_nonneg (μ.nonneg ω) ((κ ω).nonneg ξ))
  total := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.total, mul_one]

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_FiniteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteGraph

variable {I H : Type*} [Fintype H] [DecidableEq I] [DecidableEq H]

noncomputable def incoming (E : H → Finset I) (i : I) : Finset H :=
  Finset.univ.filter (fun h => i ∈ E h)

noncomputable def touching (E : H → Finset I) (S : Finset I) : Finset H :=
  S.biUnion (incoming E)

noncomputable def conflicts (E : H → Finset I) (balanced : Finset H) (h : H) : Finset H :=
  (touching E (E h) ∩ balanced).erase h

end MetricKMedian.FiniteGraph
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_SourceGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

noncomputable def graphActions (G : I → Finset I) : Actions I I where
  source := id
  erase := fun h => univ.filter (fun i => h ∈ G i)
  ordinary := univ

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_HeavyActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I : Type*} [DecidableEq I] [Fintype I]

abbrev HeavyAction (Full : Actions I I) (H : Finset I) :=
  {h : I // h ∉ H} ⊕ {p : I × I // p.1 ∈ H ∧ p.2 ∈ Full.erase p.1}

instance instFintypeHeavyAction (Full : Actions I I) (H : Finset I) : Fintype (HeavyAction Full H) := by
  unfold HeavyAction
  infer_instance

instance instDecidableEqHeavyAction (Full : Actions I I) (H : Finset I) : DecidableEq (HeavyAction Full H) := by
  unfold HeavyAction
  infer_instance

def heavyParent (Full : Actions I I) (H : Finset I) : HeavyAction Full H → I
  | .inl h => h
  | .inr p => p.val.1

noncomputable def heavyActions (Full : Actions I I) (H : Finset I) : Actions I (HeavyAction Full H) := by
  classical
  exact {
    source := fun e => Full.source (heavyParent Full H e)
    erase := Sum.elim (fun h => Full.erase h) (fun p => {p.val.2})
    ordinary := univ.filter (fun e : HeavyAction Full H => e.isLeft = true) }

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CopyRound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] (Δ : ℕ)

variable {Δ}

noncomputable def selectedSources {I : Type*} [Fintype I] [DecidableEq I]
    (G : I → Finset I) (H : Finset I) (Z : Finset (HeavyAction (graphActions G) H)) : Finset I :=
  H ∪ (Z ∩ (heavyActions (graphActions G) H).ordinary).image
    (heavyActions (graphActions G) H).source

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_QuadraticCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountStatistic
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def bit (ω : I → Bool) (i : I) : ℝ := if ω i then 1 else 0
noncomputable def statistic (b : I → ℝ) (c : I → I → ℝ) (ω : I → Bool) : ℝ :=
  (∑ i, b i*bit ω i)+(1/2)*∑ i, ∑ j, c i j*bit ω i*bit ω j

end MetricKMedian.CountStatistic
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_CountGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CountGeometry
open Finset
variable {E U : Type*} [Fintype E] [DecidableEq E] [DecidableEq U]

def overlap (S : E → Finset U) (e f : E) : ℕ :=
  if e=f then 0 else (S e ∩ S f).card

end MetricKMedian.CountGeometry
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ForceBatchBound
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

noncomputable def nextAliveAt (D : Actions I E) (a : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : Finset I :=
  if h : (internal D S A).Nonempty then
    retained a (d (D.source h.choose)) d (physical D S A)
  else physical D S A

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_RoundCountsProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                          
section
namespace MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
open Finset
variable {τ : ℝ}
abbrev Raw := List Unit × ((List (List ℚ) × List (List ℚ)) × List ℕ)
end MetricKMedian.FixedBatch.RationalParameters.RoundCountsProgram
end

end OAI
end


