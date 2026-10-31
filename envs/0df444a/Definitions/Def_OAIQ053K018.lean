-- Prove2me | Definitions.Def_OAIQ053K018
-- name    : OAIQ053K018
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-31T05:56:04.815222+00:00
-- url     : https://prove2.me/theorems/7c549150-1107-4f60-a47f-91509df8326d
-- title:
--   Definitions bundle OAIQ053K018 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 51 declarations of OpenAI's Lean: 21 definitions and 30 theorems. The definitions and types are `OAI.MetricKMedian.CopyState.roundErased`, `OAI.MetricKMedian.CopyState.roundOpened`, `OAI.MetricKMedian.CopyState.selectedSources`, `OAI.MetricKMedian.FiniteComparison.actualB`, `OAI.MetricKMedian.FiniteLaw.bernoulli`, `OAI.MetricKMedian.FiniteLaw.condition`, `OAI.MetricKMedian.FiniteLaw.joint`, `OAI.MetricKMedian.FiniteLaw.prob`, `OAI.MetricKMedian.FiniteLaw.variance`, `OAI.MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram.Input.raw`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.internal`, `OAI.MetricKMedian.FixedBatch.nextAliveAt`, `OAI.MetricKMedian.FixedBatch.physical`, `OAI.MetricKMedian.FixedBatch.relevant`, `OAI.MetricKMedian.Gaussian.ListOperation.Frame`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Rows`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.representatives`, `OAI.MetricKMedian.Preparation.RationalRepresentatives.select`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.branchLawData`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics, in whole or in part: `KMedian_Analysis_FiniteComparison`, `KMedian_Compression_AffineListOperations`, `KMedian_Compression_ComputedElimination`, `KMedian_Compression_GaussianListMachine`, `KMedian_Geometry_FixedBatchTransition`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_TrimIntegerLaw`, `KMedian_Preparation_PreparationMoments`, `KMedian_Preparation_PreparedScanProgram`, `KMedian_Preparation_RationalRepresentatives`, `KMedian_Probability_BernoulliBatches`, `KMedian_Probability_Conditioning`, `KMedian_Probability_FiniteClipping`, `KMedian_Probability_FiniteJoint`, `KMedian_Probability_FiniteKernels`, `KMedian_Probability_FiniteLaws`, `KMedian_Probability_FiniteVariance`, `KMedian_Probability_ProbabilitySupport`, `KMedian_Process_CopyRound`, `KMedian_Process_ForceBatchBound`, `KMedian_Process_HeavyActions`, `KMedian_Process_SourceGenerator`, `KMedian_Sparse_SparseBernoulliFeatures`, `KMedian_Sparse_SparseBernoulliSubsets`, `KMedian_Sparse_SparseBranchProgram`.
--
--   **Imports.** It imports the bundles `OAIQ053K000`, `OAIQ053K001`, `OAIQ053K002`, `OAIQ053K003`, `OAIQ053K004`, `OAIQ053K005` and `OAIQ053K006` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ053K031`, `OAIQ053K032`, `OAIQ053K033`, `OAIQ053K034`, `OAIQ053K036` and `OAIQ053K037`; the statements `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`, `OAI.MetricKMedian.CountStatistic.variance_bound_s53`, `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53`, `OAI.MetricKMedian.FixedBatch.masked_total_bound_s53`, `OAI.MetricKMedian.FixedBatch.post_force_bound_s53` and `OAI.MetricKMedian.PhysicalPotential.expected_time_advance_s53`; the proofs of `OAI.MetricKMedian.CopyState.balanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_count_change_s53`, `OAI.MetricKMedian.CopyState.unbalanced_small_change_s53`, `OAI.MetricKMedian.CountStatistic.variance_bound_s53`, `OAI.MetricKMedian.FiniteComparison.actual_scalar_bounds_s53`, `OAI.MetricKMedian.FiniteComparison.finite_comparison_s53`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound_s53`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum_s53`, `OAI.MetricKMedian.FixedBatch.masked_total_bound_s53`, `OAI.MetricKMedian.FixedBatch.post_force_bound_s53`, `OAI.MetricKMedian.GeneratorAverage.expanded_bound_s53` and `OAI.MetricKMedian.PhysicalPotential.expected_time_advance_s53`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K002
import Definitions.Def_OAIQ053K003
import Definitions.Def_OAIQ053K004
import Definitions.Def_OAIQ053K005
import Definitions.Def_OAIQ053K006

section
-- module Solutions.OAIQ053_KM.KMedian_Analysis_FiniteComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

open Analytic

noncomputable def actualB (x w : ℝ) (s : Bool) : ℝ :=
  (2-ScalarTransfer.bit s)*P x*(x+w)

end MetricKMedian.FiniteComparison

end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_GaussianListMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.Gaussian.ListOperation
open Binary Binary.PolyProgram Function
abbrev Frame := ℕ × Row
end MetricKMedian.Gaussian.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_AffineListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Gaussian
open Finset
abbrev Rows := Binary.IntegerList.Rows

end MetricKMedian.IntegerLaw.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Compression_ComputedElimination
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
attribute [-simp] _root_.OAI.MetricKMedian.IntegerLaw.trim_denominator _root_.OAI.MetricKMedian.IntegerLaw.trim_numerator _root_.OAI.MetricKMedian.IntegerLaw.trim_weight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem eliminateAt_preserves {n d : ℕ} (μ : IntegerLaw (Fin n))
    (v : Fin n → Fin d → ℚ) (z : Fin n → ℤ) (p : Fin n)
    (hp : 0 < z p) (hmin : ∀ i, 0 < z i → ratio μ z p ≤ ratio μ z i)
    (hzsum : ∑ i, z i=0) (hzmoment : ∀ j, ∑ i, (z i:ℚ)*v i j=0)
    (hzsupport : ∀ i, μ.numerator i=0 → z i=0) :
    let ν := eliminateAt μ z p hp hmin hzsum
    ν.numerator p=0 ∧ μ.numerator p ≠ 0 ∧
      (∀ i, μ.numerator i=0 → ν.numerator i=0) ∧
      ν.support ⊆ μ.support.erase p ∧
      ∀ j, (∑ i, ν.rational.weight i*v i j)=∑ i, μ.rational.weight i*v i j := by
  dsimp only
  have hz : (eliminateAt μ z p hp hmin hzsum).numerator p=0 := by
    rw [eliminateAt_numerator,sub_self]
  have hn : μ.numerator p ≠ 0 := by intro hp0; exact hp.ne' (hzsupport p hp0)
  have hs : ∀ i, μ.numerator i=0 → (eliminateAt μ z p hp hmin hzsum).numerator i=0 := by
    intro i hi
    rw [eliminateAt_numerator,hi,hzsupport i hi]
    ring
  refine ⟨hz,hn,hs,?_,?_⟩
  · intro i hi
    have hni := (mem_support _ i).mp hi
    apply mem_erase.mpr
    refine ⟨?_,(μ.mem_support i).mpr ?_⟩
    · intro he; subst i; exact hni hz
    · intro he; exact hni (hs i he)
  · intro j
    have hD : (μ.denominator:ℚ) ≠ 0 := by exact_mod_cast μ.denominator_pos.ne'
    have hpQ : (z p:ℚ) ≠ 0 := by exact_mod_cast hp.ne'
    change (∑ i, (((eliminateAt μ z p hp hmin hzsum).numerator i:ℚ)/
        ((μ.denominator*z p:ℤ):ℚ))*v i j)=_
    simp only [eliminateAt_numerator,Int.cast_mul,Int.cast_sub]
    have heq : ∀ i, (((μ.numerator i:ℚ)*(z p:ℚ)-(μ.numerator p:ℚ)*(z i:ℚ))/
        ((μ.denominator:ℚ)*(z p:ℚ)))*v i j=
        ((μ.numerator i:ℚ)*v i j)/(μ.denominator:ℚ)-
        ((μ.numerator p:ℚ)/(μ.denominator:ℚ)/(z p:ℚ))*((z i:ℚ)*v i j) := by
      intro i
      field_simp
    simp only [heq,sum_sub_distrib,← mul_sum,hzmoment,mul_zero,sub_zero]
    apply sum_congr rfl
    intro i _
    dsimp only [rational]
    ring

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

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
-- module Solutions.OAIQ053_KM.KMedian_Geometry_IntegerBranching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset
variable {α β : Type} [Fintype α] [Fintype β]

theorem reindex_moment (μ : IntegerLaw α) (e : α ≃ β) (f : α → ℚ) :
    (∑ b, (μ.reindex e).rational.weight b*f (e.symm b))=
      ∑ a, μ.rational.weight a*f a := by
  exact e.symm.sum_comp (fun a => μ.rational.weight a*f a)

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Geometry_TrimIntegerLaw
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset

theorem trim_moment {n : ℕ} (μ : IntegerLaw (Fin n)) (f : Fin n → ℚ) :
    (∑ i, μ.trim.rational.weight i*f (μ.support.orderEmbOfFin rfl i))=
      ∑ i, μ.rational.weight i*f i := by
  simp only [trim_weight]
  calc
    _ = ∑ i : μ.support, μ.rational.weight i*f i :=
      Equiv.sum_comp (μ.support.orderIsoOfFin rfl).toEquiv _
    _ = ∑ i ∈ μ.support, μ.rational.weight i*f i := sum_coe_sort μ.support (fun i => μ.rational.weight i*f i)
    _ = _ := by
      apply sum_subset (subset_univ _)
      intro i _ hi
      have hz : μ.numerator i=0 := not_not.mp (by simpa only [mem_support] using hi)
      simp only [rational,hz,Int.cast_zero,zero_div,zero_mul]

end MetricKMedian.IntegerLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]
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

theorem expect_mul_right (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => f ω * c) = μ.expect f * c := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

theorem expect_sum (μ : FiniteLaw Ω) {I : Type*} (s : Finset I) (f : Ω → I → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f ω i) = ∑ i ∈ s, μ.expect (fun ω => f ω i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

theorem prob_mono (μ : FiniteLaw Ω) {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (hEF : ∀ ω, E ω → F ω) : μ.prob E ≤ μ.prob F := by
  apply μ.expect_mono
  intro ω
  split_ifs with he hf hf <;> try norm_num
  exact False.elim (hf (hEF ω he))

end FiniteLaw

end MetricKMedian

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteVariance
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
theorem variance_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) : 0 ≤ μ.variance f :=
  μ.expect_nonneg (fun _ => sq_nonneg _)

omit [Fintype Ξ] in
theorem variance_eq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    μ.variance f=μ.expect (fun ω => (f ω)^2)-(μ.expect f)^2 := by
  unfold variance
  have hp : ∀ ω, (f ω-μ.expect f)^2=(f ω)^2-2*μ.expect f*f ω+(μ.expect f)^2 := by
    intro ω; ring
  simp_rw [hp, expect_add, expect_sub, expect_mul, expect_const]
  ring

omit [Fintype Ξ] in
theorem sq_expect_le_expect_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    (μ.expect f)^2 ≤ μ.expect (fun ω => (f ω)^2) := by
  have hv := μ.variance_nonneg f
  rw [variance_eq] at hv
  linarith only [hv]

omit [Fintype Ξ] in

theorem prob_le_expect_div (μ : FiniteLaw Ω) (f : Ω → ℝ) {t : ℝ}
    (hf : ∀ ω, 0 ≤ f ω) (ht : 0 < t) :
    μ.prob (fun ω => t ≤ f ω) ≤ μ.expect f/t := by
  classical
  apply (le_div_iff₀ ht).mpr
  unfold prob
  rw [← expect_mul_right]
  apply μ.expect_mono
  intro ω
  split_ifs with h
  · simpa only [one_mul] using h
  · simpa only [zero_mul] using hf ω

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_ProbabilitySupport
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

omit [Fintype Ξ] in
 theorem prob_compl (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    μ.prob (fun ω => ¬E ω)=1-μ.prob E := by
  have hp : ∀ ω, (if ¬E ω then (1:ℝ) else 0)=1-(if E ω then 1 else 0) := by
    intro ω; split_ifs <;> simp_all
  simp only [prob, hp, expect_sub, expect_const]

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparationMoments
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
 theorem expect_abs_centered_le_sqrt (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.expect (fun ω => |X ω-μ.expect X|) ≤ Real.sqrt (μ.variance X) := by
  have hs := μ.sq_expect_le_expect_sq (fun ω => |X ω-μ.expect X|)
  simp only [sq_abs] at hs
  exact (Real.le_sqrt (μ.expect_nonneg (fun _ => abs_nonneg _)) (μ.variance_nonneg X)).mpr hs

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
-- module Solutions.OAIQ053_KM.KMedian_Process_SourceGenerator
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
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
-- module Solutions.OAIQ053_KM.KMedian_Process_HeavyActions
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
-- module Solutions.OAIQ053_KM.KMedian_Process_CopyRound
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

noncomputable def roundErased (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : Finset (Copy (F := F) Δ) :=
  (Z.biUnion (heavyActions (graphActions G) H).erase).image Subtype.val

noncomputable def roundOpened (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : Finset F :=
  (selectedSources G H Z).image (fun i => i.val.1)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Process_ForceBatchBound
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
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
-- module Solutions.OAIQ053_KM.KMedian_Probability_BernoulliBatches
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian
namespace FiniteLaw
variable {I : Type*} [Fintype I] [DecidableEq I]

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
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

theorem property_bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (R : Ξ → Prop)
    (hR : ∀ ω, 0 < μ.weight ω → ∀ ξ, 0 < (κ ω).weight ξ → R ξ) :
    ∀ ξ, 0 < (μ.bind κ).weight ξ → R ξ := by
  intro ξ hξ
  by_contra hn
  have hpoint : ∀ ω, μ.weight ω*(κ ω).weight ξ=0 := by
    intro ω
    by_cases hω : 0 < μ.weight ω
    · have hk : (κ ω).weight ξ=0 := by
        apply le_antisymm _ ((κ ω).nonneg ξ)
        by_contra hneg
        exact hn (hR ω hω ξ (lt_of_not_ge hneg))
      rw [hk, mul_zero]
    · rw [le_antisymm (le_of_not_gt hω) (μ.nonneg ω), zero_mul]
  have hz : (μ.bind κ).weight ξ=0 := Finset.sum_eq_zero (fun ω _ => hpoint ω)
  rw [hz] at hξ
  exact lt_irrefl _ hξ

theorem property_map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) (R : Ξ → Prop)
    (hR : ∀ ω, 0 < μ.weight ω → R (f ω)) :
    ∀ ξ, 0 < (μ.map f).weight ξ → R ξ := by
  apply property_bind
  intro ω hω ξ hξ
  by_cases heq : ξ=f ω
  · rw [heq]; exact hR ω hω
  · simp only [dirac, ite_eq_right heq] at hξ
    exact False.elim (lt_irrefl _ hξ)

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliFeatures
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem used_without (f : Fin d → Fin (n+1)) (i : Fin n) :
    used (without f i)=(used f).erase i := by
  ext x
  simp only [used,mem_filter,mem_univ,true_and,mem_erase]
  constructor
  · rintro ⟨a,ha⟩
    dsimp only [without] at ha
    split_ifs at ha with h
    · exact False.elim ((Nat.ne_of_gt x.isLt) ha)
    · refine ⟨?_,a,ha⟩
      intro he
      exact h (ha.trans (congrArg Fin.val he))
  · rintro ⟨hxi,a,ha⟩
    refine ⟨a,?_⟩
    dsimp only [without]
    rw [ite_eq_right (fun h => hxi (Fin.ext (ha.symm.trans h)))]
    exact ha

theorem monomial_endpoint (q : Fin n → Bool) (f : Fin d → Fin (n+1))
    (i : Fin n) (b : Fin 2) :
    monomial (endpoint q i b) f=
      if i ∈ used f then (if b=0 then 1 else 0)*monomial q (without f i)
      else monomial q f := by
  by_cases hi : i ∈ used f
  · rw [ite_eq_left hi]
    unfold monomial
    rw [used_without,← mul_prod_erase (used f) (flag (endpoint q i b)) hi]
    rw [flag_endpoint,ite_eq_left rfl]
    congr 1
    apply prod_congr rfl
    intro x hx
    rw [flag_endpoint,ite_eq_right (mem_erase.mp hx).1]
  · rw [ite_eq_right hi]
    unfold monomial
    apply prod_congr rfl
    intro x hx
    rw [flag_endpoint,ite_eq_right (fun (he : x=i) => hi (he ▸ hx))]

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBernoulliSubsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.SparseBernoulli
open Finset
variable {n d : ℕ}

theorem used_tuple (S : Finset (Fin n)) (hS : S.card ≤ d) : used (tuple (d := d) S)=S := by
  ext x
  simp only [used,mem_filter,mem_univ,true_and]
  constructor
  · rintro ⟨a,ha⟩
    dsimp only [tuple] at ha
    split_ifs at ha with h
    · have he : S.orderEmbOfFin rfl ⟨a.val,h⟩=x := Fin.ext ha
      rw [← he]
      exact orderEmbOfFin_mem _ _ _
    · exact False.elim ((Nat.ne_of_gt x.isLt) ha)
  · intro hx
    let a : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨x,hx⟩
    have ha : a.val < d := lt_of_lt_of_le a.isLt hS
    refine ⟨⟨a.val,ha⟩,?_⟩
    dsimp only [tuple]
    rw [dite_eq_left a.isLt]
    change (S.orderEmbOfFin rfl a).val=x.val
    have he := (S.orderIsoOfFin rfl).apply_symm_apply ⟨x,hx⟩
    exact congrArg (fun z : S => (z.val:Fin n).val) he

end MetricKMedian.SparseBernoulli

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_Conditioning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

noncomputable def condition (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P]
    (hP : 0 < μ.prob P) : FiniteLaw Ω where
  weight := fun ω => if P ω then μ.weight ω/μ.prob P else 0
  nonneg := fun ω => by split_ifs; exact div_nonneg (μ.nonneg ω) hP.le; exact le_rfl
  total := by
    have he : ∀ ω, (if P ω then μ.weight ω/μ.prob P else 0)=
        (μ.weight ω*(if P ω then 1 else 0))/μ.prob P := by
      intro ω; split_ifs <;> simp
    simp only [he, ← sum_div]
    change μ.prob P/μ.prob P=1
    exact div_self hP.ne'

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Sparse_SparseBranchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section

namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.PolyProgram Function
variable {α γ : Type}

def branchLawData (x : LawData × List ℚ) : LawData :=
  let D := IntegerList.denominator x.2
  let zs := IntegerList.numerators x.2
  (x.1.1*D,(x.1.2.zip zs).flatMap (fun z => [z.1*z.2,z.1*(D-z.2)]))

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_PreparedScanProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
open Finset Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (Row )
variable {τ : ℝ}
def Input.raw (x : Input) : Raw := ((List.replicate x.h (),List.ofFn (fun i => (x.orig i).val)),
  ((List.ofFn (fun i => List.ofFn (x.df i)),List.ofFn (fun c => List.ofFn (x.dc c))),
  (x.ns.map List.ofFn,x.budget)))
end MetricKMedian.FixedBatch.RationalParameters.PreparedScanProgram
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Preparation_RationalRepresentatives
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.Preparation.RationalRepresentatives
open Finset
variable {n : ℕ}

def select (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ) :
    ℕ → Finset (Fin n) → Finset (Fin n)
  | 0, _ => ∅
  | k+1, U => if hU : U.Nonempty then
      let s := firstNearest U V hU
      insert s (select d V M k (U.filter (fun j => M*V j < d j s)))
    else ∅

def representatives (d : Fin n → Fin n → ℚ) (V : Fin n → ℚ) (M : ℚ) : Finset (Fin n) :=
  select d V M n univ

end MetricKMedian.Preparation.RationalRepresentatives
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteClipping
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
 theorem nonneg_expect_zero_support (μ : FiniteLaw Ω) (X : Ω → ℝ)
    (hX : ∀ ω, 0 ≤ X ω) (hmean : μ.expect X=0) :
    ∀ ω, 0 < μ.weight ω → X ω=0 := by
  intro ω hω
  have hh := single_le_sum (s := univ) (f := fun ξ => μ.weight ξ*X ξ)
    (fun ξ _ => mul_nonneg (μ.nonneg ξ) (hX ξ)) (mem_univ ω)
  change μ.weight ω*X ω ≤ μ.expect X at hh
  rw [hmean] at hh
  exact le_antisymm (by nlinarith only [hh, hω]) (hX ω)

omit [Fintype I] in
 theorem expected_half_clip (μ : FiniteLaw Ω) (Z : Ω → ℝ)
    {v : ℝ} (hmean : μ.expect Z ≤ 1/4) (hvar : μ.variance Z ≤ v) :
    μ.expect (fun ω => Z ω-min (Z ω) (1/2)) ≤ 4*v := by
  have he := μ.expect_mono (fun ω => half_clip_point (z := Z ω) hmean)
  rw [expect_mul] at he
  exact he.trans (mul_le_mul_of_nonneg_left hvar (by norm_num))

theorem clipping_budget (μ : FiniteLaw Ω) (Z : I → Ω → ℝ) (c : I → ℝ)
    {g γ : ℝ} (hg : 0 ≤ g) (hγ : 0 < γ)
    (hc : ∀ i, 0 ≤ c i)
    (hmean : ∀ i, μ.expect (Z i) ≤ 1/4)
    (hvar : ∀ i, μ.variance (Z i) ≤ g*(1+γ)*c i) :
    1-4*g*(1+γ)/γ ≤ μ.prob (fun ω =>
      (∑ i, (Z i ω-min (Z i ω) (1/2))) ≤ γ*∑ i, c i) := by
  classical
  let W : Ω → ℝ := fun ω => ∑ i, (Z i ω-min (Z i ω) (1/2))
  have hW : ∀ ω, 0 ≤ W ω := by
    intro ω
    exact sum_nonneg (fun i _ => sub_nonneg.mpr (min_le_left _ _))
  have hE : μ.expect W ≤ 4*g*(1+γ)*∑ i, c i := by
    change μ.expect (fun ω => ∑ i, (Z i ω-min (Z i ω) (1/2))) ≤ _
    rw [expect_sum, mul_sum]
    exact sum_le_sum (fun i _ => (expected_half_clip μ (Z i) (hmean i) (hvar i)).trans_eq (by ring))
  have hC : 0 ≤ ∑ i, c i := sum_nonneg (fun i _ => hc i)
  have hρ : 0 ≤ 4*g*(1+γ)/γ := by positivity
  have hfail : μ.prob (fun ω => γ*∑ i, c i < W ω) ≤ 4*g*(1+γ)/γ := by
    rcases hC.eq_or_lt with hz | hz
    · have hzero : μ.expect W=0 := le_antisymm (by simpa only [← hz, mul_zero] using hE)
        (μ.expect_nonneg hW)
      have hs := μ.nonneg_expect_zero_support W hW hzero
      have he0 : μ.prob (fun ω => γ*∑ i, c i < W ω)=0 := by
        change μ.expect (fun ω => if γ*∑ i, c i < W ω then 1 else 0)=0
        calc
          _ = μ.expect (fun _ => 0) := μ.expect_congr_support (fun ω hω => by
            rw [hs ω hω, ← hz, mul_zero, ite_eq_right (lt_irrefl 0)])
          _ = 0 := μ.expect_const _
      rw [he0]
      exact hρ
    · have he := μ.prob_le_expect_div W hW (mul_pos hγ hz)
      have hp := μ.prob_mono (E := fun ω => γ*∑ i, c i < W ω)
        (F := fun ω => γ*∑ i, c i ≤ W ω) (fun _ h => h.le)
      calc
        _ ≤ μ.expect W/(γ*∑ i, c i) := hp.trans he
        _ ≤ (4*g*(1+γ)*∑ i, c i)/(γ*∑ i, c i) := div_le_div_of_nonneg_right hE (by positivity)
        _ = _ := by field_simp
  have hcomp := μ.prob_compl (fun ω => γ*∑ i, c i < W ω)
  simp only [not_lt] at hcomp
  change 1-4*g*(1+γ)/γ ≤ μ.prob (fun ω => W ω ≤ γ*∑ i, c i)
  rw [hcomp]
  linarith only [hfail]

omit [Fintype I] in
 theorem rescaling_noise (μ : FiniteLaw Ω) (Z : Ω → ℝ) {c γ g : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1/2) (hγ : 0 ≤ γ) (_hg : 0 ≤ g)
    (hmean : μ.expect Z=(1+γ)*c) (hvar : μ.variance Z ≤ g*(1+γ)*c) :
    μ.expect (fun ω => |c-min (Z ω) (1/2)|) ≤ γ*c+Real.sqrt (g*(1+γ)*c) := by
  have hp : ∀ ω, |c-min (Z ω) (1/2)| ≤ γ*c+|Z ω-μ.expect Z| := by
    intro ω
    calc
      _ ≤ |c-Z ω| := abs_clip_le hc1
      _ ≤ |c-μ.expect Z|+|μ.expect Z-Z ω| := by
        have he : c-Z ω=(c-μ.expect Z)+(μ.expect Z-Z ω) := by ring
        rw [he]
        exact abs_add_le _ _
      _ = γ*c+|Z ω-μ.expect Z| := by
        rw [hmean, abs_sub_comm ((1+γ)*c) (Z ω)]
        congr 1
        have he : c-(1+γ)*c= -(γ*c) := by ring
        rw [he, abs_neg, abs_of_nonneg (mul_nonneg hγ hc)]
  have he := μ.expect_mono hp
  simp only [expect_add, expect_const] at he
  exact he.trans (add_le_add_right ((μ.expect_abs_centered_le_sqrt Z).trans
    (Real.sqrt_le_sqrt hvar)) _)

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Probability_FiniteJoint
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def joint (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) : FiniteLaw (Ω × Ξ) where
  weight z := μ.weight z.1*(κ z.1).weight z.2
  nonneg z := mul_nonneg (μ.nonneg z.1) ((κ z.1).nonneg z.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, total, mul_one]

end MetricKMedian.FiniteLaw
end
end

end OAI
end


