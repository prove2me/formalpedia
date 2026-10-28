-- Prove2me | Definitions.Def_OAIQ035K021
-- name    : OAIQ035K021
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:56:56.338453+00:00
-- url     : https://prove2.me/theorems/0cb0c9ed-3613-41e0-a8db-2d101da62fb8
-- title:
--   Definitions bundle OAIQ035K021 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 49 declarations of OpenAI's Lean: 30 definitions and 19 theorems. The definitions and types are `OAI.MetricKMedian.FixedBatch.balancedActions`, `OAI.MetricKMedian.FixedBatch.balancedConflicts`, `OAI.MetricKMedian.FixedBatch.charge`, `OAI.MetricKMedian.FixedBatch.countErase`, `OAI.MetricKMedian.FixedBatch.countOpening`, `OAI.MetricKMedian.FixedBatch.nextAlive`, `OAI.MetricKMedian.FixedBatch.nextCap`, `OAI.MetricKMedian.FractionalDual.bestThreshold`, `OAI.MetricKMedian.FractionalDual.gradient`, `OAI.MetricKMedian.FractionalDual.value`, `OAI.MetricKMedian.GraphComparison.normalizedDrift`, `OAI.MetricKMedian.GraphComparison.unnormalizedDrift`, `OAI.MetricKMedian.LPBinary.Input.rows`, `OAI.MetricKMedian.LPBinary.Repair.Output`, `OAI.MetricKMedian.LPBinary.Rows`, `OAI.MetricKMedian.PhysicalPotential.potential`, `OAI.MetricKMedian.Preparation.RationalSuppliers.Program.SupplierRaw`, `OAI.MetricKMedian.Preparation.computedNearest`, `OAI.MetricKMedian.Preparation.fill`, `OAI.MetricKMedian.RationalBatchData.Ordinal.actionOrder`, `OAI.MetricKMedian.RationalBatchData.Ordinal.code`, `OAI.MetricKMedian.SparseCardinalRounding.Program.weightedInput`, `OAI.MetricKMedian.SparseGraph.Program.QInput.column`, `OAI.MetricKMedian.SparseGraph.Program.QInput.columns`, `OAI.MetricKMedian.SparseGraph.Program.emptyColumn`, `OAI.MetricKMedian.SparsePhysicalBatch.Program.Input.bernInput`, `OAI.MetricKMedian.TruncatedLP.gradient`, `OAI.MetricKMedian.TruncatedLP.objective`, `OAI.MetricKMedian.TruncatedLP.optimize`, `OAI.MetricKMedian.rationalNearest`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Geometry_FixedBatchTransition`, `KMedian_Geometry_GraphComparison`, `KMedian_Geometry_IntegerBranching`, `KMedian_Geometry_RationalInstanceCost`, `KMedian_Optimization_ApproximationListProgram`, `KMedian_Optimization_ComputedNearest`, `KMedian_Optimization_FractionalDual`, `KMedian_Optimization_LPBinaryInput`, `KMedian_Optimization_LPListFacts`, `KMedian_Optimization_SimplexDiameter`, `KMedian_Optimization_TruncatedObjective`, `KMedian_Optimization_TruncatedOptimization`, `KMedian_Preparation_SupplierListOperations`, `KMedian_Probability_BernoulliListOperations`, `KMedian_Probability_BernoulliRunProgram`, `KMedian_Process_ActualActions`, `KMedian_Process_AveragedDrift`, `KMedian_Process_BatchOrdinalCodes`, `KMedian_Process_PhysicalBatchProgram`, `KMedian_Process_PhysicalPotential`, `KMedian_Process_UnbalancedActions`, `KMedian_Programs_CardinalRoundProgram`, `KMedian_Programs_GraphLawProgram`, `KMedian_Sparse_SparseBindProgram`.
--
--   **Imports.** It imports the published bundle `Def_MetricKMedian`; the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004`, `OAIQ035K005`, `OAIQ035K006`, `OAIQ035K007`, `OAIQ035K008` and `OAIQ035K010` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K032`, `OAIQ035K033`, `OAIQ035K034`, `OAIQ035K036` and `OAIQ035K062`; the statements `OAI.MetricKMedian.Completion.Rational.output_potential`, `OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival`, `OAI.MetricKMedian.CopyState.rational_conditional_round_drift`, `OAI.MetricKMedian.CopyState.round_cap`, `OAI.MetricKMedian.CopyState.unbalanced_count_change`, `OAI.MetricKMedian.CopyState.unbalanced_small_change`, `OAI.MetricKMedian.FixedBatch.charge_bound`, `OAI.MetricKMedian.FixedBatch.count_action_size`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound`, `OAI.MetricKMedian.FixedBatch.heavy_charge_le`, `OAI.MetricKMedian.FixedBatch.ideal_local_lower`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum`, `OAI.MetricKMedian.FixedBatch.masked_total_bound`, `OAI.MetricKMedian.FixedBatch.post_force_bound`, `OAI.MetricKMedian.GeneratorAverage.expanded_bound`, `OAI.MetricKMedian.GraphComparison.unnormalized_drift_le`, `OAI.MetricKMedian.PhysicalPotential.expected_time_advance`, `OAI.MetricKMedian.PhysicalPotential.time_increase_le`, `OAI.MetricKMedian.RationalBatchData.proposal_local_bound`, `OAI_MetricKMedian_RationalPhysicalKernel_histories_completed_expectation`, `OAI_MetricKMedian_Reduction_reductionOutputs_success`, `OAI.MetricKMedian.SparseCopyState.physical_count_tail`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound` and `OAI.MetricKMedian.Taper.GraphData.drift`; the proofs of `OAI.MetricKMedian.Completion.Rational.output_potential`, `OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival`, `OAI.MetricKMedian.CopyState.rational_conditional_round_drift`, `OAI.MetricKMedian.CopyState.round_cap`, `OAI.MetricKMedian.CopyState.unbalanced_count_change`, `OAI.MetricKMedian.CopyState.unbalanced_small_change`, `OAI.MetricKMedian.FixedBatch.charge_bound`, `OAI.MetricKMedian.FixedBatch.count_action_size`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound`, `OAI.MetricKMedian.FixedBatch.heavy_charge_le`, `OAI.MetricKMedian.FixedBatch.ideal_local_lower`, `OAI.MetricKMedian.FixedBatch.masked_biased_linear_bound`, `OAI.MetricKMedian.FixedBatch.masked_mass_sum`, `OAI.MetricKMedian.FixedBatch.masked_total_bound`, `OAI.MetricKMedian.FixedBatch.post_force_bound`, `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift`, `OAI.MetricKMedian.GeneratorAverage.expanded_bound`, `OAI.MetricKMedian.GraphComparison.unnormalized_drift_le`, `OAI.MetricKMedian.PhysicalPotential.expected_time_advance`, `OAI.MetricKMedian.PhysicalPotential.time_increase_le`, `OAI.MetricKMedian.RationalBatchData.proposal_count_tail`, `OAI.MetricKMedian.RationalBatchData.proposal_local_bound`, `OAI.MetricKMedian.RationalBatchData.proposal_survival`, `OAI_MetricKMedian_RationalPhysicalKernel_histories_completed_expectation`, `OAI_MetricKMedian_Reduction_reductionOutputs_success`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound`, `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound` and `OAI.MetricKMedian.Taper.GraphData.drift`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005
import Definitions.Def_OAIQ035K006
import Definitions.Def_OAIQ035K007
import Definitions.Def_OAIQ035K008
import Definitions.Def_OAIQ035K010

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

open Analytic

noncomputable def potential {I : Type*} (x g : ℝ) (d : I → ℝ) (S : Finset I) (b : ℝ) : ℝ :=
  (1 + m x + B x * mass g S) * cost g d S + (1 - mass g S) * b

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FixedBatchTransition
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

noncomputable def nextAlive (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : Finset I :=
  if h : (internal D S A).Nonempty then
    retained (coefficient x (mass g S)) (d (D.source h.choose)) d (physical D S A)
  else physical D S A

noncomputable def nextCap (D : Actions I E) (d : I → ℝ) (bForce : ℝ) (A : Finset E) : ℝ :=
  (A ∩ D.ordinary).fold min bForce (fun e => d (D.source e))

noncomputable def charge (D : Actions I E) (x g b : ℝ) (d : I → ℝ) (S : Finset I) (e : E) : ℝ :=
  if e ∈ D.ordinary ∧ D.source e ∈ S then
    d (D.source e)-(∑ i ∈ S \ D.erase e, g*max (d (D.source e)-coefficient x (mass g S)*d i) 0)-
      potential x g d S b
  else
    mass g (S ∩ D.erase e)*min b (d (D.source e))-
      coefficient x (mass g S)*PhysicalPotential.cost g d (S ∩ D.erase e)-
      B x*mass g (S ∩ D.erase e)*(PhysicalPotential.cost g d S-PhysicalPotential.cost g d (S ∩ D.erase e))

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_GraphComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

noncomputable def normalizedDrift {I : Type*} [Fintype I]
    (π D N s : I → ℝ) (q K : I → I → ℝ) (x y pHat : ℝ) : ℝ :=
  -3-2*(P x*(y-x)^2/y)+average π (fun i =>
    (1-average π (q i))*(D i+(1-pHat*s i)*N i)+
    (1+m x+2*P x*y)*average π (q i)*D i+2*P x*y*average π (q i)+
    2*P x*average π (fun t => K i t*D t)-
    average π (fun t => (1-q i t)*max (D t-(1+m x+2*P x*y)*D i) 0))

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_IntegerBranching
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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalInstanceCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian
open Finset

def rationalNearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℚ :=
  if h : S.Nonempty then
    (S.image (I.distance j)).min' (h.image _)
  else 0

end MetricKMedian
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_FractionalDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FractionalDual
open Finset
variable {ι : Type} [Fintype ι]

theorem weak_duality (d y x : ι → ℚ) (τ : ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1) :
    affine d y τ ≤ ∑ i, x i*d i := by
  have ht : ∀ i, τ*x i-y i*max 0 (τ-d i) ≤ x i*d i := by
    intro i
    by_cases hi : τ ≤ d i
    · rw [max_eq_left (sub_nonpos.mpr hi),mul_zero,sub_zero,mul_comm τ]
      exact mul_le_mul_of_nonneg_left hi (hx i).1
    · rw [max_eq_right (sub_nonneg.mpr (le_of_not_ge hi))]
      have hh := mul_le_mul_of_nonneg_right (hx i).2 (sub_nonneg.mpr (le_of_not_ge hi))
      linarith
  have hs := sum_le_sum (fun i (_ : i ∈ univ) => ht i)
  simpa only [sum_sub_distrib,← mul_sum,hxs,mul_one,affine] using hs

theorem ordered_attains [DecidableEq ι] (d y x : ι → ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1)
    (ho : ∀ i a, 0 < x i → x a < y a → d i ≤ d a) :
    ∃ a, affine d y (d a)=∑ i, x i*d i := by
  let U := univ.filter (fun i => 0 < x i)
  have hU : U.Nonempty := by
    by_contra hn
    have hz : ∀ i, x i=0 := fun i => le_antisymm
      (le_of_not_gt (fun hp => hn ⟨i,mem_filter.mpr ⟨mem_univ _,hp⟩⟩)) (hx i).1
    simp only [hz,sum_const_zero] at hxs
    norm_num at hxs
  obtain ⟨a,ha,hmax⟩ := U.exists_max_image d hU
  refine ⟨a,?_⟩
  have hapos := (mem_filter.mp ha).2
  have hi : ∀ i, y i*max 0 (d a-d i)=x i*(d a-d i) := by
    intro i
    by_cases hl : d i < d a
    · have he : x i=y i := by
        apply le_antisymm (hx i).2
        exact le_of_not_gt (fun hlt => (not_le_of_gt hl) (ho a i hapos hlt))
      rw [he,max_eq_right (sub_nonneg.mpr hl.le)]
    · by_cases he : d i=d a
      · rw [he,sub_self,max_self,mul_zero,mul_zero]
      · have hlt : d a < d i := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm he)
        have hz : x i=0 := by
          apply le_antisymm _ (hx i).1
          exact le_of_not_gt (fun hp => (not_le_of_gt hlt)
            (hmax i (mem_filter.mpr ⟨mem_univ _,hp⟩)))
        rw [hz,zero_mul,max_eq_left (sub_nonpos.mpr hlt.le),mul_zero]
  unfold affine
  simp_rw [hi,mul_sub]
  rw [sum_sub_distrib,← sum_mul,hxs,one_mul]
  ring

def value (d y : ι → ℚ) (H : ℚ) : ℚ :=
  ((thresholds d H).image (affine d y)).max'
    ((insert_nonempty 0 _).image _)

theorem affine_le_value (d y : ι → ℚ) (H τ : ℚ) (hτ : τ ∈ thresholds d H) :
    affine d y τ ≤ value d y H :=
  le_max' _ _ (mem_image.mpr ⟨τ,hτ,rfl⟩)

theorem value_le_assignment (d y x : ι → ℚ) (H : ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ y i) (hxs : ∑ i, x i=1) :
    value d y H ≤ ∑ i, x i*d i := by
  apply max'_le
  intro q hq
  obtain ⟨τ,_,rfl⟩ := mem_image.mp hq
  exact weak_duality d y x τ hx hxs

def bestThreshold (d y : ι → ℚ) (H : ℚ) : ℚ :=
  let U := (thresholds d H).filter (fun τ => affine d y τ=value d y H)
  if h : U.Nonempty then U.max' h else 0

theorem bestThreshold_spec (d y : ι → ℚ) (H : ℚ) :
    bestThreshold d y H ∈ thresholds d H ∧
      affine d y (bestThreshold d y H)=value d y H := by
  have hn : ((thresholds d H).filter (fun τ => affine d y τ=value d y H)).Nonempty := by
    obtain ⟨τ,hτ,he⟩ := mem_image.mp (max'_mem ((thresholds d H).image (affine d y))
      ((insert_nonempty 0 _).image _))
    exact ⟨τ,mem_filter.mpr ⟨hτ,he⟩⟩
  simp only [bestThreshold,dite_eq_left hn]
  exact mem_filter.mp (max'_mem _ hn)

def gradient (d y : ι → ℚ) (H : ℚ) (i : ι) : ℚ :=
  -max 0 (bestThreshold d y H-d i)

theorem gradient_spec (d y z : ι → ℚ) (H : ℚ) :
    value d y H-value d z H ≤ ∑ i, gradient d y H i*(y i-z i) := by
  obtain ⟨hτ,he⟩ := bestThreshold_spec d y H
  have hz := affine_le_value d z H (bestThreshold d y H) hτ
  rw [← he]
  have hid : affine d y (bestThreshold d y H)-affine d z (bestThreshold d y H)=
      ∑ i, gradient d y H i*(y i-z i) := by
    unfold affine gradient
    calc
      _ = (∑ i, z i*max 0 (bestThreshold d y H-d i))-
          (∑ i, y i*max 0 (bestThreshold d y H-d i)) := by ring
      _ = ∑ i, (z i*max 0 (bestThreshold d y H-d i)-y i*max 0 (bestThreshold d y H-d i)) := by
        rw [sum_sub_distrib]
      _ = _ := sum_congr rfl (fun _ _ => by ring)
  linarith

theorem gradient_bound (d y : ι → ℚ) (H : ℚ) (hH : 0 ≤ H)
    (hd : ∀ i, 0 ≤ d i ∧ d i ≤ H) (i : ι) :
    |gradient d y H i| ≤ H := by
  have hmem := (bestThreshold_spec d y H).1
  have hτ : bestThreshold d y H ≤ H := by
    obtain he | hmem := mem_insert.mp hmem
    · rw [he]; exact hH
    · obtain he | hmem := mem_insert.mp hmem
      · exact he.le
      · obtain ⟨a,_,he⟩ := mem_image.mp hmem
        rw [← he]; exact (hd a).2
  unfold gradient
  rw [abs_neg,abs_of_nonneg (le_max_left _ _)]
  exact max_le hH (by linarith [(hd i).1])

end MetricKMedian.FractionalDual
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ComputedNearest
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {n : ℕ}

def fill (U : Finset (Fin n)) (y d : Fin n → ℚ) (t : ℚ)
    (hy : ∀ i ∈ U, 0 ≤ y i) (ht : 0 ≤ t) (hm : t ≤ ∑ i ∈ U, y i) : Filling U y d t := by
  if hU : U.Nonempty then
    let a := firstNearest U d hU
    have ha : a ∈ U := (firstNearest_spec U d hU).1
    have hmin : ∀ i ∈ U, d a ≤ d i := (firstNearest_spec U d hU).2
    if hsmall : t ≤ y a then
      let x : Fin n → ℚ := fun i => if i=a then t else 0
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        exact ite_eq_right (fun (he : i=a) => hi (he.symm ▸ ha))
      · intro i hi
        by_cases he : i=a
        · subst i
          simpa only [x,ite_eq_left rfl] using And.intro ht hsmall
        · simp only [x,ite_eq_right he]
          exact ⟨le_rfl,hy i hi⟩
      · simp only [x,sum_ite_eq',ite_eq_left ha]
      · intro i hi b hb hix _
        have hei : i=a := by
          by_contra he
          simp only [x,ite_eq_right he,lt_self_iff_false] at hix
        subst i
        exact hmin b hb
    else
      have hlt : y a < t := lt_of_not_ge hsmall
      have hm' : t-y a ≤ ∑ i ∈ U.erase a, y i := by
        have hs := sum_erase_add U y ha
        linarith only [hm,hs]
      let z := fill (U.erase a) y d (t-y a) (fun i hi => hy i (mem_of_mem_erase hi))
        (sub_nonneg.mpr hlt.le) hm'
      let x : Fin n → ℚ := Function.update z.amount a (y a)
      have hxa : x a=y a := Function.update_self _ _ _
      have hxi : ∀ i, i ≠ a → x i=z.amount i := fun i hi => Function.update_of_ne hi _ _
      refine ⟨x,?_,?_,?_,?_⟩
      · intro i hi
        rw [hxi i (fun (he : i=a) => hi (he.symm ▸ ha))]
        exact z.outside i (fun he => hi (mem_of_mem_erase he))
      · intro i hi
        by_cases he : i=a
        · subst i; rw [hxa]; exact ⟨hy a ha,le_rfl⟩
        · rw [hxi i he]
          exact z.bounds i (mem_erase.mpr ⟨he,hi⟩)
      · rw [← sum_erase_add U x ha,hxa]
        have he : (∑ i ∈ U.erase a, x i)=∑ i ∈ U.erase a, z.amount i :=
          sum_congr rfl (fun i hi => hxi i (mem_erase.mp hi).1)
        rw [he,z.total]
        ring
      · intro i hi b hb hix hbx
        by_cases he : i=a
        · subst i; exact hmin b hb
        · have hbe : b ≠ a := by
            intro hb'; subst b; rw [hxa] at hbx; exact lt_irrefl _ hbx
          rw [hxi i he] at hix
          rw [hxi b hbe] at hbx
          exact z.ordered i (mem_erase.mpr ⟨he,hi⟩) b (mem_erase.mpr ⟨hbe,hb⟩) hix hbx
  else
    have he : U=∅ := not_nonempty_iff_eq_empty.mp hU
    have ht0 : t=0 := le_antisymm (by simpa only [he,sum_empty] using hm) ht
    refine ⟨fun _ => 0,fun _ _ => rfl,?_,?_,?_⟩ <;> simp [he,ht0]
termination_by U.card
decreasing_by exact card_erase_lt_of_mem ha

def computedNearest (y d : Fin n → ℚ) (hy : ∀ i, 0 ≤ y i) (hm : 1 ≤ ∑ i, y i) : Vector ℚ n :=
  Vector.ofFn (fill univ y d 1 (fun i _ => hy i) (by norm_num) hm).amount

end MetricKMedian.Preparation
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_SimplexDiameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.ProjectedSubgradient
open Finset
variable {n : ℕ}

theorem initial_feasible [NeZero n] (k : ℚ) (hk : 0 ≤ k) : feasible k (point (initial (n:=n) k)) := by
  simp only [initial,point_ofFn]
  constructor
  · intro i
    dsimp only
    split_ifs
    · exact hk
    · exact le_rfl
  · rw [sum_ite_eq',ite_eq_left (mem_univ _)]

end MetricKMedian.ProjectedSubgradient
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset
variable {ι κ : Type} [Fintype ι] [Fintype κ]

def objective (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ) : ℚ :=
  ∑ j, FractionalDual.value (truncated d H j) y H

def gradient (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ) (i : ι) : ℚ :=
  ∑ j, FractionalDual.gradient (truncated d H j) y H i

theorem subgradient (d : κ → ι → ℚ) (y z : ι → ℚ) (H : ℚ) :
    objective d y H-objective d z H ≤ ∑ i, gradient d y H i*(y i-z i) := by
  have hh := sum_le_sum (fun j (_ : j ∈ (univ:Finset κ)) =>
    FractionalDual.gradient_spec (truncated d H j) y z H)
  rw [sum_sub_distrib] at hh
  apply hh.trans_eq
  rw [sum_comm]
  exact sum_congr rfl (fun i _ => by rw [← sum_mul]; rfl)

theorem gradient_abs_bound (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) (i : ι) :
    |gradient d y H i| ≤ (Fintype.card κ:ℚ)*H := by
  unfold gradient
  calc
    _ ≤ ∑ j, |FractionalDual.gradient (truncated d H j) y H i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H := sum_le_sum (fun j _ => FractionalDual.gradient_bound _ _ _
      (by linarith) (truncated_bounds d H hH hd j) i)
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

theorem gradient_sq_bound (d : κ → ι → ℚ) (y : ι → ℚ) (H : ℚ)
    (hH : 1 ≤ H) (hd : ∀ j i, 0 ≤ d j i) :
    (∑ i, (gradient d y H i)^2) ≤ (Fintype.card ι:ℚ)*((Fintype.card κ:ℚ)*H)^2 := by
  calc
    _ ≤ ∑ _i : ι, ((Fintype.card κ:ℚ)*H)^2 := sum_le_sum (fun i _ => by
      have hh := gradient_abs_bound d y H hH hd i
      have hh' := mul_self_le_mul_self (abs_nonneg (gradient d y H i)) hh
      simpa only [← sq, sq_abs] using hh')
    _ = _ := by simp only [sum_const,card_univ,nsmul_eq_mul]

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_TruncatedOptimization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.TruncatedLP
open Finset ProjectedSubgradient
variable {n m : ℕ} [NeZero n] [NeZero m]

def optimize (d : Fin m → Fin n → ℚ) (r k H : ℕ)
    (hr : 0 < r) (hk : 0 < k) (hH : 0 < H) : Vector ℚ n :=
  let T := steps (n:=n) (m:=m) r k H
  letI : NeZero T := ⟨(steps_pos r k H hr hk hH).ne'⟩
  let v := trajectory (k:ℚ) (rate (n:=n) (m:=m) r H)
    (fun y => gradient d y H) (initial (k:ℚ))
  let a := Preparation.firstNearest (univ:Finset (Fin T))
    (fun t => objective d (point (v t.val)) H) univ_nonempty
  v a.val

end MetricKMedian.TruncatedLP
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPListFacts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset
abbrev Rows := List Row
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_LPBinaryInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                     
section
namespace MetricKMedian.LPBinary
open Binary Polynomial Finset

namespace Input
def rows (I : Input) : Rows := List.ofFn (fun j => List.ofFn (I.distance j))
end Input

end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Optimization_ApproximationListProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                
section
namespace MetricKMedian.LPBinary
open Binary Binary.PolyProgram Function Finset
namespace Repair
abbrev Output := Row × Rows
end Repair
end MetricKMedian.LPBinary
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_AveragedDrift
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

noncomputable def unnormalizedDrift {I : Type*} [Fintype I]
    (μ d N s : I → ℝ) (q K : I → I → ℝ) (x y pHat : ℝ) : ℝ :=
  let V := ∑ i, μ i*d i
  let w := fun i => ∑ t, μ t*q i t
  let a := 1+m x+B x*y;
  -(3*y+B x*(y-x)^2)*V+
    ∑ i, μ i*((y-w i)*(d i+(1-pHat*s i)*N i)+a*w i*d i+B x*V*w i+
      B x*(∑ t, μ t*K i t*d t)-
      ∑ t, μ t*(1-q i t)*max (d t-a*d i) 0)

end MetricKMedian.GraphComparison
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_ActualActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential FiniteGraph
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

noncomputable def balancedActions (D : Actions I E) (Δ : ℕ) : Finset E :=
  D.ordinary.filter (fun e => (D.erase e).card=Δ)

noncomputable def balancedConflicts (D : Actions I E) (Δ : ℕ) (e : E) : Finset E :=
  if e ∈ balancedActions D Δ then conflicts D.erase (balancedActions D Δ) e else ∅

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_UnbalancedActions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential
variable {I E : Type*} [DecidableEq I] [Fintype I] [DecidableEq E] [Fintype E]

noncomputable def countErase (D : Actions I E) (Δ : ℕ) (e : E) : Finset I :=
  if e ∈ balancedActions D Δ then ∅ else D.erase e

noncomputable def countOpening (D : Actions I E) (Δ : ℕ) (e : E) : ℝ :=
  if e ∈ D.ordinary ∧ e ∉ balancedActions D Δ then 1 else 0

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Preparation_SupplierListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                              
section
namespace MetricKMedian.Preparation.RationalSuppliers.Program
open Finset Binary Binary.Automatic Binary.Automatic.Poly
open SparseGraph.ListOperation (setView indices)
abbrev SupplierRaw := QRow × (BTable × (BTable × (QRow × (QRow × ℚ))))
end MetricKMedian.Preparation.RationalSuppliers.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.SparseBernoulli.ListOperation
open Binary Binary.Automatic Binary.Automatic.Poly

 theorem flag_product {n : ℕ} (q : Fin n → Bool) (S : Finset (Fin n)) :
    (∏ i∈S, flag q i) = if ∀ i∈S, q i=true then 1 else 0 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,ih]
    by_cases hq : q i=true <;> by_cases hs : ∀j∈S,q j=true <;> simp [flag,hq,hs]

 theorem get_true_iff {n : ℕ} (q : Fin n → Bool) (k : ℕ) :
    ((List.ofFn q)[k]?.getD true)=true ↔ ∀ i : Fin n, k=i.val → q i=true := by
  by_cases hk : k<n
  · simp only [List.getElem?_ofFn, dite_eq_left hk]
    simp only [Option.getD_some]
    constructor
    · intro h i hi
      have he : i=(⟨k,hk⟩ : Fin n) := Fin.ext hi.symm
      simpa only [he] using h
    · intro h; exact h ⟨k,hk⟩ rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hk)]
    simp only [Option.getD_none,true_iff]
    intro i hi
    exact (hk (hi ▸ i.isLt)).elim

end MetricKMedian.SparseBernoulli.ListOperation
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_BernoulliRunProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                           
section
namespace MetricKMedian.SparseBernoulli.Program
open Binary Binary.PolyProgram Function Polynomial
 theorem sizePolynomial_eval (d L : ℕ) : (sizePolynomial d).eval L=sizeBound d L := by
  simp only [sizePolynomial,sizeBound,heightBound,supportBound,HPoly,SPoly,SparseBernoulli.stepHeight,
    SparseIntegerLaw.stepHeight,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_pow,eval_zero]

end MetricKMedian.SparseBernoulli.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_BatchOrdinalCodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.RationalBatchData.Ordinal
open Finset FixedBatch
open SparseGraph.ListOperation (Row Table setView indices)
variable {I : Type} [LinearOrder I] {n : ℕ}
variable (r : Fin n ≃o I) (D : Actions I I) (H : Finset I)

abbrev actionOrder : LinearOrder (HeavyAction D H) := by
  letI : LinearOrder (I × I) := pairOrder (I:=I)
  exact LinearOrder.lift' (fun e : HeavyAction D H => toLex e) (fun _ _ h => h)

def code : HeavyAction D H → ℕ
 | .inl h => (r.symm h.val).val
 | .inr p => n+(r.symm p.val.1).val*n+(r.symm p.val.2).val

 theorem code_strictMono : @StrictMono _ _ (actionOrder D H).toPreorder _ (code r D H) := by
  let : LinearOrder (I × I) := pairOrder (I:=I)
  let : LinearOrder (HeavyAction D H) := actionOrder D H
  intro e f hef
  cases e with
  | inl e =>
    cases f with
    | inl f =>
      have hh := Sum.lex_inl_inl.mp hef
      exact r.symm.strictMono hh
    | inr f =>
      simp only [code]
      have he := (r.symm e.val).isLt
      omega
  | inr e =>
    cases f with
    | inl f => cases hef
    | inr f =>
      have hh := Sum.lex_inr_inr.mp hef
      change Prod.Lex (fun a b : I => a<b) (fun a b : I => a<b) e.val f.val at hh
      rcases Prod.lex_def.mp hh with h | ⟨h,h'⟩
      · have h1 : (r.symm e.val.1).val+1≤(r.symm f.val.1).val := r.symm.strictMono h
        have h2 := (r.symm e.val.2).isLt
        simp only [code]
        nlinarith
      · have h1 := congrArg (fun i => (r.symm i).val) h
        have h2 : (r.symm e.val.2).val<(r.symm f.val.2).val := r.symm.strictMono h'
        simp only [code]
        rw [h1]
        omega
 theorem code_lt (e : HeavyAction D H) : code r D H e<n+n*n := by
  cases e with
  | inl e => simp only [code]; have he := (r.symm e.val).isLt; omega
  | inr e =>
    simp only [code]
    have he := (r.symm e.val.1).isLt
    have hf := (r.symm e.val.2).isLt
    nlinarith
 theorem code_light (e : HeavyAction D H) : code r D H e<n ↔ e.isLeft=true := by
  cases e with
  | inl e => simp only [code,Fin.isLt,Sum.isLeft_inl]
  | inr e => simp only [code,Sum.isLeft_inr,Bool.false_eq_true,iff_false]; omega
end MetricKMedian.RationalBatchData.Ordinal
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseBindProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                         
section
namespace MetricKMedian.SparseIntegerLaw.BinarySparse
open Binary Binary.Automatic Binary.Automatic.Poly Finset

variable {α β A : Type}

 theorem scaling_denominator_equiv {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (w : ι → ℚ) :
    RationalScaling.denominator (fun j => w (e.symm j))=RationalScaling.denominator w := by
  unfold RationalScaling.denominator
  exact e.symm.prod_comp (fun i => ((w i).den:ℤ))

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalBatchProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparsePhysicalBatch.Program
open Binary Binary.PolyProgram Function
open SparseIntegerLaw.BinarySparse
open SparseGraph.ListOperation (Row Table )

def Input.bernInput (bal : Bool) (x : Input) : SparseBernoulli.Program.Input :=
  ⟨x.n,(fun i => if bal then x.p else x.q i),fun i => by cases bal <;> [exact x.hq i; exact x.hp]⟩
end MetricKMedian.SparsePhysicalBatch.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_CardinalRoundProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.SparseCardinalRounding.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse

def weightedInput (x : Input) : RoundingProgram.Input false :=
  ⟨x.n,fun _ => 1,Vector.ofFn x.p,fun _ _ => by norm_num,fun i => by
    simpa only [RationalWeightedStep.point,Vector.getElem_ofFn] using x.feasible i⟩
end MetricKMedian.SparseCardinalRounding.Program
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Programs_GraphLawProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                       
section
namespace MetricKMedian.SparseGraph.Program
open Binary Binary.PolyProgram Function SparseIntegerLaw.BinarySparse

def QInput.column (x : QInput) (i : Fin x.m) : SparseBernoulli.Program.Input :=
  ⟨x.n,fun h => x.q h i,fun h => x.feasible h i⟩
def QInput.columns (x : QInput) : List SparseBernoulli.Program.Input := List.ofFn x.column
def emptyColumn : SparseBernoulli.Program.Input := ⟨0,Fin.elim0,fun i => Fin.elim0 i⟩
end MetricKMedian.SparseGraph.Program
end

end OAI
end


