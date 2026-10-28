-- Prove2me | Definitions.Def_OAIQ035K016
-- name    : OAIQ035K016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T07:55:37.393567+00:00
-- url     : https://prove2.me/theorems/c7f963f8-d11e-4521-bb26-b2cac6a9c1dd
-- title:
--   Definitions bundle OAIQ035K016 of the split of OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 33 declarations of OpenAI's Lean: 15 definitions, 1 inductive type or structure and 17 theorems. The definitions and types are `OAI.MetricKMedian.CopyState.roundOpened`, `OAI.MetricKMedian.FiniteComparison.actualB`, `OAI.MetricKMedian.FiniteComparison.rowValue`, `OAI.MetricKMedian.FiniteComparison.uprime`, `OAI.MetricKMedian.FiniteLaw.condition`, `OAI.MetricKMedian.FiniteLaw.dirac`, `OAI.MetricKMedian.FiniteLaw.joint`, `OAI.MetricKMedian.FiniteLaw.map`, `OAI.MetricKMedian.FiniteLaw.sumMix`, `OAI.MetricKMedian.FixedBatch.RationalParameters`, `OAI.MetricKMedian.FixedBatch.RationalParameters.probabilityQ`, `OAI.MetricKMedian.IntegerLaw.ListOperation.Row`, `OAI.MetricKMedian.PhysicalPotential.savingsFraction`, `OAI.MetricKMedian.RationalPhysicalKernel.CopyList.orderEquiv`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.jointWeights`, `OAI.MetricKMedian.SparseIntegerLaw.BinarySparse.weights`.
--
--   **Sources.** They come from these modules of lean/OAI/Combinatorics/KMedian, in whole or in part: `KMedian_Analysis_FiniteAverages`, `KMedian_Analysis_FiniteComparison`, `KMedian_Analysis_RowComparison`, `KMedian_Compression_AffineListOperations`, `KMedian_Geometry_NearestReindex`, `KMedian_Geometry_RationalParameterizedHistory`, `KMedian_Preparation_PreparationMoments`, `KMedian_Probability_Conditioning`, `KMedian_Probability_FiniteClipping`, `KMedian_Probability_FiniteJoint`, `KMedian_Probability_FiniteKernels`, `KMedian_Probability_FiniteLawConstructions`, `KMedian_Probability_FiniteLaws`, `KMedian_Probability_FiniteVariance`, `KMedian_Probability_ProbabilitySupport`, `KMedian_Probability_SumLaws`, `KMedian_Process_CopyRound`, `KMedian_Process_PhysicalPotential`, `KMedian_Rounding_RationalRoundParameters`, `KMedian_Sparse_SparseBindProgram`.
--
--   **Imports.** It imports the bundles `OAIQ035K000`, `OAIQ035K001`, `OAIQ035K002`, `OAIQ035K003`, `OAIQ035K004` and `OAIQ035K005` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ035K029`, `OAIQ035K031`, `OAIQ035K032`, `OAIQ035K033`, `OAIQ035K035`, `OAIQ035K044` and `OAIQ035K062`; the statements `OAI.MetricKMedian.CopyState.round_backup`, `OAI.MetricKMedian.CopyState.round_cap`, `OAI.MetricKMedian.CopyState.unbalanced_count_change`, `OAI.MetricKMedian.CopyState.unbalanced_small_change`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound`, `OAI.MetricKMedian.Preparation.client_assignments`, `OAI.MetricKMedian.Preparation.distant_assignments`, `OAI.MetricKMedian.Preparation.nearby_assignments`, `OAI.MetricKMedian.Preparation.physical_old_estimates`, `OAI.MetricKMedian.Preparation.selected_preparation_outcome`, `OAI.MetricKMedian.Preparation.shortfall_from_deviation` and `OAI.MetricKMedian.Preparation.supplier_assignments`; the proofs of `OAI.MetricKMedian.CopyState.round_backup`, `OAI.MetricKMedian.CopyState.round_cap`, `OAI.MetricKMedian.CopyState.unbalanced_count_change`, `OAI.MetricKMedian.CopyState.unbalanced_small_change`, `OAI.MetricKMedian.FixedBatch.forced_step_local_bound`, `OAI.MetricKMedian.FixedBatch.post_force_bound`, `OAI.MetricKMedian.GeneratorAverage.expanded_bound`, `OAI.MetricKMedian.Preparation.client_assignments`, `OAI.MetricKMedian.Preparation.distant_assignments`, `OAI.MetricKMedian.Preparation.nearby_assignments`, `OAI.MetricKMedian.Preparation.physical_old_estimates`, `OAI.MetricKMedian.Preparation.selected_preparation_outcome`, `OAI.MetricKMedian.Preparation.shortfall_from_deviation` and `OAI.MetricKMedian.Preparation.supplier_assignments`.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/KMedian at commit adc7f12

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K001
import Definitions.Def_OAIQ035K002
import Definitions.Def_OAIQ035K003
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K005

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

noncomputable def rowValue {I : Type*} [Fintype I] (π Z q : I → ℝ)
    (p m a z : ℝ) (b : Bool → ℝ) (s : Bool) (D R : ℝ) : ℝ :=
  C p s * (1 - average π q) * R +
    (m * D + b s * (D + 1)) * average π q - C p s * (D + 1) -
    average π (fun t => (1 - q t) * max (Z t - a * D) 0) -
    ((2 / 5) * D + 8 / 5) * z

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

noncomputable def uprime (p m z : ℝ) (b : Bool → ℝ) (s : Bool) (D r : ℝ) : ℝ :=
  ((m * D + b s * (D + 1)) * r - ((2 / 5) * D + 8 / 5) * z) / (C p s * r)

end MetricKMedian.FiniteComparison


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_FiniteComparison
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
-- module Solutions.OAIQ035_KM.KMedian_Compression_AffineListOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                            
section
namespace MetricKMedian.IntegerLaw.ListOperation
open Binary Gaussian
open Finset
abbrev Row := Binary.IntegerList.Row

end MetricKMedian.IntegerLaw.ListOperation
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

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

theorem expect_mul_right (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => f ω * c) = μ.expect f * c := by
  simp only [expect, ← mul_assoc, Finset.sum_mul]

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
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteLawConstructions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw

noncomputable def dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) : FiniteLaw Ω where
  weight ω := if ω=ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  total := by simp

theorem expect_dirac {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ω₀ : Ω) (f : Ω → ℝ) :
    (dirac ω₀).expect f = f ω₀ := by simp [expect, dirac]

end MetricKMedian.FiniteLaw

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

theorem expect_bind (μ : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ) (f : Ξ → ℝ) :
    (μ.bind κ).expect f = μ.expect (fun ω => (κ ω).expect f) := by
  simp only [bind, expect, Finset.sum_mul, mul_assoc, Finset.mul_sum]
  exact Finset.sum_comm

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

noncomputable def map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ :=
  μ.bind (fun ω => dirac (f ω))

theorem expect_map [DecidableEq Ξ] (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    (μ.map f).expect g=μ.expect (fun ω => g (f ω)) := by
  rw [map, expect_bind]
  simp_rw [expect_dirac]

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

variable {I : Type*}

noncomputable def savingsFraction (g : ℝ) : ℝ :=
  min 1 (2 * P 1 * g / (1 + 1 / g))

end MetricKMedian.PhysicalPotential
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

noncomputable def roundOpened (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) : Finset F :=
  (selectedSources G H Z).image (fun i => i.val.1)

end MetricKMedian.CopyState
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_SumLaws
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

noncomputable def sumMix (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (μ : FiniteLaw Ω) (ν : FiniteLaw Ξ) : FiniteLaw (Ω ⊕ Ξ) where
  weight := Sum.elim (fun ω => θ*μ.weight ω) (fun ξ => (1-θ)*ν.weight ξ)
  nonneg := by
    intro z
    cases z with
    | inl ω => exact mul_nonneg hθ0 (μ.nonneg ω)
    | inr ξ => exact mul_nonneg (sub_nonneg.mpr hθ1) (ν.nonneg ξ)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum, μ.total, ν.total]
    ring

end MetricKMedian.FiniteLaw

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

omit [Fintype Ξ] in
theorem variance_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) : 0 ≤ μ.variance f :=
  μ.expect_nonneg (fun _ => sq_nonneg _)

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
-- module Solutions.OAIQ035_KM.KMedian_Probability_ProbabilitySupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

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
-- module Solutions.OAIQ035_KM.KMedian_Geometry_NearestReindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                      
section
namespace MetricKMedian.Preparation.RationalNearest
open Finset
variable {α β : Type} [LinearOrder α] [LinearOrder β]

 theorem takeNearest_map (e : α ≃o β) (d : α → ℚ) (t : ℕ) (U : Finset α) :
    takeNearest (fun b => d (e.symm b)) t (U.map e.toEmbedding)=(takeNearest d t U).map e.toEmbedding := by
  induction t generalizing U with
  | zero => simp only [takeNearest,map_empty]
  | succ t ih =>
    by_cases hU : U.Nonempty
    · rw [takeNearest,takeNearest,dite_eq_left hU,dite_eq_left (hU.map),least_map e U d hU]
      have he : (U.map e.toEmbedding).erase (e (least U d hU))=(U.erase (least U d hU)).map e.toEmbedding := by
        exact (map_erase e.toEmbedding U (least U d hU)).symm
      rw [he,ih,map_insert]
      rfl
    · have he := not_nonempty_iff_eq_empty.mp hU
      subst U
      simp [takeNearest]
end MetricKMedian.Preparation.RationalNearest

namespace MetricKMedian.RationalPhysicalKernel.CopyList
open CopyState
variable {f Δ : ℕ}

local instance instLinearOrderCopyFin_1_r6eb8e0_1 : LinearOrder (Copy (F:=Fin f) Δ) := copyOrder
def orderEquiv : @OrderIso (Copy (F:=Fin f) Δ) (Fin (f*Δ)) (copyOrder (F:=Fin f) (Δ:=Δ)).toLE inferInstance where
  toEquiv := finProdFinEquiv
  map_rel_iff' := @StrictMono.le_iff_le _ _ (copyOrder (F:=Fin f) (Δ:=Δ)) _ _ rank_strictMono
end MetricKMedian.RationalPhysicalKernel.CopyList
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Rounding_RationalRoundParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                               
section
namespace MetricKMedian.FixedBatch
open PhysicalPotential

structure RationalParameters (τ : ℝ) where
  Δ : ℕ
  g : ℚ
  h : ℚ
  φ : ℚ
  β : ℚ
  ζ : ℚ
  T : ℕ
  taper : Fin T → ℚ
  Δpos : 0<Δ
  gpos : 0<(g:ℝ)
  gle : (g:ℝ)≤1
  unit : (g:ℝ)*(Δ:ℝ)=1
  hpos : 0<(h:ℝ)
  hle : (h:ℝ)≤1
  φpos : 0<(φ:ℝ)
  φle : (φ:ℝ)≤1
  βpos : 0<(β:ℝ)
  ζpos : 0<(ζ:ℝ)
  ζle : (ζ:ℝ)<1/4
  probability : (1+(φ:ℝ))*(2*(h:ℝ)*(g:ℝ))≤1
  small : (16*((Δ^2+Δ:ℕ):ℝ)+10)*(h:ℝ)≤ savingsFraction (g:ℝ)
  survival : (2*(h:ℝ)*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ))≤1
  count : 8*(2*(h:ℝ)*(g:ℝ))*(Δ:ℝ)≤(φ:ℝ)*(g:ℝ)
  error : (T:ℝ)*(h:ℝ)*((g:ℝ)+12*(ζ:ℝ))+
    (T:ℝ)*batchConstant Δ*(h:ℝ)*((φ:ℝ)+(h:ℝ))*(Δ:ℝ)+
    5*(Δ:ℝ)*Real.exp (-(T:ℝ)*(h:ℝ)/2)≤τ
  failure : (T:ℝ)*(96*(Δ:ℝ)^2*(β:ℝ)/((2*(h:ℝ)*(g:ℝ))*(φ:ℝ)^2*(g:ℝ)))≤τ
  taper_pos : ∀ t, 0<(taper t:ℝ)
  taper_le : ∀ t, (taper t:ℝ)≤1/2
  taper_error : ∀ t, |(taper t:ℝ)-Analytic.P (Real.exp (-(t.val:ℝ)*(h:ℝ)))|≤(ζ:ℝ)

end MetricKMedian.FixedBatch
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

def probabilityQ : ℚ := 2*q.h*q.g

end MetricKMedian.FixedBatch.RationalParameters
end

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
 theorem expect_abs_centered_le_sqrt (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.expect (fun ω => |X ω-μ.expect X|) ≤ Real.sqrt (μ.variance X) := by
  have hs := μ.sq_expect_le_expect_sq (fun ω => |X ω-μ.expect X|)
  simp only [sq_abs] at hs
  exact (Real.le_sqrt (μ.expect_nonneg (fun _ => abs_nonneg _)) (μ.variance_nonneg X)).mpr hs

omit [Fintype I] in
 theorem variance_mul (μ : FiniteLaw Ω) (X : Ω → ℝ) (g : ℝ) :
    μ.variance (fun ω => g*X ω)=g^2*μ.variance X := by
  rw [variance_eq, variance_eq, expect_mul]
  simp_rw [mul_pow, expect_mul]
  ring

end MetricKMedian.FiniteLaw
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_Conditioning
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
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteJoint
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

def weights (x : LawData) : List ℚ := x.2.map (fun z : ℤ => (z:ℚ)/(x.1:ℚ))
def jointWeights (x : LawData × List (Data A)) : List ℚ :=
  ((weights x.1).zip x.2).flatMap (fun z => (weights z.2.1).map (fun q => z.1*q))

end MetricKMedian.SparseIntegerLaw.BinarySparse
end

end OAI
end


