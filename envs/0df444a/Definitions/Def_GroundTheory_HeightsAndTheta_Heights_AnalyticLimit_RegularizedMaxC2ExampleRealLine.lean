-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
-- name    : GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_RegularizedMaxC2ExampleRealLine
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:26:27.648089+00:00
-- url     : https://prove2.me/theorems/c41be57a-08c9-48b0-8650-db4e350c71e6
-- title:
--   Regularized Max C2 Example Real Line
-- statement:
--   Definitions and structural lemmas for Regularized Max C2 Example Real Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/RegularizedMaxC2ExampleRealLine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_regMax_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_fderiv2_regMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_add_const
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_comp_fderiv2
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_contDiff
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_nonneg
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_fderiv_sum
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_one_fderiv2_bound
import Theorems.Thm_ReciprocityTheory_AnForm_A_two_le_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.AnalyticLimit
open Filter Topology Metric
open ReciprocityTheory.AnForm.A (regMax regMax_contDiff regMax_add_const abs_regMax_le regMax_fderiv_sum
  regMax_fderiv_nonneg fderiv2_regMax regMax_one_fderiv2_bound regMax_comp_fderiv2 two_le_inf)
noncomputable section
section C2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
def TendstoC2On (F : ℝ → E → ℝ) (f : E → ℝ) (K : Set E) : Prop :=
  TendstoUniformlyOn F f (𝓝[>] 0) K ∧
    TendstoUniformlyOn (fun t y => fderiv ℝ (F t) y) (fderiv ℝ f) (𝓝[>] 0) K ∧
    TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ (F t)) y) (fderiv ℝ (fderiv ℝ f)) (𝓝[>] 0) K
def RegularizedMaxConvergenceC2.Statement : Prop :=
  ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (ι : Type) [Fintype ι] [Nonempty ι]
    (U K : Set E) (f : E → ℝ) (u : ℝ → ι → E → ℝ) (ε δ : ℝ → ℝ),
    IsOpen U → K ⊆ U → ContDiffOn ℝ 2 f U →
    (∀ᶠ t in 𝓝[>] 0, 0 < ε t ∧ ∀ j, ContDiffOn ℝ 2 (u t j) U) →
    Tendsto ε (𝓝[>] 0) (𝓝 0) →
    (∀ j, TendstoC2On (fun t => u t j) f K) →
    (∀ᶠ t in 𝓝[>] 0, ∀ j, ∀ x ∈ K, ‖fderiv ℝ (u t j) x - fderiv ℝ f x‖ ≤ δ t) →
    Tendsto (fun t => δ t ^ 2 / ε t) (𝓝[>] 0) (𝓝 0) →
    TendstoC2On (fun t x => regMax (ε t) (fun j => u t j x) + ε t / 2) f K
end C2
section RegMax
variable {ι : Type*} [Fintype ι] [Nonempty ι]
end RegMax
section Main
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*} [Fintype ι] [Nonempty ι]
end Main
section System
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} {R : RegChartData A}
end System
end
end GroundTheory.Heights₂.Heights.AnalyticLimit


