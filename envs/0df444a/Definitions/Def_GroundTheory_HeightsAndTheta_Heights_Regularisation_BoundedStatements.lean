-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:36:05.37175+00:00
-- url     : https://prove2.me/theorems/cfd18106-2b39-45de-a048-3d6d80e3bb3c
-- title:
--   Bounded Statements
-- statement:
--   Definitions and structural lemmas for Bounded Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/BoundedStatements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section
namespace BoundedPshData
variable {D : ℕ} {X : Type*} [TopologicalSpace X] {A : FinHolAtlas D X} (B : BoundedPshData A)
def u (j : Fin B.N) : (Fin D → ℂ) → ℝ := B.chartFun B.ph j
def smoothed (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) : (Fin D → ℂ) → ℝ :=
  molli ρ t (B.u j)
def phReg (ρ : Mollifier D) (t : ℝ) (j : Fin B.N) (x : X) : ℝ :=
  B.smoothed ρ t j (B.chart j x) - B.q j (B.chart j x)
def regularised (ρ : Mollifier D) (t ε : ℝ) (η : Fin B.N → X → ℝ) : X → ℝ :=
  B.glue (fun j x => B.phReg ρ t j x + 4 * ε * η j x) ε
end BoundedPshData
def BoundedChartComparison.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D), ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      ∀ j k : Fin B.N, ∀ x ∈ B.mid j ∩ B.mid k,
        |B.phReg ρ t j x - B.phReg ρ t k x| ≤ C / Real.log t⁻¹ + C * t
def BoundedGlue.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (B : BoundedPshData A) (ρ : Mollifier D) (η : Fin B.N → X → ℝ) (Cη t ε : ℝ),
    B.IsCutoffFamily η Cη → 0 < t → 0 < ε →
    (∀ j, ∀ x ∈ closure (B.mid j), closedBall (B.chart j x) t ⊆ (B.chart j).target) →
    (∀ j k, ∀ x ∈ B.mid j ∩ B.mid k, |B.phReg ρ t j x - B.phReg ρ t k x| ≤ ε) →
    A.Smooth (B.regularised ρ t ε η) ∧
      ∀ k : Fin B.N, ∀ x ∈ B.mid k, ∀ w : Fin D → ℂ,
        -(4 * Cη * ε) * ‖w‖ ^ 2 ≤ levi (B.chartFun (B.regularised ρ t ε η) k) (B.chart k x) w
section Inhabitants
end Inhabitants
end
end GroundTheory.Heights₂.Heights.Regular


