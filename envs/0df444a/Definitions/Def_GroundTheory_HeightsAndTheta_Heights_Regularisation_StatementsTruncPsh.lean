-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:17.685717+00:00
-- url     : https://prove2.me/theorems/34320c28-1444-443b-880d-e917b872ec26
-- title:
--   Statements Trunc Psh
-- statement:
--   Definitions and structural lemmas for Statements Trunc Psh, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/StatementsTruncPsh.lean

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
open Metric
open ReciprocityTheory.AnForm.A (IsPsh)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
def TruncPsh.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ B : ℝ, 0 < δ ∧ ∀ j : Fin R.N, ∃ V : Set (Fin D → ℂ), IsOpen V ∧
      V ⊆ (R.chart j).target ∧ (∀ x ∈ R.mid j, closedBall (R.chart j x) δ ⊆ V) ∧
      ∀ K : ℝ, IsPsh V (R.trunc K j) ∧ ∀ y ∈ V, R.trunc K j y ≤ max B (-K)
end
end GroundTheory.Heights₂.Heights.Regular


