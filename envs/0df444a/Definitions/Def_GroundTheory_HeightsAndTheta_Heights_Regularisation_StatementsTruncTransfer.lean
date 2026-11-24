-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
-- name    : GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncTransfer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:02.751873+00:00
-- url     : https://prove2.me/theorems/1798e775-57ec-47f2-944b-ef7b7b181e58
-- title:
--   Statements Trunc Transfer
-- statement:
--   Definitions and structural lemmas for Statements Trunc Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/StatementsTruncTransfer.lean

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
open ReciprocityTheory.AnForm.A (polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
def TruncTransfer.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (R : RegChartData A), ∃ δ L B : ℝ, 0 < δ ∧ 1 ≤ L ∧ ∀ (K : ℝ) (j k : Fin R.N),
      ∀ x ∈ R.mid j ∩ R.mid k, ∀ t : ℝ, 0 < t → t < δ → ∀ y ∈ closedBall (R.chart j x) t,
        R.trunc K j y ≤ max (polyMax (R.trunc K k) (R.chart k x) (L * t)) (-K + B) +
          (R.q j (R.chart j x) - R.q k (R.chart k x)) + L * t
end
end GroundTheory.Heights₂.Heights.Regular


