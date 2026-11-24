-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
-- name    : GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsLeadBlockGaussTail
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:58:42.092876+00:00
-- url     : https://prove2.me/theorems/9df874a4-6f9e-46d9-8047-3df3b5e6902a
-- title:
--   Statements Lead Block Gauss Tail
-- statement:
--   Definitions and structural lemmas for Statements Lead Block Gauss Tail, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/StatementsLeadBlockGaussTail.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeTangentAverage
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open MeasureTheory
open scoped ENNReal
noncomputable section
def LeadBlockGaussTail.Statement : Prop :=
  ∀ (m k : ℕ), 0 < m → ∃ C : ℝ, ∀ r : ℝ,
    ∫⁻ π : Fin m → Fin (m + k) → ℂ, matGauss π *
        (Metric.ball (0 : EuclideanSpace ℂ (Fin m)) 1).indicator 1
          (linProj π ((r : ℂ) • firstCoordVec (m + k))) *
        ENNReal.ofReal (‖(coordPlaneBlock π).det‖ ^ 2) ≤
      ENNReal.ofReal (C / (1 + r ^ 2) ^ (m + 1))
end
end GroundTheory.Heights₂.Heights


