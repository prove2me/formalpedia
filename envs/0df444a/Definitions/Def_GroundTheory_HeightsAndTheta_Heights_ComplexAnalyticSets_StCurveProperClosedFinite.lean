-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveProperClosedFinite
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveProperClosedFinite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:32:45.622912+00:00
-- url     : https://prove2.me/theorems/b03568fc-b1f3-41e1-a94a-d9fec6a95772
-- title:
--   St Curve Proper Closed Finite
-- statement:
--   Definitions and structural lemmas for St Curve Proper Closed Finite, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StCurveProperClosedFinite.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCurveNormalisationLength
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
open MvPolynomial ComplexSets Filter Topology
noncomputable section
def CurveProperClosedFinite.Statement : Prop :=
  ∀ (n : ℕ) (W K : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 → ¬ K ≤ W →
      (zeroSet W ∩ zeroSet K).Finite
end
end GroundTheory.Heights₂.Heights


