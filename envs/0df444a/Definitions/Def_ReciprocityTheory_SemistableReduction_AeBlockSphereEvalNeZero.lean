-- Prove2me | Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
-- name    : ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:50.07272+00:00
-- url     : https://prove2.me/theorems/85812de2-ac4f-441a-9fbc-40928f30cd9f
-- title:
--   Ae Block Sphere Eval Ne Zero
-- statement:
--   Definitions and structural lemmas for Ae Block Sphere Eval Ne Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/AeBlockSphereEvalNeZero.lean

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric
def blockCoordEquiv (B n : ℕ) : (Fin B → EuclideanSpace ℂ (Fin n)) ≃ₗ[ℂ] (Fin B × Fin n → ℂ) :=
  (LinearEquiv.piCongrRight fun _ => WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).trans
    (LinearEquiv.curry ℂ ℂ (Fin B) (Fin n)).symm
end ReciprocityTheory.MultiplicativeHeights


