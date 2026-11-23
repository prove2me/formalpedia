-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConvSqLe
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ConvSqLe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:31:46.709659+00:00
-- url     : https://prove2.me/theorems/90de38bc-84a2-4d29-bc43-de9dbb6ba2ad
-- title:
--   Conv Sq Le
-- statement:
--   Definitions and structural lemmas for Conv Sq Le, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ConvSqLe.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qj8.E :
    ℕ → Type :=
    fun (d : ℕ) ↦ EuclideanSpace ℝ (Fin d)


