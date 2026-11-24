-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_VandermondeOfEqDet
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:18.910103+00:00
-- url     : https://prove2.me/theorems/0497adb8-836c-4147-bfe0-2ba3c6fe133e
-- title:
--   Vandermonde Of Eq Det
-- statement:
--   Definitions and structural lemmas for Vandermonde Of Eq Det, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/VandermondeOfEqDet.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qm12.vandermondeOf.{u_1} :
    {R : Type u_1} → [CommRing R] → {m : ℕ} → (Fin m → R) → R :=
    fun {R : Type u_1} [CommRing R] {m : ℕ} (v : Fin m → R) ↦ ∏ i : Fin m, ∏ j > i, (v i - v j)


