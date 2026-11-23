-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PhiMulSelf
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PhiMulSelf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:44.348309+00:00
-- url     : https://prove2.me/theorems/442f0c05-4130-4581-99cc-d326e56f7c84
-- title:
--   Phi Mul Self
-- statement:
--   Definitions and structural lemmas for Phi Mul Self, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/PhiMulSelf.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Yzd3.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)


