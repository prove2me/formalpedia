-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PhiMulTranspose
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_PhiMulTranspose
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:24:46.746601+00:00
-- url     : https://prove2.me/theorems/be445af8-5f80-4cad-b228-3a707e14f24a
-- title:
--   Phi Mul Transpose
-- statement:
--   Definitions and structural lemmas for Phi Mul Transpose, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/PhiMulTranspose.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Yzd2.Phi :
    (n : ℕ) → (R : Type) → [CommRing R] → Matrix (Fin n) (Fin n) R :=
    fun (n : ℕ) (R : Type) [CommRing R] ↦
      (Matrix.of : (Fin n → Fin n → R) → Matrix (Fin n) (Fin n) R) fun (i j : Fin n) ↦
        if (↑i : ℕ) + (↑j : ℕ) + (1 : ℕ) = n then (-1 : R) ^ (↑i : ℕ) else (0 : R)


