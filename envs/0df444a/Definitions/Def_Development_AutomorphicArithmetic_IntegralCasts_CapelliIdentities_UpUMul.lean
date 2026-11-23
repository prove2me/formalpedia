-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UpUMul
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UpUMul
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:03.939038+00:00
-- url     : https://prove2.me/theorems/f47eeff3-398e-495c-804e-655d237c0891
-- title:
--   Up UMul
-- statement:
--   Definitions and structural lemmas for Up UMul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UpUMul.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qh21.UpU.{u_1} :
    {K : Type u_1} → [Field K] → {N : ℕ} → Matrix (Fin N) (Fin N) K → Prop :=
    fun {K : Type u_1} [Field K] {N : ℕ} (U : Matrix (Fin N) (Fin N) K) ↦
      ∀ (i j : Fin N), (j < i → U i j = (0 : K)) ∧ (i = j → U i j = (1 : K))


