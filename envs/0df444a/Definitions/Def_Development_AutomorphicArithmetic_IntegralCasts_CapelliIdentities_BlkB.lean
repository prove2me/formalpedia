-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlkB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:11.312996+00:00
-- url     : https://prove2.me/theorems/78d36f5b-3456-4422-a25d-bf5f9732a971
-- title:
--   Blk B
-- statement:
--   Definitions and structural lemmas for Blk B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BlkB.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Yha8.blkA :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ {i : Fin n | (↑i : ℕ) < j}
noncomputable def UpperTheory.Reformulated.B.Yha8.blkB :
    {n : ℕ} → ℕ → Finset (Fin n) :=
    fun {n : ℕ} (j : ℕ) ↦ (UpperTheory.Reformulated.B.Yha8.blkA j)ᶜ


