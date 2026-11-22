-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeIffLtColH
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LeIffLtColH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:56.303209+00:00
-- url     : https://prove2.me/theorems/1a53f3e4-4c34-4616-a01d-7a5799b1b6be
-- title:
--   Le Iff Lt Col H
-- statement:
--   Definitions and structural lemmas for Le Iff Lt Col H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/LeIffLtColH.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qk46.colH :
    {n : Nat} → (Fin n → Int) → Int → Nat :=
    fun {n : Nat} (mu : Fin n → Int) (c : Int) ↦ @Finset.card (Fin n) {m : Fin n | @LE.le Int Int.instLEInt c (mu m)}


