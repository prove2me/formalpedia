-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_OpenFix
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_OpenFix
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:51.466522+00:00
-- url     : https://prove2.me/theorems/86d3320d-d20c-4d3d-8b5d-80cac411494f
-- title:
--   Open Fix
-- statement:
--   Definitions and structural lemmas for Open Fix, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/OpenFix.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.Om :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi42.GQ :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ Gal(UpperTheory.Reformulated.B.Qi42.Om l/ℚ_[l])


