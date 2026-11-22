-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleySignature
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CayleySignature
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:24.284808+00:00
-- url     : https://prove2.me/theorems/c833bec2-4a0e-4923-9014-ea896184f46d
-- title:
--   Cayley Signature
-- statement:
--   Definitions and structural lemmas for Cayley Signature, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CayleySignature.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.CayleySignature.IsLatIn :
    {R W : Type} →
      [inst : CommRing R] → [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submodule R W → Submodule R W → Prop :=
    fun {R W : Type} [CommRing R] [AddCommGroup W] [_root_.Module R W] (M V : Submodule R W) ↦
      M.FG ∧ M ≤ V ∧ ∀ x ∈ V, ∃ (c : R), c ≠ (0 : R) ∧ c • x ∈ M


