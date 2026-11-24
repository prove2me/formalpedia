-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoxBounds
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BoxBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:56.483807+00:00
-- url     : https://prove2.me/theorems/3a618348-4d40-450a-a21c-da84ca34a23b
-- title:
--   Box Bounds
-- statement:
--   Definitions and structural lemmas for Box Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BoxBounds.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.BoxBounds.box :
    {K : Type} → [inst : Field K] → {i : ℕ} → K → Submodule (NumberField.RingOfIntegers K) (Fin i → K) :=
    fun {K : Type} [Field K] {i : ℕ} (c : K) ↦ Submodule.pi Set.univ fun (x : Fin i) ↦ NumberField.RingOfIntegers K ∙ c


