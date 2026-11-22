-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DegLESum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:52.714633+00:00
-- url     : https://prove2.me/theorems/a3c4be44-cbde-43b2-ab6b-8ca0bb29bbe7
-- title:
--   Deg LESum
-- statement:
--   Definitions and structural lemmas for Deg LESum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DegLESum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qf21.degLE :
    {κ R : Type} → [inst : CommRing R] → Finset κ → ℕ → MvPolynomial κ R → Prop :=
    fun {κ R : Type} [CommRing R] (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) ↦
      ∀ (β : κ →₀ ℕ), MvPolynomial.coeff β F ≠ (0 : R) → ∑ k ∈ W, (β : κ → ℕ) k ≤ n


