-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BiHomSum
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:50.963802+00:00
-- url     : https://prove2.me/theorems/7a0fcf03-f1c3-4b9f-9103-373e31f5de28
-- title:
--   Bi Hom Sum
-- statement:
--   Definitions and structural lemmas for Bi Hom Sum, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/BiHomSum.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qf22.biHom :
    {K ι κ : Type} → [inst : Field K] → ℕ → MvPolynomial κ (MvPolynomial ι K) → Prop :=
    fun {K ι κ : Type} [Field K] (d : ℕ) (F : MvPolynomial κ (MvPolynomial ι K)) ↦
      ∀ (β : κ →₀ ℕ) (n : ι →₀ ℕ),
        MvPolynomial.coeff n (MvPolynomial.coeff β F) ≠ (0 : K) →
          (Finsupp.degree : (ι →₀ ℕ) → ℕ) n + (Finsupp.degree : (κ →₀ ℕ) → ℕ) β = d


