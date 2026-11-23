-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_OkpInert
-- name    : Formalism_PeriodIntegrals_OkpInert
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:31:32.607419+00:00
-- url     : https://prove2.me/theorems/90c317bf-6159-4fed-87f0-10be3f23bc53
-- title:
--   Okp Inert
-- statement:
--   Definitions and structural lemmas for Okp Inert, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OkpInert.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace PI
def W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))
def OkpInert : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]),
    Module.finrank ℚ K = 2 → (∃ x, c x ≠ x) → p ≠ 2 → (Ideal.span {(p : 𝓞 K)}).IsPrime →
    closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K)))) = W2pair p
end PI


