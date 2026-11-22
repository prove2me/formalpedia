-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_TayInvPow
-- name    : Formalism_PeriodIntegrals_TayInvPow
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:29.877913+00:00
-- url     : https://prove2.me/theorems/e8faa75c-3e5b-4403-b17f-b5b61b69b1ca
-- title:
--   Tay Inv Pow
-- statement:
--   Definitions and structural lemmas for Tay Inv Pow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/TayInvPow.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace PI
open MvPowerSeries
universe u v
def TayInvPow : Prop :=
  ∀ (σ : Type u) (A : Type v) [CommRing A] (τ : A →+* MvPowerSeries σ A) (s t : A) (c : σ →₀ A),
    s * t = 1 →
    τ s = C s + c.sum (fun p a => C a * X p) →
    ∀ (k : ℕ) (β : σ →₀ ℕ),
      coeff β (τ (t ^ k)) =
        (-1) ^ (β.sum fun _ n => n) * (((k + (β.sum fun _ n => n) - 1).choose (β.sum fun _ n => n) : ℕ) : A) *
          ((Nat.multinomial β.support β : ℕ) : A) * (β.prod fun p b => c p ^ b) * t ^ (k + β.sum fun _ n => n)
end PI


