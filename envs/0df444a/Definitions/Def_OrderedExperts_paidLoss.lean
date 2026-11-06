-- Prove2me | Definitions.Def_OrderedExperts_paidLoss
-- name    : OrderedExperts_paidLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:37.50572+00:00
-- url     : https://prove2.me/theorems/5955145b-7259-4e3c-b3cf-97e4c8189760
-- title:
--   Paid loss of one round
-- statement:
--   Under two-point feedback the learner queries two active actions $x_{t,A}$, $x_{t,B}$ and incurs their average loss
--   $$
--   \tfrac12\bigl(\ell_t(x_{t,A})+\ell_t(x_{t,B})\bigr),\qquad \ell_t=\ell^\uparrow_t+\ell^\downarrow_t .
--   $$
-- source:
--   Zuo, Online Learning with Ordered Experts (via Two-point Feedback), STOC 2027 submission (held version, sha256 a6480b1e…fe429), Sec. 2.2, p.5; Sec. 2.1, p.5

import Definitions.Def_OrderedExperts_chainPt

namespace OrderedExperts

/-- **The paid loss of one round.** Zuo, *Online Learning with Ordered Experts (via Two-point Feedback)*, STOC 2027 submission (held version), Sec. 2.2, p.5: "The learner
simultaneously chooses `At, Bt ∈ Xt` and incurs `½(ℓt(At) + ℓt(Bt))`", with
`ℓt(a) = ℓ↑t(a) + ℓ↓t(a)` (Sec. 2.1, p.5).

`paidLoss rec up down t a b = ½(ℓt(xt,a) + ℓt(xt,b))` for the queried ranks `a`, `b`. -/
noncomputable def paidLoss {A : Type*} [LinearOrder A] [OrderBot A] {n : ℕ}
    (rec : ℕ → Fin n → A) (up down : ℕ → A → ℝ) (t a b : ℕ) : ℝ :=
  ((up t (chainPt rec t a) + down t (chainPt rec t a)) +
    (up t (chainPt rec t b) + down t (chainPt rec t b))) / 2

end OrderedExperts


