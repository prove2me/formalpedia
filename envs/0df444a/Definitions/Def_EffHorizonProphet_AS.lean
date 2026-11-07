-- Prove2me | Definitions.Def_EffHorizonProphet_AS
-- name    : EffHorizonProphet_AS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:33.258581+00:00
-- url     : https://prove2.me/theorems/49c788a6-cd44-4082-a238-b12ba1f200a4
-- title:
--   The function $A_S$
-- statement:
--   For $x>0$,
--   $$A_S(x)=\sum_{s=1}^S\tilde\gamma^{\,s-1}\exp\Big(-\frac{(s-1)x}{S}\Big)\big(1-e^{-x/S}\big).$$
--   It is the limit of the discounted sum of first-acceptance weights when $np\to x$.
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Eq. (18), p.22

import Mathlib

namespace EffHorizonProphet

/-- The function `A_S(x) = ∑_{s=1}^S γ̃^{s-1} exp(-(s-1)x/S) (1 - e^{-x/S})` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…), Eq. (18),
p.22). With `0`-based `s` the exponent is `s` and the decay power is `γ^s`. -/
noncomputable def AS (S : ℕ) (γ x : ℝ) : ℝ :=
  ∑ s ∈ Finset.range S,
    γ ^ s * Real.exp (-((s : ℝ) * x / (S : ℝ))) * (1 - Real.exp (-(x / (S : ℝ))))

end EffHorizonProphet


