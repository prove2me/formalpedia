-- Prove2me | Definitions.Def_BayesBAI_KLSetting
-- name    : BayesBAI_KLSetting
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:52:54.552648+00:00
-- url     : https://prove2.me/theorems/345b0ae3-3151-4927-b574-25f96114d2e4
-- title:
--   The setting of Lemmas 11 to 13
-- statement:
--   For real $T>0$, this is the set of conditions on $l,u,h$ used in Appendix C:
--   $$
--   T^{-1/6}<\tfrac12,\qquad 2h<T^{-1/6},\qquad l\in[T^{-1/6},1-T^{-1/6}],\qquad l<u<h+l.
--   $$
--   They imply $0<l<u<1$, so that all Bernoulli divergences among $l,u,(l+u)/2$ are defined.
--
--   **Formalization Note.** The paper takes $h(T)=o(T^{-1/6})$ and a threshold $T_0$. Here the inequalities are pointwise, at one $T$, so that constants are visibly universal.
-- source:
--   Komiyama, Ariu, Kato, Qin, Rate-optimal Bayesian Simple Regret in Best Arm Identification, arXiv:2111.09885v3, Appendix C, p.17

import Mathlib

namespace BayesBAI

/-- The setting of Lemmas 11 and 12, Komiyama, Ariu, Kato, Qin, arXiv:2111.09885v3, p.17:
`l ∈ [T^(-1/6), 1 - T^(-1/6)]`, `2h < T^(-1/6)`, `T^(-1/6) < 1/2` and `l < u < h + l`.

**Formalization Note.** The paper takes `h(T) = o(T^(-1/6))` and an abstract `T₀` such that `2h(T) <
T^(-1/6)` and `T^(-1/6) < 1/2` for `T ≥ T₀`. Here the two inequalities are stated pointwise, at one
real `T > 0`, so that the constants of the lemmas are visibly universal. These hypotheses imply `0 < h`,
`0 < l < u < 1`. -/
structure KLSetting (T l u h : ℝ) : Prop where
  /-- `T` is positive. -/
  T_pos : 0 < T
  /-- `T^(-1/6) < 1/2`. -/
  T_large : T ^ (-(1 / 6) : ℝ) < 1 / 2
  /-- `2h(T) < T^(-1/6)`. -/
  h_small : 2 * h < T ^ (-(1 / 6) : ℝ)
  /-- `T^(-1/6) ≤ l`. -/
  l_ge : T ^ (-(1 / 6) : ℝ) ≤ l
  /-- `l ≤ 1 - T^(-1/6)`. -/
  l_le : l ≤ 1 - T ^ (-(1 / 6) : ℝ)
  /-- `l < u`. -/
  l_lt_u : l < u
  /-- `u < h(T) + l`. -/
  u_lt : u < h + l

end BayesBAI


