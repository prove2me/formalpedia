-- Prove2me | Definitions.Def_EffHorizonProphet_truncGeomMoment
-- name    : EffHorizonProphet_truncGeomMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:41:51.082563+00:00
-- url     : https://prove2.me/theorems/228b6e94-7028-4d5d-88d1-5e623034c350
-- title:
--   Moments of the truncated geometric law
-- statement:
--   For $r\in[0,1)$, let $K$ have the truncated geometric law $P(K=j)\propto r^j$ on $\{0,\dots,S-1\}$. This definition gives its moment
--   $$\mathbb E[K^k]=\frac{\sum_{j=0}^{S-1}j^kr^j}{\sum_{j=0}^{S-1}r^j}.$$
-- source:
--   Kim–Perchet, Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards, STOC 2027 submission (manuscript sha256 2ee8cccf…), Lemmas 13 and 14, p.25

import Mathlib

namespace EffHorizonProphet

/-- The moment `E[K^k]` of the truncated geometric law `P(K = j) ∝ r^j` on `{0, …, S-1}` (Kim–Perchet, *Effective Horizons for Prophet Inequalities with Discounted I.I.D. Rewards*, STOC 2027
submission (manuscript sha256 2ee8cccf…),
Lemmas 13 and 14, p.25), written as the ratio of finite sums `G_k / G_0`.

**Formalization Note** `0 ^ 0 = 1` gives the point mass at `0` for `r = 0`, and `(0 : ℝ) ^ 0 = 1`
makes `k = 0` the total mass. -/
noncomputable def truncGeomMoment (S : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  (∑ j ∈ Finset.range S, (j : ℝ) ^ k * r ^ j) / ∑ j ∈ Finset.range S, r ^ j

end EffHorizonProphet


