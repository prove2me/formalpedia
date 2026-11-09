-- Prove2me | Definitions.Def_CubeSampling_ksF
-- name    : CubeSampling_ksF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:15:31.742194+00:00
-- url     : https://prove2.me/theorems/85bca7fd-9fc7-4310-a55f-5342d8d76716
-- title:
--   Kirshner–Samorodnitsky rate $F(p,q)$ of (6)
-- statement:
--   For $p \ge 2$ and $0 < q < 1/2$, with $z \in (0,1)$ the solution of the root equation,
--   $$
--   F(p,q) = \log\frac{(1+z)^p + (1-z)^p}{2} - pq\log z - \frac p2 H_2(q),
--   $$
--   and at the endpoints $F(p,0) = 0$, $F(p,1/2) = (p/2 - 1)\log 2$. It is the exponent of the sharp moment bound of Theorem 3.1.
--
--   **Formalization Note** The root is chosen by Hilbert's choice operator among the solutions of the root equation (the paper asserts uniqueness; existence is verified separately). Powers are real powers; $H_2$ is the natural-log binary entropy. Values outside $[0,1/2]$ are not used.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), (6), p.12

import Mathlib
import Definitions.Def_CubeSampling_ksRoot

namespace CubeSampling

/-- The Kirshner–Samorodnitsky rate `F(p, q)` of (6) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), (6), p.12): for `p ≥ 2`, `0 < q < 1/2`,
`F(p, q) = log(((1 + z)^p + (1 − z)^p)/2) − pq log z − (p/2) H₂(q)` with `z ∈ (0, 1)` the solution of
`ksRoot p q z`; `F(p, 0) = 0` and `F(p, 1/2) = (p/2 − 1) log 2`.

**Formalization Note** `z` is chosen by `Classical.epsilon` among the solutions; the paper states
the solution is unique for `p ≥ 2`, `0 < q < 1/2` (existence is proved in the sanity file). Powers
are real powers; `H₂` is `Real.binEntropy`. Outside `[0, 1/2]` the value is not used. -/
noncomputable def ksF (p q : ℝ) : ℝ :=
  if q = 0 then 0 else if q = 1 / 2 then (p / 2 - 1) * Real.log 2 else
    Real.log (((1 + Classical.epsilon (ksRoot p q)) ^ p + (1 - Classical.epsilon (ksRoot p q)) ^ p) / 2)
      - p * q * Real.log (Classical.epsilon (ksRoot p q)) - p / 2 * Real.binEntropy q

end CubeSampling


