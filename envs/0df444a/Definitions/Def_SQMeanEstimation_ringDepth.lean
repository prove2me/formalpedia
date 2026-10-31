-- Prove2me | Definitions.Def_SQMeanEstimation_ringDepth
-- name    : SQMeanEstimation_ringDepth
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:04.182689+00:00
-- url     : https://prove2.me/theorems/ac75236f-61b6-42dc-87bc-cbdf7945ab32
-- title:
--   Number of rings $k=\lfloor\log(d)/q\rfloor-2$
-- statement:
--   For $d\in\mathbb N$ and $q>0$,
--   $$
--   k=\Big\lfloor\frac{\log_2 d}{q}\Big\rfloor-2\in\mathbb Z,
--   $$
--   the index of the last ring in the proof of Theorem 3.15.
--
--   **Formalization Note** The paper writes $\log$; it is the binary logarithm, since the ring thresholds are powers of $2$ and the step $2^{1-\lfloor\log(d)/q\rfloor}\le4d^{-1/q}$ on p.18 holds only in base $2$. $k$ is an integer and is negative for small $d$ (e.g. $k=-2$ for $d=2$ and $q\in(1,2)$).
-- source:
--   Feldman, Guzmán, Vempala, Statistical Query Algorithms for Mean Vector Estimation and Stochastic Convex Optimization, arXiv:1512.09170v2, proof of Theorem 3.15, p.17

import Mathlib

namespace SQMeanEstimation

/-- **The number of rings `k = ⌊log(d)/q⌋ − 2`.**
Feldman, Guzmán, Vempala, arXiv:1512.09170v2, proof of Theorem 3.15, p.17: "where
k ≐ ⌊log(d)/q⌋−2".

**Formalization Note.** `log` is the binary logarithm `Real.logb 2` (the ring thresholds are
powers of 2, and the step `2^{1−⌊log(d)/q⌋} ≤ 4d^{−1/q}` on p.18 needs base 2). `k` is an
integer and is negative for small `d` (e.g. `k = −2` for `d = 2`). -/
noncomputable def ringDepth (d : ℕ) (q : ℝ) : ℤ :=
  ⌊Real.logb 2 d / q⌋ - 2

end SQMeanEstimation


