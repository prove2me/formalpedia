-- Prove2me | Definitions.Def_WeightedCongestionBR_runTime
-- name    : WeightedCongestionBR_runTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:09.112166+00:00
-- url     : https://prove2.me/theorems/7d531498-fa37-4b05-89c6-77761adc74ed
-- title:
--   Running time of a run of Algorithm 1
-- statement:
--   For a run with $k$ steps on a rational instance, with $L$ the largest bit length and a best-response oracle of cost $t_{BR}$ per call,
--
--   $$
--   \mathrm{Time}=(n+m+3)L^2+n\,t_{BR}+(k+1)\,n\,\big(t_{BR}+(2|E|(n+d+2)+3)L^2\big).
--   $$
--
--   The first two terms are Lines 1–5: computing $c_{\max}$, $c_{\min}$ (with $n$ oracle calls), $g$ and the $m$ boundaries. Each of the $k+1$ guard evaluations scans at most $n$ players with one oracle call, two cost evaluations of at most $|E|(n+d+2)$ rational operations, and at most three comparisons. An operation on numbers of bit length at most $L$ costs $L^2$.
--
--   **Formalization Note** The game is the published `HarksKlimm.Consistency.Game n r`: players `Fin n`, resources `Fin r` with $n, r \ge 1$, nonempty finite strategy sets $S_u \subseteq 2^E$, weights $w_u > 0$ (the field `demand`) and cost functions of the load. The paper names no machine and assumes best responses computable in polynomial time; this is that accounting, with the oracle time as a parameter (Reading 1).
-- source:
--   Giannakopoulos, Noarov, Schulz, Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses, arXiv:1810.12806v6, Theorem 4, p.18, and footnote 15, p.15

import Mathlib
import Definitions.Def_HarksKlimm_Consistency_Game
import Definitions.Def_WeightedCongestionBR_RatData
import Definitions.Def_WeightedCongestionBR_Config
import Definitions.Def_WeightedCongestionBR_maxBitLen
set_option autoImplicit false
open scoped NNReal
open HarksKlimm.Consistency

namespace WeightedCongestionBR

/-- The **running time** of a run of Algorithm 1 on a rational instance, in the cost model of the
mission (Reading 1; Giannakopoulos, Noarov, Schulz, *Computing Approximate Equilibria in Weighted Congestion Games via Best-Responses*, arXiv:1810.12806v6, Theorem 4, p.18, and footnote 15, p.15). With `L = maxBitLen`, `k` steps,
and a best-response oracle that costs `t_BR` per call:

`Time := (n + m + 3) L² + n t_BR + (k + 1) n (t_BR + (2|E|(n + d + 2) + 3) L²)`.

The first two terms are Lines 1–5 (computing `c_max`, `c_min`, `g` and the `m` boundaries, with `n`
oracle calls for `BR_u(0)`). Each of the `k + 1` guard evaluations of a run with `k` steps scans at
most `n` players, each with one oracle call, two cost evaluations of at most `|E|(n + d + 2)` rational
operations and at most three comparisons; an operation on numbers of bit length at most `L` costs
`L²`.

**Formalization Note** A run with `k` steps is a list of `k + 1` configurations, so the factor
`k + 1` is `l.length`. The paper names no machine model and assumes best responses computable in
polynomial time; this definition is that accounting, with the oracle time as a parameter. -/
noncomputable def runTime {n r d : ℕ} (G : Game n r) (D : RatData n r d) (m : ℕ)
    (sinit : G.Profile) (tBR : ℕ) (l : List (Config G)) : ℕ :=
  (n + m + 3) * maxBitLen G D m sinit ^ 2 + n * tBR +
    l.length * n * (tBR + (2 * r * (n + d + 2) + 3) * maxBitLen G D m sinit ^ 2)

end WeightedCongestionBR


