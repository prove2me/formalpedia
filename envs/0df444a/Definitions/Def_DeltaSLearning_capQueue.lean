-- Prove2me | Definitions.Def_DeltaSLearning_capQueue
-- name    : DeltaSLearning_capQueue
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:05:49.213014+00:00
-- url     : https://prove2.me/theorems/5cec9343-1d0c-40ad-8ff1-fd6a7b3e709c
-- title:
--   Capped queue $Z_{n+1}=\mathrm{Proj}_{[0,\beta]}(Z_n+A_n-D_n)$
-- statement:
--   For arrivals $A_1,A_2,\dots$, departures $D_1,D_2,\dots$ and a cap $\beta$, the queue of Lemma 5:
--   $$Z_1=0,\qquad Z_{n+1}=\mathrm{Proj}_{[0,\beta]}(Z_n+A_n-D_n),\qquad \mathrm{Proj}_{[0,\beta]}(x)=\max\{0,\min\{x,\beta\}\}.$$
--   In the regret analysis $Z_n$ dominates the inventory carried over above the leader's target.
--
--   **Formalization Note** 0-based indices: the $k$-th value is the paper's $Z_{k+1}$, driven by $A_{k+1}$ and $D_{k+1}$.
-- source:
--   Yuan, Luo, Shi, Marrying SGD with Bandits, SSRN 3329611 (accepted manuscript, Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 5, p.26; projection, p.7

import Mathlib

namespace DeltaSLearning

/-- The capped queue of Lemma 5: `Z_1 = 0` and `Z_{n+1} = Proj_{[0, β]}(Z_n + A_n - D_n)`, with
arrivals `a` and departures `d`, where `Proj_{[0,β]}(x) = max{0, min{x, β}}`.
Yuan, Luo, Shi, SSRN 3329611 (Management Science 2021, doi:10.1287/mnsc.2020.3799), Lemma 5,
p.26, and the projection of p.7.

**Formalization Note** Indices are 0-based: `capQueue β a d k` is the paper's `Z_{k+1}`, and
`a k`, `d k` are the paper's `A_{k+1}`, `D_{k+1}`. -/
noncomputable def capQueue (β : ℝ) (a d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => max 0 (min (capQueue β a d k + a k - d k) β)

end DeltaSLearning


