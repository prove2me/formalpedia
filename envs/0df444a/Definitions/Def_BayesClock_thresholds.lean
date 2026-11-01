-- Prove2me | Definitions.Def_BayesClock_thresholds
-- name    : BayesClock_thresholds
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:20.65766+00:00
-- url     : https://prove2.me/theorems/2828375c-5a63-44e4-ae40-3afbfd84e8bb
-- title:
--   The threshold $t_S$
-- statement:
--   With $k$ the number of maximal feasible sets, the **threshold** $t_S$ of a set $S$ is the least $t\ge 0$ with
--
--   $$\mathbb E_v[|S(t,v)|]\le\log k.$$
--
--   When $\mathbb E_v[|S(t,v)|]=\log k$ has a solution this is the least solution, which is the paper's definition; the inequality form is footnote 2, needed when the expected count jumps over $\log k$.
--
--   **Formalization Note** An infimum in $\mathbb R_{\ge0}$, attained for $k\ge2$ because $\mu_S$ is right-continuous and tends to $0$. For $k=1$ the set may be empty and the infimum is a junk $0$, so every statement using $t_S$ assumes $k\ge2$. If $\mu_S(0)\le\log k$ then $t_S=0$. Here $\log$ is the base-2 logarithm, the paper's convention: it writes $\ln 2$ for the natural logarithm (§A.1, p.20), and counts $\log m+2$ doubling buckets (p.20).
-- source:
--   Feldman, Gkatzelis, Gravin & Schoepflin, Bayesian and Randomized Clock Auctions, arXiv:2202.09291v1, §3.2, p.7, and footnote 2

import Mathlib
import Definitions.Def_BayesClock_maximalSets
import Definitions.Def_BayesClock_expectedAbove

open MeasureTheory
open scoped NNReal ENNReal

namespace BayesClock

/-- The threshold `tS` of the set `S`: the least `t ≥ 0` with `E_v[|S(t, v)|] ≤ log k`, where `k` is
the number of maximal feasible sets. Feldman et al., arXiv:2202.09291v1, §3.2, p.7 and footnote 2
("we set the threshold tS to be the value satisfying inf_tS E_v[|S(tS, v)|] ≤ log k").

**Formalization Note** `t ↦ E_v[|S(t, v)|]` is non-increasing and right-continuous and tends to `0`,
so for `k ≥ 2` the set below is nonempty and the infimum is attained, and when
`E_v[|S(t, v)|] = log k` has a solution the value is the least one. If `E_v[|S(0, v)|] ≤ log k` then
`tS = 0`. For `k = 1` the set can be empty and `sInf ∅ = 0`, a junk value: every statement using
`thresholds` assumes `2 ≤ k`. `log` is the base-2 logarithm `Real.logb 2`, the paper's convention: it
writes `ln 2` for the natural logarithm (§A.1, p.20), and its doubling buckets number `log m + 2` (p.20). -/
noncomputable def thresholds {N : Type*} [Fintype N] [DecidableEq N] (𝓕 : Finset (Finset N))
    (ν : N → Measure ℝ≥0) (S : Finset N) : ℝ≥0 :=
  sInf {t : ℝ≥0 | expectedAbove ν S t ≤ ENNReal.ofReal (Real.logb 2 (maximalSets 𝓕).card)}

end BayesClock


