-- Prove2me | Definitions.Def_StaticCalendar_binomMinExp
-- name    : StaticCalendar_binomMinExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:12.369759+00:00
-- url     : https://prove2.me/theorems/bca75da2-5fdb-45b0-b2f3-d82f756edaff
-- title:
--   $\mathbb E[\min\{c,\mathrm{Bin}(T,p)\}]$
-- statement:
--   For $T\in\mathbb N$ and real $p,c$,
--
--   $$
--   \sum_{k=0}^{T}\binom Tk p^k(1-p)^{T-k}\min\{c,k\},
--   $$
--
--   which for $p\in[0,1]$ is the expected value of $\min\{c,\mathrm{Bin}(T,p)\}$.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, (9), p.14

import Mathlib

namespace StaticCalendar

/-- `E[min{c, Bin(T,p)}]`, arXiv:1811.01077v5, p.14, written as the explicit binomial sum. -/
noncomputable def binomMinExp (T : ℕ) (p c : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (T + 1), (T.choose k : ℝ) * p ^ k * (1 - p) ^ (T - k) * min c (k : ℝ)

end StaticCalendar


