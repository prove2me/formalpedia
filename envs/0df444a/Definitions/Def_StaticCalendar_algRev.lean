-- Prove2me | Definitions.Def_StaticCalendar_algRev
-- name    : StaticCalendar_algRev
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:26:39.697197+00:00
-- url     : https://prove2.me/theorems/72a4c288-e152-4394-91ca-317474d4d609
-- title:
--   Expected revenue of Algorithm 1
-- statement:
--   The expected revenue of Algorithm 1 run on $x$ for $k$ periods from starting inventories $c$. The pairs (assortment, demand) of the $k$ periods are independent, each with the law of one period of Algorithm 1, and the revenue is the sequential revenue under static substitution.
--
--   For $c=b$, $k=T$ this is the quantity bounded in Theorem 1. For $k=T-t+1$ it is $\mathsf{Rev}(c,t)$ of the proof.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, Algorithm 1, p.14; independence across periods, p.ec13; Rev(b,t), p.ec11

import Mathlib
import Definitions.Def_StaticCalendar_pathRev
import Definitions.Def_StaticCalendar_period

open MeasureTheory

namespace StaticCalendar

/-- The expected revenue of Algorithm 1, arXiv:1811.01077v5, p.14, run on `x` for `k` periods from
starting inventories `c`, under static substitution: assortments are drawn independently in every
period and demand is independent across periods (p.ec13). With `c = b`, `k = T` this is the
revenue in Theorem 1; `algRev I x c (T - t + 1)` is the paper's `Rev(c,t)`, p.ec11.

**Formalization Note.** The run is the product over `Fin k` of the one-period law `period I x`. -/
noncomputable def algRev {n m : ℕ} (I : DemandModel n m) (x : Assortment n m → ℝ)
    (c : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∫ ω, pathRev I.p k c ω ∂(Measure.pi fun _ : Fin k => period I x)

end StaticCalendar


