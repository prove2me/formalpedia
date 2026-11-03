-- Prove2me | Definitions.Def_StaticCalendar_IsLPFeasible
-- name    : StaticCalendar_IsLPFeasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:50.515094+00:00
-- url     : https://prove2.me/theorems/d2335004-4b95-49fd-a55f-cee612da30a0
-- title:
--   Feasible solutions of CDLP-S
-- statement:
--   A vector $(x(S))_{S\in\mathcal S}$ is feasible for the stationary choice-based LP with horizon $T$ and inventories $b_1,\dots,b_n$ when
--
--   $$
--   T\sum_{S\in\mathcal S}x(S)\sum_{j:(i,j)\in S}q(i,j,S)\le b_i\quad(i=1,\dots,n),\qquad \sum_{S\in\mathcal S}x(S)=1,\qquad x(S)\ge0 .
--   $$
--
--   These are constraints (6)–(8). The number $x(S)$ is the probability of offering $S$ in a period.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, CDLP-S, (6)–(8), p.11

import Mathlib
import Definitions.Def_StaticCalendar_DemandModel

namespace StaticCalendar

/-- Feasible solutions of CDLP-S, constraints (6)–(8), arXiv:1811.01077v5, p.11:
`T · Σ_{S∈𝒮} x(S) Σ_{j:(i,j)∈S} q(i,j,S) ≤ bᵢ` for all `i`, `Σ_{S∈𝒮} x(S) = 1`, and `x(S) ≥ 0`.

**Formalization Note.** `x` is a function on all assortments; only its values on `family` matter. -/
structure IsLPFeasible {n m : ℕ} (I : DemandModel n m) (T : ℕ) (b : Fin n → ℝ)
    (x : Assortment n m → ℝ) : Prop where
  /-- (8) -/
  nonneg : ∀ S ∈ I.family, 0 ≤ x S
  /-- (7) -/
  sum_one : ∑ S ∈ I.family, x S = 1
  /-- (6) -/
  capacity : ∀ i, (T : ℝ) * ∑ S ∈ I.family, x S *
    ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ S), I.q S i j ≤ b i

end StaticCalendar


