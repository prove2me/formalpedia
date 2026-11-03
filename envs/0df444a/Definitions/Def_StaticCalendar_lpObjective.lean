-- Prove2me | Definitions.Def_StaticCalendar_lpObjective
-- name    : StaticCalendar_lpObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:55.518323+00:00
-- url     : https://prove2.me/theorems/1d315335-dc54-4e80-8e04-9f4d9ce1823e
-- title:
--   Objective of CDLP-S
-- statement:
--   The objective (5) of CDLP-S at $x$ is
--
--   $$
--   T\sum_{S\in\mathcal S}x(S)\sum_{(i,j)\in S}p_j\,q(i,j,S).
--   $$
--
--   Its maximum over feasible $x$ is the benchmark $\mathsf{OPT}_{\mathrm{LP}}$ of the paper.
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, CDLP-S, (5), p.11; p.12

import Mathlib
import Definitions.Def_StaticCalendar_DemandModel

namespace StaticCalendar

/-- The objective (5) of CDLP-S at `x`, arXiv:1811.01077v5, p.11:
`T · Σ_{S∈𝒮} x(S) Σ_{(i,j)∈S} p_j q(i,j,S)`. Its maximum over feasible `x` is `OPT_LP` (p.12). -/
noncomputable def lpObjective {n m : ℕ} (I : DemandModel n m) (T : ℕ)
    (x : Assortment n m → ℝ) : ℝ :=
  (T : ℝ) * ∑ S ∈ I.family, x S * ∑ ij ∈ S, I.p ij.2 * I.q S ij.1 ij.2

end StaticCalendar


