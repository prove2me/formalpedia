-- Prove2me | Definitions.Def_StaticCalendar_rho
-- name    : StaticCalendar_rho
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T04:25:58.603621+00:00
-- url     : https://prove2.me/theorems/5fdff571-2b79-4e28-b7c6-49674e7f5a9c
-- title:
--   Per-period demand $\rho_i$
-- statement:
--   For item $i$, the expected quantity demanded in one period of Algorithm 1:
--
--   $$
--   \rho_i=\sum_{S\in\mathcal S}x(S)\sum_{j:(i,j)\in S}q(i,j,S).
--   $$
-- source:
--   Ma, Simchi-Levi & Zhao, Dynamic Pricing (and Assortment) under a Static Calendar, arXiv:1811.01077v5, p.ec13

import Mathlib
import Definitions.Def_StaticCalendar_DemandModel

namespace StaticCalendar

/-- `ρᵢ := Σ_{S∈𝒮} x(S) Σ_{j:(i,j)∈S} q(i,j,S)`, arXiv:1811.01077v5, p.ec13: the expected quantity
of item `i` demanded in one period of Algorithm 1. -/
noncomputable def rho {n m : ℕ} (I : DemandModel n m) (x : Assortment n m → ℝ) (i : Fin n) : ℝ :=
  ∑ S ∈ I.family, x S * ∑ j ∈ Finset.univ.filter (fun j => (i, j) ∈ S), I.q S i j

end StaticCalendar


