-- Prove2me | Definitions.Def_BrownianEnergyRep_TimeGrid
-- name    : BrownianEnergyRep_TimeGrid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:32.789195+00:00
-- url     : https://prove2.me/theorems/e235c9d2-c214-485e-abd7-ded311dbd499
-- title:
--   Partitions of $[0,t]$ and their mesh
-- statement:
--   A partition $0=s_0\le s_1\le\dots\le s_k=t$ of $[0,t]$, and its mesh $\max_i(s_{i+1}-s_i)$. Stochastic integrals in this mission are limits along partitions whose mesh tends to $0$.
--
--   **Formalization Note** The empty partition of $[0,0]$ has mesh $0$.
-- source:
--   Albeverio, Driver, Gordina, Vershik, Equivalence of the Brownian and energy representations, arXiv:1511.07378v1, Definition 2.8, p.5

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology ContDiff RealInnerProductSpace

namespace BrownianEnergyRep

/-- A partition `0 = s₀ ≤ s₁ ≤ … ≤ s_k = t` of `[0,t]`. -/
structure TimeGrid (t : ℝ) where
  k : ℕ
  s : Fin (k + 1) → ℝ
  zero : s 0 = 0
  last : s (Fin.last k) = t
  mono : Monotone s

/-- The mesh of a partition; `0` for the empty partition of `[0,0]`. -/
noncomputable def TimeGrid.mesh {t : ℝ} (π : TimeGrid t) : ℝ :=
  ⨆ i : Fin π.k, (π.s i.succ - π.s i.castSucc)

end BrownianEnergyRep


