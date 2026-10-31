-- Prove2me | Definitions.Def_DynTargetMV_IsOptimal
-- name    : DynTargetMV_IsOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:38:19.700978+00:00
-- url     : https://prove2.me/theorems/27fa5ac5-6d6d-4c3c-90ed-4d3b320e0177
-- title:
--   Optimal solution of a minimization problem
-- statement:
--   A point $y$ is an optimal solution of the problem $\min_{w\in S} f(w)$ if $y\in S$ and $f(y)\le f(w)$ for every $w\in S$.
--
--   This is the notion of "optimal solution" in every quadratic program of the paper.
-- source:
--   He & Jiang, Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth, Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, (2.10), p.10; (B.2)–(B.4), p.22

import Mathlib

open Set

namespace DynTargetMV

/-- `y` is an optimal solution of `min_{w ∈ S} f w`: it is feasible and attains the minimum.
He & Jiang, *Mean-Variance Portfolio Selection with Dynamic Targets for Expected Terminal Wealth*,
Math. Oper. Res. 47(1):587–615 (2022), doi:10.1287/moor.2021.1142, accepted manuscript, used for (2.10), p.10, (B.2)–(B.4), p.22, (C.14), p.27, (C.18), p.28, (C.22), p.30. -/
def IsOptimal {α : Type*} (f : α → ℝ) (S : Set α) (y : α) : Prop :=
  y ∈ S ∧ IsMinOn f S y

end DynTargetMV


