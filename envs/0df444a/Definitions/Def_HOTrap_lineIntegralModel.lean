-- Prove2me | Definitions.Def_HOTrap_lineIntegralModel
-- name    : HOTrap_lineIntegralModel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:46:06.197168+00:00
-- url     : https://prove2.me/theorems/c734626c-fa0d-485c-a68e-38c06e73b036
-- title:
--   Scalar model $P(x+v)=\int_0^1\langle W(x+tv),v\rangle\,dt$
-- statement:
--   For a vector field $W$ and a base point $x$,
--   $$
--   P(x+v):=\int_0^1\langle W(x+tv),v\rangle\,dt.
--   $$
--
--   This turns a vector polynomial, which need not be a gradient, into a scalar model.
-- source:
--   Zhou–Sugiyama–Suzuki, Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds, arXiv:2610.02791, Lemma A.7, p.61

import Mathlib

namespace HOTrap

/-- **The scalar model of a vector field** `P(x + v) := ∫₀¹ ⟨W(x + tv), v⟩ dt`. Zhou–Sugiyama–Suzuki, *Finding Stationary Points under Higher-Order Smoothness: Trapping Algorithms and First-Order Lower Bounds*, arXiv:2610.02791, Lemma A.7, p.61.

**Formalization Note** Written at `y = x + v`. -/
noncomputable def lineIntegralModel {d : ℕ} (W : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∫ t in (0 : ℝ)..1, inner ℝ (W (x + t • (y - x))) (y - x)

end HOTrap


