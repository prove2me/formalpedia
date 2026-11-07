-- Prove2me | Definitions.Def_QuasiStrictNE_PLFPData
-- name    : QuasiStrictNE_PLFPData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:07.054646+00:00
-- url     : https://prove2.me/theorems/f2d855bd-b8e3-46b4-bd24-269d9651d64d
-- title:
--   Data of a piecewise-linear fixed-point problem
-- statement:
--   A **piecewise-linear fixed-point problem** assigns to every instance string $I$: whether it is valid, a dimension $d_I$, a list of rational linear inequalities $a^\top x\le b$ defining the domain $D_I\subseteq\mathbb R^{d_I}$, and a map $F_I:\mathbb R^{d_I}\to\mathbb R^{d_I}$. The conditions are the predicate `IsPLFP`.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 6, p.8

import Mathlib

namespace QuasiStrictNE

/-- **The data of a piecewise-linear fixed-point problem** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 6, p.8: "For each
instance I, let FI : DI → DI be a continuous self-map of a nonempty compact convex domain DI. …
1. DI is a polytope defined by a set of linear inequalities").

For each instance string `I`: whether `I` is a valid instance, the dimension `dim I`, the list
`ineqs I` of rational inequalities `a⊤x ≤ b` defining the domain `D_I ⊆ ℝ^{dim I}`, and the map
`F I : ℝ^{dim I} → ℝ^{dim I}`.

**Formalization Note** The conditions of Definition 6 are the separate predicate `IsPLFP`; the domain
is `PLFPData.D`. -/
structure PLFPData where
  valid : List Bool → Prop
  dim : List Bool → ℕ
  ineqs : (I : List Bool) → List ((Fin (dim I) → ℚ) × ℚ)
  F : (I : List Bool) → (Fin (dim I) → ℝ) → (Fin (dim I) → ℝ)

end QuasiStrictNE


