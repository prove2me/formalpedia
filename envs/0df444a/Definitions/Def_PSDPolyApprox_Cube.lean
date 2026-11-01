-- Prove2me | Definitions.Def_PSDPolyApprox_Cube
-- name    : PSDPolyApprox_Cube
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:14.657889+00:00
-- url     : https://prove2.me/theorems/4ac12ab9-5d12-4258-8cc4-b97660ab7b9d
-- title:
--   The discrete hypercube $H_n=\{-1,1\}^n$
-- statement:
--   The **discrete hypercube** in $n$ dimensions is $H_n=\{-1,1\}^n$, a set with $2^n$ points.
--
--   **Formalization Note** A point is a function from $\{1,\dots,n\}$ to the units of $\mathbb Z$, which are exactly $\pm1$; the real coordinate $x_i\in\{-1,1\}$ is the cast of that unit.
-- source:
--   Fawzi, On polyhedral approximations of the positive semidefinite cone, arXiv:1811.09649v1, §2.1, p.3

import Mathlib

namespace PSDPolyApprox

/-- **The discrete hypercube** `Hₙ = {−1, 1}ⁿ`.
Fawzi, arXiv:1811.09649v1, §2.1, p.3: "Let Hn = {−1, 1}n be the discrete hypercube in n
dimensions."

**Formalization Note.** A point is a function `Fin n → ℤˣ`; the units of `ℤ` are exactly `±1`,
and the real coordinate `xᵢ ∈ {−1, 1}` is the cast `((x i : ℤ) : ℝ)`. `Hₙ` has `2ⁿ` points. -/
abbrev Cube (n : ℕ) : Type := Fin n → ℤˣ

end PSDPolyApprox


