-- Prove2me | Definitions.Def_ChapterLegendrePolynomial
-- name    : ChapterLegendrePolynomial
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:16:01.002118+00:00
-- url     : https://prove2.me/theorems/43db3651-0bd3-49d4-98b7-edb16062ad90
-- title:
--   Chapter LegendrePolynomial
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLegendrePolynomial.lean`): generated def bundle for ChapterLegendrePolynomial. See BookProof/ChapterLegendrePolynomial.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLegendrePolynomial.lean

import Mathlib


/-!
# Legendre polynomials, their differential equation, and the coefficients of
their derivatives

This module provides the one-variable algebraic input needed to identify the
associated Legendre functions / spherical harmonics `Y_{lμ}` of `book.tex` §A.5
with harmonic functions homogeneous of degree `l` (the missing ingredient of
Note 68, recorded until now as an open boundary).  Mathlib has no Legendre
polynomials, so they are built here from Rodrigues' formula.

## Contents

* `iterD_add`, `iterD_X_mul`, `iterD_Xsq_mul` — Leibniz rules for the iterated
  derivative of `X · f` and `X² · f` (the two cases needed below);
* `legendreAux l = (d/dX)ˡ (X²−1)ˡ` and the normalized
  `legendre l = (2ˡ l!)⁻¹ (d/dX)ˡ (X²−1)ˡ` (Rodrigues' formula);
* `legendreAux_ode`, `legendre_ode` — **Legendre's differential equation**
  `(1−X²)P'' − 2X P' + l(l+1) P = 0`;
* `legendre_deriv_ode` — the equation satisfied by the `μ`-th derivative
  `Y = P^{(μ)}` (the Gegenbauer form)
  `(1−X²)Y'' − 2(μ+1) X Y' + (l−μ)(l+μ+1) Y = 0`;
* `legendre_deriv_coeff_rec` — the resulting **two-step coefficient recursion**
  `(j+2)(j+1) Y_{j+2} = −((l−μ)−j)((l−μ)+j+2μ+1) Y_j`, which is exactly the
  condition for the associated solid harmonic to be harmonic;
* `legendre_natDegree_le`, `legendre_deriv_coeff_eq_zero_of_lt`,
  `legendre_deriv_parity` — degree and parity of `Y`, needed to sum the
  associated solid harmonic over the right index set;
* `legendre_coeff_top`, `legendre_ne_zero` — the leading coefficient of `P_l`
  is `(2l)!/(2ˡ (l!)²) ≠ 0`, so the construction is not vacuous.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterLegendrePolynomial

open Polynomial

/-! ## Leibniz rules for the iterated derivative -/









/-! ## Rodrigues' formula and Legendre's equation -/

/-- The unnormalized Rodrigues polynomial `(d/dX)ˡ (X²−1)ˡ`. -/
noncomputable def legendreAux (l : ℕ) : ℝ[X] := derivative^[l] ((X ^ 2 - 1) ^ l)

/-- **The Legendre polynomial** `P_l = (2ˡ l!)⁻¹ (d/dX)ˡ (X²−1)ˡ`. -/
noncomputable def legendre (l : ℕ) : ℝ[X] :=
  C ((2 ^ l * (Nat.factorial l : ℝ))⁻¹) * legendreAux l









/-! ## The coefficient recursion -/





/-! ## Degree, parity and the leading coefficient -/























end BookProof.ChapterLegendrePolynomial


