-- Prove2me | Definitions.Def_ChapterGaussCoordCombo
-- name    : ChapterGaussCoordCombo
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:05:55.668708+00:00
-- url     : https://prove2.me/theorems/b7abb64d-458b-42cd-b4f4-58e4cd6ed72c
-- title:
--   Chapter GaussCoordCombo
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterGaussCoordCombo.lean`): generated def bundle for ChapterGaussCoordCombo. See BookProof/ChapterGaussCoordCombo.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterGaussCoordCombo.lean

import Definitions.Def_ChapterHermiteProductCore
import Mathlib


/-!
# Coordinate-wise Hermite combinations on the Gauss–polynomial core

This chapter provides the *quantitative* companion of
`BookProof.ChapterHermiteProductCore`.  There the Gauss–polynomial core of
`L²(ℝᵈ)` was identified with the span of the product Hermite functions; here we
compute Gaussian integrals of the concrete states that will be used to test
quadratic forms on that core.

The states are products, over the coordinates, of **one-variable Hermite
combinations**

`coordCombo i c p K = ∑_{k ≤ K} c k · He_{2k+p}(x_i)`,

with real coefficients `c` and a fixed parity `p ∈ {0,1}`.  The two facts we
need are:

* `gaussInt_coordCombo_sq` — a *relative orthogonality* statement: against any
  polynomial `R` that does not involve `x_i`,
  `∫ (coordCombo i c p K)² R e^{-‖x‖²/2} = (∑_k c k² (2k+p)!) ∫ R e^{-‖x‖²/2}`;
* `gaussInt_prod_coordFactor` — the resulting product rule for a product of such
  combinations, one in each coordinate of a finite set.

Everything rests on the `d`-dimensional Gaussian integration by parts
`BookProof.HermiteProductCore.gaussInt_pderiv`; no new analysis is needed.
-/

namespace BookProof.GaussCoordCombo

open MvPolynomial BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ}

/-! ## Derivatives of the one-coordinate Hermite factors -/











/-! ## Gaussian integration by parts in the creation form -/









/-! ## Relative orthogonality of the Hermite factors -/



/-! ## Coordinate combinations -/

/-- The one-coordinate Hermite combination `∑_{k ≤ K} c k He_{2k+p}(x_i)`. -/
def coordCombo (i : Fin d) (c : ℕ → ℝ) (p K : ℕ) : MvPolynomial (Fin d) ℂ :=
  ∑ k ∈ Finset.range (K + 1), ((c k : ℝ) : ℂ) • hermiteFactor i (2 * k + p)

/-- The Gaussian square norm of a coordinate combination, `∑_k c k² (2k+p)!`. -/
def coordComboSum (c : ℕ → ℝ) (p K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), (c k) ^ 2 * ((2 * k + p).factorial : ℝ)







/-! ## Products over the coordinates -/

/-- A **coordinate factor**: a polynomial living in the single coordinate `i` whose Gaussian
square, relative to any polynomial free of `x_i`, is the constant `s`. -/
def CoordFactor (i : Fin d) (w : MvPolynomial (Fin d) ℂ) (s : ℝ) : Prop :=
  (∀ j, j ≠ i → pderiv j w = 0) ∧
    ∀ R : MvPolynomial (Fin d) ℂ, pderiv i R = 0 → gaussInt (w * (w * R)) = ((s : ℝ) : ℂ) *
      gaussInt R







end

end BookProof.GaussCoordCombo


