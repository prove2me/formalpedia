-- Prove2me | Definitions.Def_ChapterHermiteBandCalculusHigher
-- name    : ChapterHermiteBandCalculusHigher
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-13T16:55:12.695383+00:00
-- url     : https://prove2.me/theorems/207064a0-057e-44f8-8e8b-c4502f4d9d77
-- title:
--   Chapter ChapterHermiteBandCalculusHigher
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteBandCalculusHigher`, source chapter `BookProof/ChapterHermiteBandCalculusHigher.lean`): Chapter ChapterHermiteBandCalculusHigher
--
--   Generated def bundle for ChapterHermiteBandCalculusHigher. See BookProof/ChapterHermiteBandCalculusHigher.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteBandCalculusHigher.lean

import Definitions.Def_ChapterHermiteBandCalculus
import Mathlib

import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterYangMillsHermite

/-!
# The graded band calculus of arbitrary order

`BookProof.ChapterHermiteBandCalculus` develops the band calculus of the product Hermite
basis for the two growths `g1 n = √(n+1)` (a ladder operator) and `g2 n = n + 1` (a
quadratic Hamiltonian), and stops there because the weighted Schur gate it feeds is only
available for quadratic symbols.  The *matrix structure* of an operator of higher degree is
nevertheless well defined and useful — it is the data a spectral certificate consumes — and
this chapter supplies it.

## What is proved

* `gpow m n = √(n+1)^m` — the growth of an operator of order `m`; `gpow 0 = 1`,
  `gpow 1 = g1`, `gpow 2 = g2`, and `gpow` is monotone in `m` (`gpow_mono`).
* `Band.monoR`, `Band.monoG` — widening the band radius and the growth.
* **`Band.compGen`** — the general composition law: composing a band operator of order `m₁`
  and radius `r₁` with one of order `m₂` gives an operator of order `m₁ + m₂` and radius
  `r₁ + r₂`, with the explicit constant `M₁·C₁·C₂·√(r₁+1)^{m₂}`.  The analytic content is
  `√(deg γ + 1) ≤ √(r₁+1)·√(deg α + 1)` whenever `|deg γ − deg α| ≤ r₁`.
* `IsBandR r m T` (explicit band radius) and `IsBandDeg m T` (radius existentially
  quantified) — closed under sums, scalar multiples, finite sums, composition
  (`IsBandR.comp` adds both the radii and the orders) and the order bound (`IsBandR.le`).
* `isBandDeg_one`, `isBandDeg1_mulXPoly`, `isBandDeg1_momPoly`, `isBandDeg1_crePoly`,
  `isBandDeg1_annPoly` — the base cases; `isBand1_iff_isBandDeg_one`,
  `IsBand2.isBandDeg_two`, `IsBandDeg.isBand2` — the comparison with the old predicates.
* **`isBandDeg_mulOp_multiset`** — multiplication by a product of `k` coordinates is a band
  operator of order `k`; **`isBandDeg_mulOp_monomial`** and **`isBandDeg_mulOp`** —
  multiplication by an arbitrary polynomial `p` is a band operator of order
  `p.totalDegree`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HermiteBandHigher

noncomputable section

open MvPolynomial BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.HermiteBand BookProof.YangMillsHermite
open BookProof.NavierStokesFlow.DifferentialL2

variable {d : ℕ}

/-! ## The growth of an operator of order `m` -/

/-- The growth of a band operator of order `m`: `√(n+1)^m`. -/
def gpow (m : ℕ) : ℕ → ℝ := fun n => Real.sqrt ((n : ℝ) + 1) ^ m















/-! ## Widening a band -/





/-! ## The general composition law -/



/-! ## The order predicate -/

/-- `T` is a band operator of **radius `r` and order `m`**: on every Hermite state it
produces boundedly many states whose degrees differ by at most `r`, with coefficients
bounded by `C·√(deg+1)^m`. -/
def IsBandR (r m : ℕ) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) : Prop :=
  ∃ (M : ℕ) (C : ℝ), 0 ≤ C ∧ Band T r M C (gpow m)

/-- `T` is a band operator of order `m`: some band radius, some column bound, and
coefficients bounded by `C·√(deg+1)^m`. -/
def IsBandDeg (m : ℕ) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) : Prop :=
  ∃ r, IsBandR r m T





























/-! ## Comparison with the first- and second-order predicates -/









/-! ## The base cases -/





















/-! ## Multiplication by a polynomial -/





















end

end BookProof.HermiteBandHigher


