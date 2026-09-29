-- Prove2me | Definitions.Def_ChapterHermiteRelativeBound
-- name    : ChapterHermiteRelativeBound
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:40:51.049352+00:00
-- url     : https://prove2.me/theorems/dd1e9760-6d8b-4206-aefe-75f29553f594
-- title:
--   `BookProof.ChapterHyperbolicQuadraticEsa` proves that `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` is essentially self-adjoint on the Gau ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HermiteRelativeBound`, source chapter `BookProof/ChapterHermiteRelativeBound.lean`).
--
--   `BookProof.ChapterHyperbolicQuadraticEsa` proves that `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)` for *every* real weight vector `c`, and widens the potential class by a **bounded** real multiplier (Kato–Rellich). This module widens it by an **unbounded** perturbation, in the elliptic case `cᵢ ≥ c₀ > 0`:
--
--   * `posL`, `momL`, `oscL` — the position `xᵢ`, the momentum `πᵢ = −i∂ᵢ` and the one-coordinate oscillator `πᵢ² + xᵢ²/4`, as operators from the core into `L²`; * `posL_symmetric`, `momL_symmetric` — both are symmetric on the core (Gaussian integration by parts, through `BookProof.YangMillsHermite.PolySym`); * `inner_oscL_eq` — the form identity `⟪u, (πᵢ² + xᵢ²/4)u⟫ = ‖πᵢu‖² + ‖xᵢu‖²/4`; * `re_inner_oscL_le_quadOp` — for weights `cᵢ ≥ c₀ > 0` the oscillator form of a single coordinate is dominated by the form of `H_c`: `c₀⟪u, oscᵢ u⟫ ≤ ⟪u, H_c u⟫` (the symbols satisfy `c₀(αᵢ + ½) ≤ ∑ⱼ cⱼ(αⱼ + ½)`); * `norm_posL_le`, `norm_momL_le` — consequently `xᵢ` and `πᵢ` are `H_c`-bounded with *arbitrarily small* relative bound: `‖xᵢu‖ ≤ ε‖H_c u‖ + (2/(c₀ε))‖u‖`, and the same for `πᵢ`; * HEADLINE `quadOp_add_firstOrder_essentiallySelfAdjoint` — therefore `H_c + B` is essentially self-adjoint on the same core for every **first-order** perturbation `B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` with real coefficients. The perturbation is genuinely unbounded, so this is outside the reach of the bounded Kato–Rellich statement; * `hermiteMvBasis_repr_quadOp` — the product Hermite basis *is* a diagonalizing unitary for `H_c`: in those coordinates the operator is multiplication by the real symbol `∑ᵢ cᵢ(αᵢ + ½)`; * `harmonicOsc_add_linearPotential_essentiallySelfAdjoint` and `foOp_linear_apply_eq_mul` — the physical corollary: the Stark-shifted oscillator `−Δ + ‖x‖²/4 + ⟨b, x⟩` (a harmonic oscillator in a constant external field) is essentially self-adjoint on the Hermite core, the perturbation being multiplication by the unbounded real function `x ↦ ⟨b, x⟩`.
--
--   Two general instruments are proved on the way and are reusable: `apply_sum_of_diagonal` and `re_inner_diagonal_le` — a diagonal operator with a real symbol acts on a finite combination of the diagonalizing vectors coefficientwise, and the quadratic forms of two diagonal operators are ordered by their symbols.
--
--   The strict positivity `cᵢ ≥ c₀ > 0` is used, and is not removable by this argument: in the hyperbolic (mixed sign) case the symbol `∑ⱼ cⱼ(αⱼ + ½)` vanishes on an infinite set of multi-indices, so `H_c` does not dominate the number operator and no relative bound of the above kind can hold. The general Faris–Lavine potential (bounded above by a quadratic) therefore stays open, as recorded in `CONSOLIDATED_PLAN.md`.
--
--   Everything is `sorry`-free and `axiom`-free.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHermiteRelativeBound.lean

import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterKatoRellichRelative
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesDifferentialL2

import Mathlib

/-!
# Relatively bounded (unbounded) perturbations of the diagonal quadratic Hamiltonian

`BookProof.ChapterHyperbolicQuadraticEsa` proves that
`H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` is essentially self-adjoint on the Gauss–polynomial
(product Hermite) core of `L²(ℝᵈ)` for *every* real weight vector `c`, and widens the
potential class by a **bounded** real multiplier (Kato–Rellich).  This module widens it by
an **unbounded** perturbation, in the elliptic case `cᵢ ≥ c₀ > 0`:

* `posL`, `momL`, `oscL` — the position `xᵢ`, the momentum `πᵢ = −i∂ᵢ` and the
  one-coordinate oscillator `πᵢ² + xᵢ²/4`, as operators from the core into `L²`;
* `posL_symmetric`, `momL_symmetric` — both are symmetric on the core (Gaussian
  integration by parts, through `BookProof.YangMillsHermite.PolySym`);
* `inner_oscL_eq` — the form identity `⟪u, (πᵢ² + xᵢ²/4)u⟫ = ‖πᵢu‖² + ‖xᵢu‖²/4`;
* `re_inner_oscL_le_quadOp` — for weights `cᵢ ≥ c₀ > 0` the oscillator form of a single
  coordinate is dominated by the form of `H_c`: `c₀⟪u, oscᵢ u⟫ ≤ ⟪u, H_c u⟫` (the symbols
  satisfy `c₀(αᵢ + ½) ≤ ∑ⱼ cⱼ(αⱼ + ½)`);
* `norm_posL_le`, `norm_momL_le` — consequently `xᵢ` and `πᵢ` are `H_c`-bounded with
  *arbitrarily small* relative bound: `‖xᵢu‖ ≤ ε‖H_c u‖ + (2/(c₀ε))‖u‖`, and the same for
  `πᵢ`;
* HEADLINE `quadOp_add_firstOrder_essentiallySelfAdjoint` — therefore `H_c + B` is
  essentially self-adjoint on the same core for every **first-order** perturbation
  `B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` with real coefficients.  The perturbation is genuinely
  unbounded, so this is outside the reach of the bounded Kato–Rellich statement;
* `hermiteMvBasis_repr_quadOp` — the product Hermite basis *is* a diagonalizing unitary
  for `H_c`: in those coordinates the operator is multiplication by the real symbol
  `∑ᵢ cᵢ(αᵢ + ½)`;
* `harmonicOsc_add_linearPotential_essentiallySelfAdjoint` and
  `foOp_linear_apply_eq_mul` — the physical corollary: the Stark-shifted oscillator
  `−Δ + ‖x‖²/4 + ⟨b, x⟩` (a harmonic oscillator in a constant external field) is
  essentially self-adjoint on the Hermite core, the perturbation being multiplication by
  the unbounded real function `x ↦ ⟨b, x⟩`.

Two general instruments are proved on the way and are reusable: `apply_sum_of_diagonal`
and `re_inner_diagonal_le` — a diagonal operator with a real symbol acts on a finite
combination of the diagonalizing vectors coefficientwise, and the quadratic forms of two
diagonal operators are ordered by their symbols.

## Honest boundary

The strict positivity `cᵢ ≥ c₀ > 0` is used, and is not removable by this argument: in
the hyperbolic (mixed sign) case the symbol `∑ⱼ cⱼ(αⱼ + ½)` vanishes on an infinite set of
multi-indices, so `H_c` does not dominate the number operator and no relative bound of the
above kind can hold.  The general Faris–Lavine potential (bounded above by a quadratic)
therefore stays open, as recorded in `CONSOLIDATED_PLAN.md`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.HermiteRelative

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

/-! ## Instruments: diagonal operators on an orthonormal family -/

section Diagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}







end Diagonal

variable {d : ℕ}

/-! ## The canonical pair and the one-coordinate oscillator on the core -/











/-- The position operator `xᵢ` as a map from the core into `L²`. -/
def posL (i : Fin d) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (mulXPoly i)

/-- The momentum operator `πᵢ = −i∂ᵢ` as a map from the core into `L²`. -/
def momL (i : Fin d) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (momPoly i)

/-- The one-coordinate oscillator `πᵢ² + xᵢ²/4` as a map from the core into `L²`. -/
def oscL (i : Fin d) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (oscPoly i)

/-! ### Symmetry, by Gaussian integration by parts -/















/-! ### The oscillator form -/





/-! ### The diagonal action of the oscillator and of `H_c` -/





/-! ### The relative bounds -/











/-! ## The first-order perturbation -/

/-- The first-order symbol `∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)`, on polynomial coordinates. -/
def foPoly (b b' : Fin d → ℝ) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, (((b i : ℝ) : ℂ) • mulXPoly i + ((b' i : ℝ) : ℂ) • momPoly i)

/-- **The first-order perturbation** `B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` on the Hermite core. -/
def foOp (b b' : Fin d → ℝ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (foPoly b b')

















/-! ## The diagonalizing unitary -/



/-! ## The Stark-shifted oscillator -/





end

end BookProof.HermiteRelative


