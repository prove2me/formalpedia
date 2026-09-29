-- Prove2me | Definitions.Def_ChapterHyperbolicQuadraticEsa
-- name    : ChapterHyperbolicQuadraticEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-10T00:32:19.600933+00:00
-- url     : https://prove2.me/theorems/313b970b-9ad0-4517-be6a-b3f57fb7d43e
-- title:
--   `BookProof.ChapterStrichartzWave` proves essential self-adjointness of every constant-coefficient operator with a real s ...
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.HyperbolicQuadraticEsa`, source chapter `BookProof/ChapterHyperbolicQuadraticEsa.lean`).
--
--   `BookProof.ChapterStrichartzWave` proves essential self-adjointness of every constant-coefficient operator with a real symbol — in particular of the wave operator `□ = −∂_t² + Δ_x` — on the Schwartz core of `L²(ℝ^{1+n})`, and `BookProof.ChapterWaveUnboundedPotential` does the same for multiplication by a real potential of temperate growth. Both of those are *commuting* halves: the first is a pure Fourier multiplier, the second a pure multiplication operator. `BookProof.ChapterHarmonicOscillatorEsa` settles the prototypical **non-commuting** mixture in the *elliptic* normalization, `−d²/dx² + x²/4` on `L²(ℝ)`.
--
--   What was recorded as open (`STRICHARTZ_WAVE_ESA.md`, `CONSOLIDATED_PLAN.md` §9.5 and the Lean-specialist backlog item A1) is the non-commuting mixture in the **hyperbolic** normalization: `□ + V` with `V` in the Faris–Lavine class (bounded above by a quadratic — the sign that the sign warning of `STRICHARTZ_WAVE_ESA.md` singles out; with the opposite sign the operator genuinely fails to be essentially self-adjoint). This module proves that mixture for the quadratic potentials that are diagonal in the coordinates, by exhibiting the joint eigenbasis: the product Hermite functions of `BookProof.ChapterHermiteProductBasis`.
--
--   For an arbitrary real weight vector `c : Fin d → ℝ` — *no sign condition* — let
--
--   `H_c = ∑ᵢ cᵢ (−∂²/∂xᵢ² + xᵢ²/4)`
--
--   on the Gauss–polynomial (product Hermite) core `polyGaussCore` of `L²(ℝᵈ)`.
--
--   * `oscPoly`, `oscPoly_apply`, `oscPoly_hermiteMv` — the one-coordinate oscillator `−∂ᵢ² + xᵢ²/4`, written with the *canonical pair* `momPoly i = −i∂ᵢ`, `mulXPoly i = xᵢ·` of `BookProof.ChapterNavierStokesDifferentialL2`, is the number operator `aᵢ†aᵢ + ½` on the product Hermite functions; * `quadOp`, `quadSymbol`, `quadOp_hermiteMvLp` — `H_c` on the core, and its diagonal action `H_c ψ_α = (∑ᵢ cᵢ(αᵢ + ½)) ψ_α`; * `quadPoly_apply_eq_differential` — the **identification**: pointwise, `H_c` really is `∑ᵢ cᵢ(−∂ᵢ²f + (xᵢ²/4)f)` with Mathlib's `deriv` taken twice along the `i`-th coordinate line; * `quadOp_symmetric` and `quadOp_essentiallySelfAdjoint` — **the headline**: `H_c` is symmetric and essentially self-adjoint on the Hermite core, for every real `c`; * `quadOp_not_bounded`, `polyGaussCore_dense_L2'` — the operator is genuinely unbounded as soon as some `cᵢ ≠ 0`, and the core is dense, so the statement is not an artefact; * `minkowskiCoeff`, `wave_indefiniteQuadratic_essentiallySelfAdjoint` and `minkowski_apply_eq_differential` — the case `c = (1, −1, …, −1)`: in the convention `□ = −∂_t² + Δ_x` of `BookProof.ChapterStrichartzWave` this is
--
--   `□ + V`, `V(t, x) = (t² − ‖x‖²)/4`,
--
--   an unbounded potential which is bounded above by the quadratic `(t² + ‖x‖²)/4` — the Faris–Lavine sign — and which does not commute with `□`.
--
--   * `quadOp_add_boundedPotential_essentiallySelfAdjoint` and `quadOp_add_realBoundedPotential_essentiallySelfAdjoint` — the potential class is widened by the already-proved Kato–Rellich theorem: `H_c + W` is still essentially self-adjoint on the same core for every real, essentially bounded `W`, so the potential may be any *diagonal quadratic plus bounded* real function.
--
--   Two general instruments are proved on the way and are reusable: `symmetricOn_of_diagonal` and `deficiencyTrivialAt_of_diagonal` — an operator that is diagonal with a *real* symbol on an orthonormal family spanning its domain is symmetric, and its deficiency spaces at non-real points vanish as soon as the family is total.
--
--   The potential is quadratic and diagonal in the coordinates (`∑ᵢ cᵢxᵢ²/4`); a general Faris–Lavine potential bounded above by a quadratic is *not* covered — the joint eigenbasis is what makes the argument work, and it exists only for the diagonal quadratic family. Nothing here claims anything for the opposite sign (the `−d²/dx² − x⁴` class, whose deficien
--
--   ...
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterHyperbolicQuadraticEsa.lean

import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterWaveBoundedPotential
import Mathlib

import Mathlib

/-!
# The hyperbolic operator with an indefinite quadratic potential

`BookProof.ChapterStrichartzWave` proves essential self-adjointness of every
constant-coefficient operator with a real symbol — in particular of the wave operator
`□ = −∂_t² + Δ_x` — on the Schwartz core of `L²(ℝ^{1+n})`, and
`BookProof.ChapterWaveUnboundedPotential` does the same for multiplication by a real
potential of temperate growth.  Both of those are *commuting* halves: the first is a pure
Fourier multiplier, the second a pure multiplication operator.
`BookProof.ChapterHarmonicOscillatorEsa` settles the prototypical **non-commuting** mixture
in the *elliptic* normalization, `−d²/dx² + x²/4` on `L²(ℝ)`.

What was recorded as open (`STRICHARTZ_WAVE_ESA.md`, `CONSOLIDATED_PLAN.md` §9.5 and the
Lean-specialist backlog item A1) is the non-commuting mixture in the **hyperbolic**
normalization: `□ + V` with `V` in the Faris–Lavine class (bounded above by a quadratic —
the sign that the sign warning of `STRICHARTZ_WAVE_ESA.md` singles out; with the opposite
sign the operator genuinely fails to be essentially self-adjoint).  This module proves that
mixture for the quadratic potentials that are diagonal in the coordinates, by exhibiting
the joint eigenbasis: the product Hermite functions of
`BookProof.ChapterHermiteProductBasis`.

## What is proved

For an arbitrary real weight vector `c : Fin d → ℝ` — *no sign condition* — let

`H_c = ∑ᵢ cᵢ (−∂²/∂xᵢ² + xᵢ²/4)`

on the Gauss–polynomial (product Hermite) core `polyGaussCore` of `L²(ℝᵈ)`.

* `oscPoly`, `oscPoly_apply`, `oscPoly_hermiteMv` — the one-coordinate oscillator
  `−∂ᵢ² + xᵢ²/4`, written with the *canonical pair* `momPoly i = −i∂ᵢ`,
  `mulXPoly i = xᵢ·` of `BookProof.ChapterNavierStokesDifferentialL2`, is the number
  operator `aᵢ†aᵢ + ½` on the product Hermite functions;
* `quadOp`, `quadSymbol`, `quadOp_hermiteMvLp` — `H_c` on the core, and its diagonal
  action `H_c ψ_α = (∑ᵢ cᵢ(αᵢ + ½)) ψ_α`;
* `quadPoly_apply_eq_differential` — the **identification**: pointwise, `H_c` really is
  `∑ᵢ cᵢ(−∂ᵢ²f + (xᵢ²/4)f)` with Mathlib's `deriv` taken twice along the `i`-th coordinate
  line;
* `quadOp_symmetric` and `quadOp_essentiallySelfAdjoint` — **the headline**: `H_c` is
  symmetric and essentially self-adjoint on the Hermite core, for every real `c`;
* `quadOp_not_bounded`, `polyGaussCore_dense_L2'` — the operator is genuinely unbounded as
  soon as some `cᵢ ≠ 0`, and the core is dense, so the statement is not an artefact;
* `minkowskiCoeff`, `wave_indefiniteQuadratic_essentiallySelfAdjoint` and
  `minkowski_apply_eq_differential` — the case `c = (1, −1, …, −1)`: in the convention
  `□ = −∂_t² + Δ_x` of `BookProof.ChapterStrichartzWave` this is

  `□ + V`,  `V(t, x) = (t² − ‖x‖²)/4`,

  an unbounded potential which is bounded above by the quadratic `(t² + ‖x‖²)/4` — the
  Faris–Lavine sign — and which does not commute with `□`.

* `quadOp_add_boundedPotential_essentiallySelfAdjoint` and
  `quadOp_add_realBoundedPotential_essentiallySelfAdjoint` — the potential class is
  widened by the already-proved Kato–Rellich theorem: `H_c + W` is still essentially
  self-adjoint on the same core for every real, essentially bounded `W`, so the
  potential may be any *diagonal quadratic plus bounded* real function.

Two general instruments are proved on the way and are reusable:
`symmetricOn_of_diagonal` and `deficiencyTrivialAt_of_diagonal` — an operator that is
diagonal with a *real* symbol on an orthonormal family spanning its domain is symmetric,
and its deficiency spaces at non-real points vanish as soon as the family is total.

## Honest boundary

The potential is quadratic and diagonal in the coordinates (`∑ᵢ cᵢxᵢ²/4`); a general
Faris–Lavine potential bounded above by a quadratic is *not* covered — the joint
eigenbasis is what makes the argument work, and it exists only for the diagonal quadratic
family.  Nothing here claims anything for the opposite sign (the `−d²/dx² − x⁴` class,
whose deficiency indices are non-zero).
-/

namespace BookProof.HyperbolicQuadratic

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

/-! ## An instrument: operators that are diagonal on an orthonormal family -/

section Diagonal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*}





end Diagonal

variable {d : ℕ}

/-! ## The one-coordinate oscillator in the canonical pair -/

/-- The one-coordinate harmonic oscillator `−∂ᵢ² + xᵢ²/4`, written with the canonical pair
`πᵢ = −i∂ᵢ` and `xᵢ·` of `BookProof.ChapterNavierStokesDifferentialL2`: `πᵢ² + xᵢ²/4`. -/
def oscPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  (momPoly i).comp (momPoly i) + (1/4 : ℂ) • ((mulXPoly i).comp (mulXPoly i))











/-! ## The Hamiltonian `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` -/

/-- The weighted sum of the one-coordinate oscillators, in polynomial coordinates. -/
def quadPoly (c : Fin d → ℝ) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, ((c i : ℝ) : ℂ) • oscPoly i

/-- The symbol of `H_c` on the product Hermite function `ψ_α`. -/
def quadSymbol (c : Fin d → ℝ) (a : Fin d →₀ ℕ) : ℝ := ∑ i, c i * ((a i : ℝ) + 1/2)



/-- **The Hamiltonian `H_c` on the Gauss–polynomial (Hermite) core of `L²(ℝᵈ)`.** -/
def quadOp (c : Fin d → ℝ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (quadPoly c)





/-! ## Symmetry and essential self-adjointness -/











/-! ## The operator is unbounded -/





/-! ## The differential identification -/

/-- The coordinate derivative in polynomial coordinates:
`∂ᵢ(p·e^{−‖x‖²/4}) = (∂ᵢp − (xᵢ/2)p)·e^{−‖x‖²/4}`. -/
def dPoly (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ where
  toFun p := pderiv i p - (1/2 : ℂ) • (X i * p)
  map_add' p q := by
    simp only [map_add, mul_add, smul_add]
    abel
  map_smul' r p := by
    simp only [RingHom.id_apply, Derivation.map_smul_of_tower, mul_smul_comm, smul_sub]
    rw [smul_comm]























/-! ## A bounded perturbation of the potential (Kato–Rellich) -/





/-! ## The Minkowski case: `□ + V` with an indefinite quadratic potential -/

/-- The Minkowski weights `(1, −1, …, −1)`: coordinate `0` is the time. -/
def minkowskiCoeff (n : ℕ) : Fin (1 + n) → ℝ := fun i => if i = 0 then 1 else -1





end

end BookProof.HyperbolicQuadratic


