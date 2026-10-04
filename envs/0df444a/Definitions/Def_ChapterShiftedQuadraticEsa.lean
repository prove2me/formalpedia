-- Prove2me | Definitions.Def_ChapterShiftedQuadraticEsa
-- name    : ChapterShiftedQuadraticEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-04T07:43:34.58091+00:00
-- url     : https://prove2.me/theorems/7c894458-d6fd-45d1-81c1-b9d5a4ebf17c
-- title:
--   Chapter ShiftedQuadraticEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterShiftedQuadraticEsa.lean`): generated def bundle for ChapterShiftedQuadraticEsa. See BookProof/ChapterShiftedQuadraticEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedQuadraticEsa.lean

import Definitions.Def_ChapterShiftedHermiteCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Mathlib


/-!
# The indefinite quadratic Hamiltonian with an unbounded first-order perturbation

`BookProof.ChapterHyperbolicQuadraticEsa` proves that the diagonal quadratic Hamiltonian
`H_c = ∑ᵢ cᵢ(πᵢ² + xᵢ²/4)` is essentially self-adjoint on the Gauss–polynomial core for
**every** real weight vector `c` — no sign condition — and
`BookProof.ChapterHermiteRelativeBound` adds an arbitrary first-order term
`B = ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` by a Kato–Rellich relative bound, but only for **strictly positive**
weights: in the indefinite case the symbol of `H_c` vanishes on infinitely many
multi-indices, `H_c` does not dominate the number operator, and no relative bound holds.
That indefinite case was the recorded boundary of that module.

This module removes it, by *completing the square* rather than by a perturbation estimate.
For weights `cᵢ ≠ 0` of **arbitrary sign** and arbitrary real `b, b'` the operator

`H = ∑ᵢ (cᵢ(πᵢ² + xᵢ²/4) + bᵢxᵢ + b'ᵢπᵢ)`,  `πᵢ = −i∂/∂xᵢ`,

is symmetric and essentially self-adjoint on the **phase-space translate** of the Hermite
core built in `BookProof.ChapterShiftedHermiteCore`,

`D_{a,k} = { p(x − a) e^{-‖x−a‖²/4} e^{i⟨k,x⟩} }`,  `aᵢ = −2bᵢ/cᵢ`,  `kᵢ = −b'ᵢ/(2cᵢ)`,

which is again a dense subspace of `L²(ℝᵈ)` (`polyGaussCoreT_dense`).  The classical
equilibrium of the completed square is `x = a` with momentum `k`, and on that recentred,
boosted core the Hamiltonian is again diagonal:

`H ψ_{α,a,k} = (∑ᵢ cᵢ(αᵢ + ½) − ∑ᵢ (b'ᵢ²/(4cᵢ) + bᵢ²/cᵢ)) ψ_{α,a,k}`.

## What is proved

* `oscTPoly`, `oscTPoly_apply`, `shiftedHPoly` — the Hamiltonian in the polynomial
  coordinates of the translated, modulated frame;
* `shiftVec`, `boostVec`, `shiftConst`, `shiftedHPoly_eq_quadPoly` — **completing the
  square**: with the classical equilibrium as translation and boost, the first-order term
  disappears and the symbol becomes `H_c` plus a real constant;
* `shiftedHOp`, `shiftedHOp_hermiteTLp` — the operator on the translated core, and its
  diagonal action on the translated, modulated product Hermite functions;
* `shiftedHOp_symmetric`, `shiftedHOp_essentiallySelfAdjoint` — **the headline**;
* `shiftedHPoly_apply_eq_differential` — the **identification**: pointwise, `H` really is
  `∑ᵢ (cᵢ(−∂ᵢ²f + xᵢ²f/4) + bᵢxᵢf + b'ᵢ(−i∂ᵢf))`, with Mathlib's `deriv` along the
  coordinate lines;
* `shiftedHOp_not_bounded` — the operator is genuinely unbounded;
* `shiftedHOp_stone_flow` — the resulting complete unitary Schrödinger flow, by Stone's
  theorem;
* `wave_indefiniteQuadratic_linear_essentiallySelfAdjoint` — the Minkowski corollary:
  `□ + (t² − ‖x‖²)/4 + ⟨b, (t,x)⟩` (an indefinite quadratic potential *and* a constant
  external field) is essentially self-adjoint on a dense core of `L²(ℝ^{1+n})`.

## Honest boundary

`cᵢ ≠ 0` is used exactly once, to solve for the classical equilibrium; if some `cᵢ = 0`
and the corresponding `bᵢ` or `b'ᵢ` is non-zero the square cannot be completed in that
coordinate (the motion is free, and the operator is a different — still essentially
self-adjoint, but not diagonalizable in this basis — object).  The core is the *translated*
Hermite core `D_{a,k}`, not `polyGaussCore`; the two are unitarily equivalent (they are
Weyl translates of one another) but not equal.  Nothing here claims a general
Faris–Lavine potential.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ShiftedQuadratic

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic
open BookProof.ShiftedHermiteCore
open BookProof.FarisLavine
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. The Hamiltonian in the translated, modulated polynomial coordinates -/

/-- The one-coordinate oscillator `πᵢ² + xᵢ²/4` in the translated, modulated frame. -/
def oscTPoly (a k : Vd d) (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  (momTPoly k i).comp (momTPoly k i) + (1/4 : ℂ) • ((mulXTPoly a i).comp (mulXTPoly a i))



/-- The full Hamiltonian `∑ᵢ (cᵢ(πᵢ² + xᵢ²/4) + bᵢxᵢ + b'ᵢπᵢ)` in the polynomial
coordinates of the translated, modulated frame. -/
def shiftedHPoly (a k : Vd d) (c b b' : Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, (((c i : ℝ) : ℂ) • oscTPoly a k i + ((b i : ℝ) : ℂ) • mulXTPoly a i
        + ((b' i : ℝ) : ℂ) • momTPoly k i)



/-! ## 2. Completing the square -/

/-- The classical equilibrium position `aᵢ = −2bᵢ/cᵢ`. -/
def shiftVec (c b : Fin d → ℝ) : Vd d := (WithLp.toLp 2 (fun i => -2 * b i / c i) : Vd d)

/-- The classical equilibrium momentum `kᵢ = −b'ᵢ/(2cᵢ)`. -/
def boostVec (c b' : Fin d → ℝ) : Vd d := (WithLp.toLp 2 (fun i => -b' i / (2 * c i)) : Vd d)

@[simp] theorem shiftVec_apply (c b : Fin d → ℝ) (i : Fin d) :
    (shiftVec c b) i = -2 * b i / c i := rfl

@[simp] theorem boostVec_apply (c b' : Fin d → ℝ) (i : Fin d) :
    (boostVec c b') i = -b' i / (2 * c i) := rfl

/-- The constant produced by completing the square,
`−∑ᵢ (b'ᵢ²/(4cᵢ) + bᵢ²/cᵢ)`. -/
def shiftConst (c b b' : Fin d → ℝ) : ℝ :=
  ∑ i, (-(b' i ^ 2) / (4 * c i) - b i ^ 2 / c i)





/-! ## 3. The operator on the translated core, and its diagonal action -/

/-- **The Hamiltonian on the translated, modulated Hermite core of `L²(ℝᵈ)`.** -/
def shiftedHOp (a k : Vd d) (c b b' : Fin d → ℝ) : (polyGaussCoreT a k) →ₗ[ℂ] L2d d :=
  (polyGaussCoreT a k).subtype ∘ₗ coreOpT a k (shiftedHPoly a k c b b')





/-! ## 4. Symmetry, essential self-adjointness, unboundedness -/













/-! ## 5. The differential identification -/

/-- The coordinate derivative `∂ᵢ` in the translated, modulated frame. -/
def dPolyT (k : Vd d) (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  dPoly i + (Complex.I * ((k i : ℝ) : ℂ)) • LinearMap.id

@[simp] theorem dPolyT_apply (k : Vd d) (i : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    dPolyT k i p = dPoly i p + (Complex.I * ((k i : ℝ) : ℂ)) • p := rfl



















/-! ## 6. The Minkowski corollary -/





end

end BookProof.ShiftedQuadratic


