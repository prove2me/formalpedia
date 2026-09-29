-- Prove2me | Definitions.Def_ChapterFullQuadraticEsa
-- name    : ChapterFullQuadraticEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-13T16:25:18.013218+00:00
-- url     : https://prove2.me/theorems/7f85e51f-d76c-4604-84d0-aa31ac909bf0
-- title:
--   Chapter ChapterFullQuadraticEsa
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.FullQuadraticEsa`, source chapter `BookProof/ChapterFullQuadraticEsa.lean`): Chapter ChapterFullQuadraticEsa
--
--   Generated def bundle for ChapterFullQuadraticEsa. See BookProof/ChapterFullQuadraticEsa.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterFullQuadraticEsa.lean

import Mathlib

import Mathlib
import Definitions.Def_ChapterCarlemanSimplex
import Definitions.Def_ChapterContinuityUnitary
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterYangMillsHermite

/-!
# The general real quadratic Hamiltonian on the Gauss–polynomial core

`BookProof.ChapterModeQuadraticEsa` proves essential self-adjointness, on the plain
Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`, of the general **mode-diagonal**
quadratic Hamiltonian

`∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

for arbitrary real `p, q, s, b, b'`.  What that leaves open is the coupling of **distinct**
modes: `xᵢxⱼ`, `πᵢπⱼ` and `xᵢπⱼ` with `i ≠ j`.

This module removes that restriction.  For arbitrary real matrices `P, Q, S` and arbitrary
real vectors `b, b'` the Weyl-ordered operator

`H = ∑_{i,j} (Pᵢⱼ πᵢπⱼ + Qᵢⱼ xᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

— i.e. *every* real quadratic-plus-linear Hamiltonian in `d` degrees of freedom, with no
ellipticity, no definiteness, no non-degeneracy and no classical equilibrium — is
essentially self-adjoint on the plain Gauss–polynomial core, and hence generates a
complete unitary flow.

## The mechanism

In the ladder variables `xᵢ = aᵢ† + aᵢ`, `πᵢ = (i/2)(aᵢ† − aᵢ)` a product of two of them
is a sum of four hops of the multi-index `α`:

* `α ↦ α + eᵢ + eⱼ` (pair creation), amplitude `√((αᵢ+1)(αⱼ+1))`;
* `α ↦ α − eᵢ − eⱼ` (pair annihilation), amplitude `√(αᵢαⱼ)`;
* `α ↦ α + eᵢ − eⱼ` (mode exchange), amplitude `√(αⱼ(αᵢ+1))`;

plus, when `i = j`, a constant diagonal.  The first two change the total degree `|α|` by
`±2`, the third preserves it.  `BookProof.ChapterCarlemanSimplex` runs the Carleman flux
argument on the simplex shells `{|α| ≤ N}`, which is exactly adapted to this grading: the
mode-exchange hops carry no flux at all (their contribution over a shell is real, because
their amplitude matrix is Hermitian), and the degree-changing hops leak only through a
two-thick boundary shell.

## What is proved

* `lop_lop_hermiteMv_gen`, `weyl_hermiteMv_gen` — the two-index ladder algebra, uniform in
  `i` and `j` (the diagonal `i = j` differs only by an extra constant).
* `fqQuadPoly`, `fqPoly`, `fqOp` — the Hamiltonian, assembled from Weyl-ordered products
  of the canonical pair, hence symmetric on the core (`fqOp_symmetric`).
* `fqQuadPoly_hermiteMv`, `fqOp_hermiteCore` — its ladder form: a real constant diagonal,
  the pair amplitude `Qᵢⱼ − Pᵢⱼ/4 + i Sᵢⱼ/2`, the Hermitian exchange matrix
  `fqExch`, and the one-step amplitude `bᵢ + i b'ᵢ/2` of the first-order part.
* `fqOp_deficiencyTrivialAt`, `fqOp_essentiallySelfAdjoint` — **the headline**, by the
  simplex Carleman criterion `BookProof.CarlemanSimplex.ladderQ_eq_zero`.
* `fqOp_stone_flow` — the resulting complete unitary flow, by Stone's theorem.
* `crossTerm_essentiallySelfAdjoint`, `crossTerm_stone_flow` — the corollary for the
  purely off-diagonal cross term `½(xᵢπⱼ + πⱼxᵢ) + ½(xⱼπᵢ + πᵢxⱼ)`.
* `rotMat`, `fqQuadPoly_rotMat`, `angularMomentum_essentiallySelfAdjoint`,
  `angularMomentum_stone_flow` — an *antisymmetric* exchange matrix realizes the
  angular-momentum generator `xₖπ_l − x_lπₖ`, the compact counterpart of the dilation
  generator; it too is essentially self-adjoint on the core, with a complete flow.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.FullQuadratic

open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.ChapterCarlemanSimplex
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 1. Two-index multi-index arithmetic -/





















/-! ## 2. The two-index ladder algebra -/







/-! ## 3. The Hamiltonian -/

/-- The pair-creation amplitude `Qᵢⱼ − Pᵢⱼ/4 + i Sᵢⱼ/2`. -/
def fqAmp (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : ℂ :=
  ((Q i j - P i j / 4 : ℝ) : ℂ) + Complex.I * ((S i j / 2 : ℝ) : ℂ)

/-- The half of the mode-exchange amplitude coming from the ordered pair `(i, j)`. -/
def fqMl (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : ℂ :=
  ((Q i j + P i j / 4 : ℝ) : ℂ) - Complex.I * ((S i j / 2 : ℝ) : ℂ)

/-- **The mode-exchange amplitude matrix**, which is Hermitian. -/
def fqExch (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : ℂ :=
  fqMl P Q S i j + (starRingEnd ℂ) (fqMl P Q S j i)



/-- The constant diagonal `∑ᵢ (Qᵢᵢ + Pᵢᵢ/4)` of the Weyl-ordered Hamiltonian. -/
def fqSymbol (P Q : Fin d → Fin d → ℝ) : ℝ := ∑ i, (Q i i + P i i / 4)

/-- The quadratic part `∑_{i,j} (Pᵢⱼπᵢπⱼ + Qᵢⱼxᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ))`, on polynomial
coordinates, assembled from Weyl-ordered products of the canonical pair. -/
def fqQuadPoly (P Q S : Fin d → Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, ∑ j, (((P i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly j)
      + ((Q i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j)
      + ((S i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j))

/-- The full symbol: quadratic part plus first-order part. -/
def fqPoly (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  fqQuadPoly P Q S + foPoly b b'

/-- **The general real quadratic Hamiltonian** on the Gauss–polynomial core. -/
def fqOp (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (fqPoly P Q S b b')

/-! ### Symmetry -/







/-! ### The ladder form on polynomials -/











/-! ### Transport to the orthonormal basis -/











/-! ## 4. Essential self-adjointness -/











/-! ## 5. The angular-momentum generators

An **antisymmetric** exchange matrix `S` picks out the rotation generators: since `xᵢ`
and `πⱼ` commute for `i ≠ j` and the diagonal of `S` vanishes,
`∑_{i,j} Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ) = ∑_{i<j} Sᵢⱼ (xᵢπⱼ − xⱼπᵢ)`.  The elementary antisymmetric
matrix therefore realizes the angular-momentum generator `xₖπ_l − x_lπₖ`, the compact
counterpart of the dilation generator of `BookProof.ModeQuadratic`. -/

/-- The elementary antisymmetric matrix `E_{kl} − E_{lk}`. -/
def rotMat (k l : Fin d) : Fin d → Fin d → ℝ := fun i j =>
  (if i = k then (if j = l then (1 : ℝ) else 0) else 0)
    - (if i = l then (if j = k then (1 : ℝ) else 0) else 0)







end

end BookProof.FullQuadratic


