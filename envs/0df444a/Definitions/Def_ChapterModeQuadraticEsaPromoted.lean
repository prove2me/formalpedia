-- Prove2me | Definitions.Def_ChapterModeQuadraticEsaPromoted
-- name    : ChapterModeQuadraticEsaPromoted
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-11-08T12:10:22.938022+00:00
-- url     : https://prove2.me/theorems/ddb4825e-87a9-4462-b9ad-d4157fd1f7d0
-- title:
--   Mode-quadratic ESAs: the quadratic Hamiltonian on the Gauss-polynomial core
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterModeQuadraticEsa.lean`): the mode-quadratic operator `p·π² + q·x² + s·½(xπ+πx) + b·x + b'·π` on the Gauss-polynomial core, its Weyl-ordered building blocks and the Hermite-basis action.  The platform's served `Def_ChapterModeQuadraticEsa` copy is an empty skeleton, so every consumer statement that says `open BookProof.ModeQuadratic` dies with `unknown namespace`.  Published bundles are immutable, so this bundle re-carries the chapter's DEFINITIONS in the original namespace; the 25 theorem facts stay separate problem nodes.  Consumers add a single `import Definitions.Def_ChapterModeQuadraticEsaPromoted`.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterModeQuadraticEsa.lean

-- §2.13 new-name route (Session 40): the platform's served `Def_ChapterModeQuadraticEsa` copy is a
-- skeleton (no declarations at all), so `open BookProof.ModeQuadratic` in every consumer statement
-- dies with `unknown namespace`.  `submit-definition` cannot update an existing
-- name, so this bundle carries the chapter's DEFINITIONS in the original
-- namespace; its theorem facts stay problem nodes.  Consumers add a single
-- `import Definitions.Def_ChapterModeQuadraticEsaPromoted`.
-- Left to the problem nodes on purpose (theorem facts):
--   sub_single_one_one
--   add_single_apply_self
--   sub_single_apply_self
--   mulXPoly_eq_lop
--   momPoly_eq_lop
--   lop_hermiteMv
--   polySym_mqPoly
--   momsq_hermiteMv
--   xsq_hermiteMv
--   weylxp_hermiteMv
--   mqQuadPoly_hermiteMv
--   ascend2_Lp
--   descend2_Lp
--   mqOp_hermiteCore
--   mqOp_deficiencyTrivialAt
--   mqOp_stone_flow
--   dilation_stone_flow
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterHyperbolicQuadraticEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQuadratureEsa
import Definitions.Def_ChapterStoneBridge
import Mathlib


/-!
# The general mode-diagonal quadratic Hamiltonian on the Gauss–polynomial core

`BookProof.ChapterHermiteCarlemanEsa` proves essential self-adjointness, on the plain
Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`, of

`∑ᵢ cᵢ(πᵢ² + xᵢ²/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

for **arbitrary** real `c, b, b'`.  The quadratic part there is the *harmonic* one: in
each mode it is a multiple of the harmonic oscillator `πᵢ² + xᵢ²/4`, which is diagonal on
the Hermite basis.  The one-mode real quadratic forms make up a three-dimensional space,
spanned by `πᵢ²`, `xᵢ²` and the squeezing (dilation) generator `½(xᵢπᵢ + πᵢxᵢ)`, and
only a one-dimensional subspace of it is diagonal.

This module removes that last restriction: for **arbitrary** real `p, q, s, b, b'` the
operator

`H = ∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

is essentially self-adjoint on the plain Gauss–polynomial core.  Every real quadratic
Hamiltonian which does not couple distinct modes is of this form — elliptic, hyperbolic
or parabolic in each mode, with any signs, with degenerate modes allowed, and with an
arbitrary constant force and boost on top.  In particular (taking `p = q = b = b' = 0`,
`s = 1`) the generator of dilations `½∑ᵢ(xᵢπᵢ + πᵢxᵢ)` is essentially self-adjoint on the
core.

## What is proved

* `lop`, `lop_hermiteMv`, `lop_lop_hermiteMv` — the two-step ladder algebra.  Both `xᵢ`
  and `πᵢ` are of the form `aᵢ† + t aᵢ` up to a scalar, so a product of two of them moves
  the `i`-th excitation number by `0` or `±2`; the `±2` amplitudes are `√((αᵢ+1)(αᵢ+2))`
  and `√(αᵢ(αᵢ−1))`, of size `O(αᵢ)`.
* `mqQuadPoly`, `mqPoly`, `mqOp` — the Hamiltonian, assembled from Weyl-ordered products
  of the canonical pair, hence symmetric on the core (`mqOp_symmetric`).
* `mqQuadPoly_hermiteMv`, `mqOp_hermiteCore` — the ladder form of the Hamiltonian: a real
  diagonal `∑ᵢ(qᵢ + pᵢ/4)(2αᵢ+1)`, a two-step amplitude `qᵢ − pᵢ/4 + i sᵢ/2`, and the
  one-step amplitude `bᵢ + i b'ᵢ/2` of the first-order part.
* `mqOp_deficiencyTrivialAt`, `mqOp_essentiallySelfAdjoint` — **the headline**, by the
  two-step Carleman criterion `BookProof.CarlemanTwoStep.ladder2_eq_zero`.
* `mqOp_stone_flow` — the resulting complete unitary flow, by Stone's theorem.
* `dilation_essentiallySelfAdjoint`, `dilation_stone_flow` — the corollary for the
  generator of dilations.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.ModeQuadratic

open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}

/-! ## 2. The two-step ladder algebra -/

/-- The generic one-step operator `aᵢ† + t aᵢ`.  Both `xᵢ = aᵢ† + aᵢ` and
`πᵢ = (i/2)(aᵢ† − aᵢ)` are of this shape. -/
def lop (t : ℂ) (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  crePoly i + t • annPoly i

/-! ## 3. The Hamiltonian -/

/-- The two-step (squeezing) amplitude `qᵢ − pᵢ/4 + i sᵢ/2` of the mode-diagonal
quadratic Hamiltonian: the coefficient with which it raises the `i`-th excitation number
by two. -/
def mqAmp (p q s : Fin d → ℝ) (i : Fin d) : ℂ :=
  ((q i - p i / 4 : ℝ) : ℂ) + Complex.I * ((s i / 2 : ℝ) : ℂ)

/-- The real diagonal symbol `∑ᵢ (qᵢ + pᵢ/4)(2αᵢ+1)` of the mode-diagonal quadratic
Hamiltonian. -/
def mqSymbol (p q : Fin d → ℝ) (a : Fin d →₀ ℕ) : ℝ :=
  ∑ i, (q i + p i / 4) * (2 * (a i : ℝ) + 1)

/-- The quadratic part `∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ))`, on polynomial
coordinates, assembled from Weyl-ordered products of the canonical pair. -/
def mqQuadPoly (p q s : Fin d → ℝ) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, (((p i : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly i)
      + ((q i : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly i)
      + ((s i : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly i))

/-- The full symbol, quadratic part plus first-order part. -/
def mqPoly (p q s b b' : Fin d → ℝ) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  mqQuadPoly p q s + foPoly b b'

/-- **The general mode-diagonal quadratic Hamiltonian**
`∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` on the Gauss–polynomial
core. -/
def mqOp (p q s b b' : Fin d → ℝ) : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (mqPoly p q s b b')

set_option maxHeartbeats 1600000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive
set_option maxHeartbeats 1600000 in
-- the core coercions make the elaboration of this transport expensive
/-! ## 4. Essential self-adjointness -/

set_option maxHeartbeats 1600000 in
-- the core coercions make the elaboration of the deficiency computation expensive
end

end BookProof.ModeQuadratic


