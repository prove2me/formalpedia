-- Prove2me | Definitions.Def_ChapterQgOuterFockEsa
-- name    : ChapterQgOuterFockEsa
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-18T21:06:27.035341+00:00
-- url     : https://prove2.me/theorems/ceeb8946-be52-4441-a241-c46dce87c67f
-- title:
--   Outer Fock space for the quantum gravity Faris-Lavine programme
-- statement:
--   Formal definitions for the outer Fock space in the quantum gravity Faris-Lavine programme.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/main/BookProof/ChapterQgOuterFockEsa.lean

import Definitions.Def_ChapterQg3DGaugeEsa
import Definitions.Def_ChapterQgHermiteOscillatorEsa
import Definitions.Def_ChapterDirectSumEsa
import Mathlib


/-!
# The full quantum-gravity Hamiltonian on the outer Fock space

`BookProof.ChapterQg3DGaugeEsa` proves that the **one-particle** gauge-fixed 3D gravity
Hamiltonian — the `84`-dimensional signed kinetic form plus the `64` squared torsion
constraints — is essentially self-adjoint on the Gauss–polynomial (Hermite) core of
`L²(ℝ⁸⁴)`.  This module lifts that statement to the **outer Fock space**

`𝔉 = ⊕ₙ L²(ℝ^{84n})`,

the `ℓ²`-direct sum of the `n`-particle sectors (the finite-particle Fock space of
distinguishable field-space excitations already used by
`BookProof.ChapterQgOneParticleCcEsa`), and proves that the second-quantized Hamiltonian
`H = Σₚ h^{(p)}` — the one-particle Hamiltonian acting in each particle's own `84`
field-space coordinates — is essentially self-adjoint on the finite-particle core.

## The mechanism

The `n`-particle sector Hamiltonian is *again* a real quadratic Hamiltonian, now in `84n`
degrees of freedom: the momentum block is the one-particle signature repeated once per
particle, and the potential block is the Gram matrix of the `64n` torsion forms
(`gramQ`).  So the general quadratic instrument
`BookProof.FullQuadratic.fqOp_essentiallySelfAdjoint` — the Carleman-flux argument on the
simplex shells, which needs no ellipticity, no definiteness and no sign condition —
applies verbatim to every sector, and `BookProof.DirectSumEsa` glues the sectors.

## What is proved

* `linForm`, `gramQ`, `diagP`, `sqSumPoly`, `sqSumOp` — the operator
  `½ Σⱼ κⱼ πⱼ² + ½ Σᵣ Lᵣ²` for an arbitrary real signature `κ` and an arbitrary finite
  family of linear forms `Lᵣ`, on the Gauss–polynomial core of `L²(ℝᴰ)`;
* `sqSumPoly_eq_fqPoly`, `sqSumOp_eq_fqOp` — its identification with the general
  quadratic Hamiltonian `fqOp (diag κ/2) (gramQ v) 0 0 0`, whence
  `sqSumOp_symmetricOn` and `sqSumOp_essentiallySelfAdjointOn`;
* `pcoord`, `partOf`, `modeOf`, `qgKappaN`, `qgTorsionVecN`, `qgSectorHam` — the
  `n`-particle sector data and the sector Hamiltonian;
* `linForm_qgTorsionVecN`, `qgSectorPoly_eq_sum_particles` — the sector Hamiltonian **is**
  the sum over the particles of the one-particle gravity Hamiltonian, each acting in its
  own particle's coordinates: the torsion forms of particle `p` are the one-particle
  torsion forms in the coordinates `pcoord p ·`;
* `qgSectorHam_symmetricOn`, `qgSectorHam_essentiallySelfAdjointOn` — the sector
  statements;
* `qgOuterFock`, `qgOuterCore`, `qgOuterCore_dense`, `qgOuterHam` — the outer Fock space,
  its finite-particle core and the full Hamiltonian;
* `qgOuterFock_esa` — **the headline**: the full gravity Hamiltonian is essentially
  self-adjoint on the finite-particle core of the outer Fock space, and
  `qgOuterHam_stone_flow` is the complete unitary group `e^{−itH}` it generates;
* `qgOuterN`, `qgOuterN_symmetricOn`, `dsOp_quadForm_nonneg`, `qgOuterN_quadForm_nonneg`,
  `qgOuterN_esa` — the lifted positive one-particle operator `dΓ(N₁)`,
  `N₁ = −Δ + ‖x‖²/4`, which is the comparison operator of the Faris–Lavine route;
  `BookProof.ChapterQgOuterFockFarisLavine` lifts its Friedrichs extension to the outer
  Fock space and runs Faris–Lavine there.

## Honest boundary

The Fock space is the direct sum of the sectors — *distinguishable* excitations, no
symmetrization; the Hamiltonian is particle-number preserving (block diagonal), which is
what makes the direct-sum gluing available.  No interaction between different particle
numbers is included, and nothing here is a statement about a continuum field theory.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.QgOuterFock

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.Qg3DGaugeEsa
open BookProof.QgHermiteOscillator
open BookProof.DirectSumEsa
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. Kinetic-plus-squares Hamiltonians in `d` dimensions -/

variable {D : ℕ}

/-- A linear form `Σᵢ vᵢ xᵢ` in the coordinates. -/
def linForm (v : Fin D → ℝ) : MvPolynomial (Fin D) ℂ :=
  ∑ i : Fin D, ((v i : ℝ) : ℂ) • X i

/-- The Gram matrix `½ Σ_r v_r v_rᵀ` of a finite family of linear forms. -/
def gramQ {R : Type*} [Fintype R] (v : R → Fin D → ℝ) (i j : Fin D) : ℝ :=
  (1 / 2) * ∑ r : R, v r i * v r j

/-- The diagonal momentum matrix `diag(κ/2)`. -/
def diagP (kappa : Fin D → ℝ) (j k : Fin D) : ℝ := if j = k then kappa j / 2 else 0

/-- The polynomial-level Hamiltonian `½ Σ_j κ_j π_j² + ½ Σ_r L_r²`, for an arbitrary real
signature `κ` and an arbitrary finite family of linear forms `L_r = Σᵢ v_r i xᵢ`. -/
def sqSumPoly {R : Type*} [Fintype R] (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    MvPolynomial (Fin D) ℂ →ₗ[ℂ] MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) •
    ((∑ j : Fin D, ((kappa j : ℝ) : ℂ) •
        (YangMillsHermite.momOp j).comp (YangMillsHermite.momOp j))
      + ∑ r : R, (YangMillsHermite.mulOp (linForm (v r))).comp
          (YangMillsHermite.mulOp (linForm (v r))))









/-- The operator `½ Σ_j κ_j π_j² + ½ Σ_r L_r²` on the Gauss–polynomial core of `L²(ℝᴰ)`. -/
def sqSumOp {R : Type*} [Fintype R] (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) :
    (polyGaussCore (d := D)) →ₗ[ℂ] L2d D :=
  (polyGaussCore (d := D)).subtype ∘ₗ coreOp (sqSumPoly kappa v)







/-! ## 2. The `n`-particle sector of the gravity Hamiltonian -/

/-- The coordinate of the `i`-th field-space direction of the `p`-th particle. -/
def pcoord {n : ℕ} (p : Fin n) (i : Fin 84) : Fin (n * 84) := finProdFinEquiv (p, i)

/-- The particle carrying the coordinate `I`. -/
def partOf {n : ℕ} (I : Fin (n * 84)) : Fin n := (finProdFinEquiv.symm I).1

/-- The field-space direction of the coordinate `I`. -/
def modeOf {n : ℕ} (I : Fin (n * 84)) : Fin 84 := (finProdFinEquiv.symm I).2







/-- The `n`-particle signature: the one-particle signature in every particle's block. -/
def qgKappaN (n : ℕ) (I : Fin (n * 84)) : ℝ := qgKappa (modeOf I)

/-- The `n`-particle torsion family: the one-particle torsion forms, one copy per
particle. -/
def qgTorsionVecN (n : ℕ) (r : Fin n × Fin 64) (I : Fin (n * 84)) : ℝ :=
  if partOf I = r.1 then torsionVec r.2 (modeOf I) else 0

/-- **The `n`-particle gravity Hamiltonian** `Σ_p h^{(p)}` on the Gauss–polynomial core of
`L²(ℝ^{84n})`. -/
def qgSectorHam (n : ℕ) : (polyGaussCore (d := n * 84)) →ₗ[ℂ] L2d (n * 84) :=
  sqSumOp (qgKappaN n) (qgTorsionVecN n)









/-- The one-particle torsion form, in the coordinates of the `p`-th particle. -/
def qgTorsionBlock {n : ℕ} (p : Fin n) (m : Fin 64) : MvPolynomial (Fin (n * 84)) ℂ :=
  X (pcoord p (torsionIdx1 m)) - X (pcoord p (torsionIdx2 m))







/-! ## 3. The outer Fock space and the full Hamiltonian -/

/-- **The outer Fock space** over the gravity one-particle space `L²(ℝ⁸⁴)`. -/
abbrev qgOuterFock := lp (fun n : ℕ => L2d (n * 84)) 2

/-- The finite-particle core: the algebraic direct sum of the sector Gauss–polynomial
cores. -/
def qgOuterCore : Submodule ℂ qgOuterFock :=
  dsCore (fun n : ℕ => polyGaussCore (d := n * 84))



/-- **The full gravity Hamiltonian on the outer Fock space.** -/
def qgOuterHam : qgOuterCore →ₗ[ℂ] qgOuterFock := dsOp (fun n : ℕ => qgSectorHam n)







/-! ## 4. The lifted comparison operator -/

/-- **The lift of the positive one-particle comparison operator** `N₁ = −Δ + ‖x‖²/4`. -/
def qgOuterN : qgOuterCore →ₗ[ℂ] qgOuterFock := dsOp (fun n : ℕ => harmCore (d := n * 84))









end

end BookProof.QgOuterFock


