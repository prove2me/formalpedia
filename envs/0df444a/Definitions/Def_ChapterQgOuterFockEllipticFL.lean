-- Prove2me | Definitions.Def_ChapterQgOuterFockEllipticFL
-- name    : ChapterQgOuterFockEllipticFL
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-21T11:23:40.154188+00:00
-- url     : https://prove2.me/theorems/924fb430-0597-4a3f-a6d2-274009e18a33
-- title:
--   The Lean 4 theorem `quadForm_comp_self` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterQgOuterFockEllipticFL.lean`): generated def bundle for ChapterQgOuterFockEllipticFL. See BookProof/ChapterQgOuterFockEllipticFL.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterQgOuterFockEllipticFL.lean

import Theorems.Thm_BookProof_QuantumGravity3DGauge_qgKappaElliptic_nonneg

import Theorems.Thm_BookProof_QgOuterFock_sqSumOp_symmetricOn

import Theorems.Thm_BookProof_HermiteRelative_symmetricOn_of_polySym

import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym


import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym

import Theorems.Thm_BookProof_HermiteRelative_coreOp_add

import Theorems.Thm_BookProof_HermiteRelative_coreOp_comp

import Theorems.Thm_BookProof_HermiteRelative_coreOp_smul

import Theorems.Thm_BookProof_HermiteRelative_coreOp_sum

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum

import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X

import Definitions.Def_ChapterQgOuterFockFarisLavine
import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_esa_self
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_isPositiveSelfAdjointExtension
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteRelativeBound
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Mathlib


/-!
# The gravity Hamiltonian on the outer Fock space: Faris–Lavine with its own Friedrichs
extension

`BookProof.ChapterQgOuterFockFarisLavine` builds the Faris–Lavine apparatus on the outer
Fock space `𝔉 = ⊕ₙ L²(ℝ^{84n})`: a *comparison operator* is a positive symmetric operator
whose shift `N + 1` is onto (`Comparison`), the Friedrichs extension of any densely defined
positive symmetric operator is one (`friedrichsComparison`), and a family of fibre
comparison operators lifts to one on an `ℓ²`-direct sum (`dsComparison`).  That module then
lifts the one-particle oscillator `N₁ = −Δ + ‖x‖²/4` and leaves the sector data of the
gravity Hamiltonian as hypotheses.

This module removes the hypotheses in the case the Faris–Lavine strategy reaches
*unconditionally*: it takes the **gravity Hamiltonian itself** as the positive one-particle
operator.  The missing analytic ingredient is positivity of the sector Hamiltonian, which
is supplied here for every nonnegative signature.

## The positivity input

`BookProof.QgOuterFock.sqSumOp kappa v` is the operator `½ Σ_j κ_j π_j² + ½ Σ_r L_r²` on the
Gauss–polynomial core of `L²(ℝᴰ)`, for an arbitrary real signature `κ` and an arbitrary
finite family of real linear forms `L_r`.  Its quadratic form is
`½ Σ_j κ_j ‖π_j u‖² + ½ Σ_r ‖L_r u‖²`, because momentum and multiplication by a real
polynomial are Gauss-symmetric on the core; hence

`sqSumOp_quadForm_nonneg` : `0 ≤ κ` implies `0 ≤ ⟪ u, (sqSumOp κ v) u⟫`.

(The index set of the potential squares is an arbitrary finite type — the `n`-particle
gravity Hamiltonian needs `Fin n × Fin 64` — which is why this is proved here rather than
read off `BookProof.QuantumGravity3DGauge.signedOp_quadForm_nonneg`.)

## What is proved

* `quadForm_comp_self`, `quadForm_subtype_add`, `quadForm_subtype_real_smul`,
  `quadForm_subtype_sum`, `quadForm_sumSquares_nonneg` — the quadratic form of a sum of
  squares of symmetric operators with nonnegative weights is nonnegative.
* `momD`, `mulD`, `sqSumOp_eq_subtype_comp`, `sqSumOp_quadForm_nonneg` — the positivity
  input above.
* `dsFriedComparison`, `dsCore_le_dsFriedDom`,
  `dsFriedComparison_isPositiveSelfAdjointExtension`, `dsFriedComparison_esa` — **the
  general lift**: a family of densely defined positive symmetric operators, one per fibre,
  produces a Faris–Lavine comparison operator on the `ℓ²`-direct sum which is a positive
  self-adjoint extension of the direct sum of the fibre operators and is essentially
  self-adjoint on its domain.  This is the abstract form of “the Friedrichs extension of
  the positive one-particle operator lifts to the outer Fock space”.
* `kappaN`, `sectorHam`, `sectorHam_qgKappa`, `sectorHam_symmetricOn`,
  `sectorHam_quadForm_nonneg`, `sectorPosSym` — the `n`-particle gravity Hamiltonian
  `Σ_p h^{(p)}` of an arbitrary one-particle signature, and its positivity when the
  signature is nonnegative.
* `outerHam`, `outerHam_qgKappa`, `outerComparison`, `outer_esa_farisLavine`,
  `outer_isPositiveSelfAdjointExtension` — the outer Fock Hamiltonian of a nonnegative
  signature, its lifted Friedrichs comparison operator, and the two conclusions.
* `qgOuterEllipticHam`, `qgOuterEllipticComparison`, `qgOuterEllipticDom`,
  `qgOuterEllipticH`, **`qgOuterEllipticFock_esa_farisLavine`** — the physical instance:
  the elliptic-signature gravity Hamiltonian on the outer Fock space is essentially
  self-adjoint on the lifted Friedrichs domain, by Theorem 1 of Faris–Lavine with `c = 0`,
  and the lifted operator is a positive self-adjoint extension of `⊕ₙ Σ_p h^{(p)}` on the
  finite-particle core.

## Honest boundary

The signature must be **nonnegative**: this is the elliptic sector, `qgKappaElliptic`, not
the physical hyperbolic signature `qgKappa` (which is negative in the conformal direction,
`qgKappa_conformal_neg`), for which the sector Hamiltonian is not positive and has no
Friedrichs extension to lift.  For the physical signature the outer Fock space statement
that is proved is `BookProof.QgOuterFock.qgOuterFock_esa` — essential self-adjointness on
the *finite-particle core*, by the Carleman route sector by sector — and the Faris–Lavine
route stays conditional on the sector data of
`BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine`.  Nothing here claims a spectrum, a
mass gap or a continuum limit.

Everything in this module is `sorry`-free and `axiom`-free.
-/
namespace BookProof.QgOuterFockElliptic

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuantumGravity3DGauge
open BookProof.QgOuterFock
open BookProof.QgOuterFockFL
open BookProof.DirectSumEsa
open BookProof.FriedrichsExtension
open BookProof.YangMillsFriedrichs

noncomputable section

/-! ## 1. Positivity of a sum of squares with a nonnegative signature -/

section QuadForm

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- The quadratic form of `A²` for a symmetric `A` is `‖A x‖²`. -/
theorem quadForm_comp_self (A : D →ₗ[ℂ] D) (hA : SymmetricOn D (D.subtype.comp A)) (x : D) :
    quadForm (D.subtype.comp (A.comp A)) x = ‖((A x : D) : F)‖ ^ 2 := by
  have hkey : (inner ℂ ((A (A x) : D) : F) ((x : D) : F) : ℂ)
      = inner ℂ ((A x : D) : F) ((A x : D) : F) := hA (A x) x
  have hval : (D.subtype.comp (A.comp A)) x = ((A (A x) : D) : F) := rfl
  rw [quadForm, hval, ← inner_conj_symm (𝕜 := ℂ) ((x : D) : F) ((A (A x) : D) : F),
    Complex.conj_re, hkey]
  simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ((A x : D) : F)

theorem quadForm_subtype_add (S T : D →ₗ[ℂ] D) (x : D) :
    quadForm (D.subtype.comp (S + T)) x
      = quadForm (D.subtype.comp S) x + quadForm (D.subtype.comp T) x := by
  have hval : (D.subtype.comp (S + T)) x = (D.subtype.comp S) x + (D.subtype.comp T) x := rfl
  rw [quadForm, quadForm, quadForm, hval, inner_add_right, Complex.add_re]

theorem quadForm_subtype_real_smul (t : ℝ) (T : D →ₗ[ℂ] D) (x : D) :
    quadForm (D.subtype.comp (((t : ℝ) : ℂ) • T)) x = t * quadForm (D.subtype.comp T) x := by
  have hval : (D.subtype.comp (((t : ℝ) : ℂ) • T)) x = ((t : ℝ) : ℂ) • (D.subtype.comp T) x := rfl
  rw [quadForm, quadForm, hval, inner_smul_right]
  simp

theorem quadForm_subtype_sum {R : Type*} (s : Finset R) (T : R → D →ₗ[ℂ] D) (x : D) :
    quadForm (D.subtype.comp (∑ r ∈ s, T r)) x = ∑ r ∈ s, quadForm (D.subtype.comp (T r)) x := by
  classical
  induction s using Finset.induction with
  | empty => simp [quadForm]
  | insert r s hr ih =>
      rw [Finset.sum_insert hr, quadForm_subtype_add, ih, Finset.sum_insert hr]

/-- **A sum of squares with a nonnegative signature has a nonnegative quadratic form.**  The
index set of the potential squares is an arbitrary finite type (the gravity sector needs
`Fin n × Fin 64`), which is why this is not a direct instance of
`BookProof.QuantumGravity3DGauge.signedOp_quadForm_nonneg`. -/
theorem quadForm_sumSquares_nonneg {N : ℕ} {R : Type*} [Fintype R] (kappa : Fin N → ℝ)
    (hk : ∀ j, 0 ≤ kappa j) (pi : Fin N → D →ₗ[ℂ] D) (Bf : R → D →ₗ[ℂ] D)
    (hpi : ∀ j, SymmetricOn D (D.subtype.comp (pi j)))
    (hB : ∀ r, SymmetricOn D (D.subtype.comp (Bf r))) (x : D) :
    0 ≤ quadForm (D.subtype.comp (((1 / 2 : ℝ) : ℂ) •
      ((∑ j, ((kappa j : ℝ) : ℂ) • (pi j).comp (pi j)) + ∑ r, (Bf r).comp (Bf r)))) x := by
  rw [quadForm_subtype_real_smul, quadForm_subtype_add, quadForm_subtype_sum,
    quadForm_subtype_sum]
  have h1 : 0 ≤ ∑ j, quadForm (D.subtype.comp (((kappa j : ℝ) : ℂ) • (pi j).comp (pi j))) x := by
    refine Finset.sum_nonneg fun j _ => ?_
    rw [quadForm_subtype_real_smul, quadForm_comp_self (pi j) (hpi j)]
    exact mul_nonneg (hk j) (by positivity)
  have h2 : 0 ≤ ∑ r, quadForm (D.subtype.comp ((Bf r).comp (Bf r))) x := by
    refine Finset.sum_nonneg fun r _ => ?_
    rw [quadForm_comp_self (Bf r) (hB r)]
    positivity
  linarith

end QuadForm

/-! ## 2. The `d`-dimensional sum-of-squares operator with a nonnegative signature -/

variable {D : ℕ}

theorem realCoeff_linForm (v : Fin D → ℝ) : RealCoeff (linForm v) := by
  rw [linForm]
  exact RealCoeff.sum fun i _ => RealCoeff.smul (realCoeff_X i)

/-- The momentum operator `π_j`, as an operator of the Gauss–polynomial core into itself. -/
def momD (j : Fin D) : polyGaussCore (d := D) →ₗ[ℂ] polyGaussCore (d := D) :=
  coreOp (YangMillsHermite.momOp j)

/-- Multiplication by a polynomial, as an operator of the core into itself. -/
def mulD (f : MvPolynomial (Fin D) ℂ) :
    polyGaussCore (d := D) →ₗ[ℂ] polyGaussCore (d := D) :=
  coreOp (YangMillsHermite.mulOp f)

theorem momD_eq (j : Fin D) : coreOp (YangMillsHermite.momOp (d := D) j) = momD j := rfl

theorem mulD_eq (f : MvPolynomial (Fin D) ℂ) : coreOp (YangMillsHermite.mulOp f) = mulD f := rfl

theorem momD_symmetricOn (j : Fin D) :
    SymmetricOn (polyGaussCore (d := D)) ((polyGaussCore (d := D)).subtype.comp (momD j)) :=
  symmetricOn_of_polySym (YangMillsHermite.momOp_polySym j)

theorem mulD_symmetricOn {f : MvPolynomial (Fin D) ℂ} (hf : RealCoeff f) :
    SymmetricOn (polyGaussCore (d := D)) ((polyGaussCore (d := D)).subtype.comp (mulD f)) :=
  symmetricOn_of_polySym (YangMillsHermite.mulOp_polySym hf)

set_option maxHeartbeats 1200000 in
-- the composite core operators make the unification in the statement expensive
/-- The sum-of-squares operator, rewritten with the momentum and multiplication operators
of the core. -/
theorem sqSumOp_eq_subtype_comp {R : Type*} [Fintype R] (kappa : Fin D → ℝ)
    (v : R → Fin D → ℝ) :
    sqSumOp kappa v
      = (polyGaussCore (d := D)).subtype.comp (((1 / 2 : ℝ) : ℂ) •
        ((∑ j, ((kappa j : ℝ) : ℂ) • (momD j).comp (momD j))
          + ∑ r : R, (mulD (linForm (v r))).comp (mulD (linForm (v r))))) := by
  rw [sqSumOp, sqSumPoly, coreOp_smul, coreOp_add, coreOp_sum, coreOp_sum]
  simp only [coreOp_smul, coreOp_comp, momD_eq, mulD_eq]

/-- **The sum of squares `½ Σ_j κ_j π_j² + ½ Σ_r L_r²` is a positive operator whenever the
signature `κ` is nonnegative.** -/
theorem sqSumOp_quadForm_nonneg {R : Type*} [Fintype R] (kappa : Fin D → ℝ)
    (hk : ∀ j, 0 ≤ kappa j) (v : R → Fin D → ℝ) (x : polyGaussCore (d := D)) :
    0 ≤ quadForm (sqSumOp kappa v) x := by
  rw [sqSumOp_eq_subtype_comp]
  exact quadForm_sumSquares_nonneg kappa hk _ _ momD_symmetricOn
    (fun r => mulD_symmetricOn (realCoeff_linForm (v r))) x

/-! ## 3. The Friedrichs lift of a family of positive symmetric operators -/

section GenericLift

variable {I : Type*} {G : I → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] [∀ i, CompleteSpace (G i)]

/-- **The lifted Friedrichs comparison operator.**  Every fibre carries a densely defined
positive symmetric operator; the Friedrichs extension of the fibre operator is a
Faris–Lavine comparison operator on the fibre, and `dsComparison` glues the fibres into a
comparison operator on the `ℓ²`-direct sum. -/
def dsFriedComparison (S : ∀ i, PosSymOp (G i)) (hd : ∀ i, Dense ((S i).dom : Set (G i))) :
    Comparison (lp G 2) :=
  dsComparison fun i => friedrichsComparison (S i) (hd i)

/-- The algebraic direct sum of the fibre domains sits inside the domain of the lifted
Friedrichs operator. -/
theorem dsCore_le_dsFriedDom (S : ∀ i, PosSymOp (G i))
    (hd : ∀ i, Dense ((S i).dom : Set (G i))) :
    dsCore (fun i => (S i).dom) ≤ (dsFriedComparison S hd).dom := by
  intro x hx
  refine ⟨fun i =>
    (friedrichsComparison_extends (S i) (hd i) ⟨(x : lp G 2) i, hx.2 i⟩).choose, ?_⟩
  have hfun : (fun i => opTot (friedrichsComparison (S i) (hd i)).op ((x : lp G 2) i))
      = fun i => ((S i).op ⟨(x : lp G 2) i, hx.2 i⟩ : G i) := by
    funext i
    rw [opTot_of_mem _
      (friedrichsComparison_extends (S i) (hd i) ⟨(x : lp G 2) i, hx.2 i⟩).choose]
    exact (friedrichsComparison_extends (S i) (hd i) ⟨(x : lp G 2) i, hx.2 i⟩).choose_spec
  rw [hfun]
  refine memLp_of_finite_support (Set.Finite.subset hx.1 fun i hi => ?_)
  simp only [Set.mem_setOf_eq] at hi ⊢
  intro h0
  refine hi ?_
  have hz : (⟨(x : lp G 2) i, hx.2 i⟩ : (S i).dom) = 0 := Subtype.ext h0
  rw [hz, map_zero]

/-- **The lifted Friedrichs operator is a positive self-adjoint extension of the direct sum
of the fibre operators.** -/
theorem dsFriedComparison_isPositiveSelfAdjointExtension (S : ∀ i, PosSymOp (G i))
    (hd : ∀ i, Dense ((S i).dom : Set (G i))) :
    IsPositiveSelfAdjointExtension (dsOp fun i => (S i).op) (dsFriedComparison S hd).op :=
  (dsFriedComparison S hd).isPositiveSelfAdjointExtension (dsOp fun i => (S i).op) fun x => by
    refine ⟨dsCore_le_dsFriedDom S hd x.2, ?_⟩
    refine lp.ext (funext fun i => ?_)
    refine Eq.trans (dsCompOp_fib (fun i => friedrichsComparison (S i) (hd i))
      ⟨(x : lp G 2), dsCore_le_dsFriedDom S hd x.2⟩ i) ?_
    exact (friedrichsComparison_extends (S i) (hd i) ⟨(x : lp G 2) i, x.2.2 i⟩).choose_spec

/-- **The lifted Friedrichs operator is essentially self-adjoint on its domain** — the
`H = N`, `c = 0` case of the Faris–Lavine criterion. -/
theorem dsFriedComparison_esa (S : ∀ i, PosSymOp (G i))
    (hd : ∀ i, Dense ((S i).dom : Set (G i))) :
    EssentiallySelfAdjointOn (dsFriedComparison S hd).dom (dsFriedComparison S hd).op :=
  (dsFriedComparison S hd).esa_self

end GenericLift

/-! ## 4. The gravity Hamiltonian of a nonnegative signature on the outer Fock space -/

/-- The `n`-particle signature obtained by repeating a one-particle signature in every
particle's block of `84` field-space coordinates. -/
def kappaN (kappa : Fin 84 → ℝ) (n : ℕ) (J : Fin (n * 84)) : ℝ := kappa (modeOf J)

/-- The `n`-particle gravity Hamiltonian `Σ_p h^{(p)}` of a one-particle signature. -/
def sectorHam (kappa : Fin 84 → ℝ) (n : ℕ) :
    (polyGaussCore (d := n * 84)) →ₗ[ℂ] L2d (n * 84) :=
  sqSumOp (kappaN kappa n) (qgTorsionVecN n)

theorem kappaN_qgKappa (n : ℕ) : kappaN qgKappa n = qgKappaN n := rfl

/-- The physical signature gives back the sector Hamiltonian of
`BookProof.ChapterQgOuterFockEsa`. -/
theorem sectorHam_qgKappa (n : ℕ) : sectorHam qgKappa n = qgSectorHam n := by
  rw [sectorHam, kappaN_qgKappa, qgSectorHam]

theorem sectorHam_symmetricOn (kappa : Fin 84 → ℝ) (n : ℕ) :
    SymmetricOn (polyGaussCore (d := n * 84)) (sectorHam kappa n) :=
  sqSumOp_symmetricOn _ _

theorem sectorHam_quadForm_nonneg {kappa : Fin 84 → ℝ} (hk : ∀ j, 0 ≤ kappa j) (n : ℕ)
    (x : polyGaussCore (d := n * 84)) : 0 ≤ quadForm (sectorHam kappa n) x :=
  sqSumOp_quadForm_nonneg _ (fun J => hk (modeOf J)) _ x

/-- The `n`-particle Hamiltonian of a **nonnegative** signature, as a densely defined
positive symmetric operator on the sector `L²(ℝ^{84n})`. -/
def sectorPosSym {kappa : Fin 84 → ℝ} (hk : ∀ j, 0 ≤ kappa j) (n : ℕ) :
    PosSymOp (L2d (n * 84)) where
  dom := polyGaussCore (d := n * 84)
  op := sectorHam kappa n
  sym := sectorHam_symmetricOn kappa n
  pos := sectorHam_quadForm_nonneg hk n

/-- The full gravity Hamiltonian of a signature on the finite-particle core of the outer
Fock space. -/
def outerHam (kappa : Fin 84 → ℝ) : qgOuterCore →ₗ[ℂ] QgOuterFock.qgOuterFock :=
  dsOp fun n : ℕ => sectorHam kappa n

set_option maxHeartbeats 1200000 in
-- identifying two direct sums of core operators is a costly defeq check
theorem outerHam_qgKappa : outerHam qgKappa = qgOuterHam :=
  congrArg dsOp (funext fun n => sectorHam_qgKappa n)

/-- **The lifted Friedrichs comparison operator of the gravity Hamiltonian itself**, for a
nonnegative signature: the Friedrichs extension of the positive `n`-particle operator,
lifted to the outer Fock space. -/
def outerComparison {kappa : Fin 84 → ℝ} (hk : ∀ j, 0 ≤ kappa j) : Comparison QgOuterFock.qgOuterFock :=
  dsFriedComparison (fun n : ℕ => sectorPosSym hk n) fun _ => polyGaussCore_dense

/-- **Essential self-adjointness on the outer Fock space, by Faris–Lavine.** -/
theorem outer_esa_farisLavine {kappa : Fin 84 → ℝ} (hk : ∀ j, 0 ≤ kappa j) :
    EssentiallySelfAdjointOn (outerComparison hk).dom (outerComparison hk).op :=
  dsFriedComparison_esa _ _

set_option maxHeartbeats 1200000 in
-- the Friedrichs domains are ranges of completion-built resolvents: defeq checks are costly
/-- **The lifted operator is a positive self-adjoint extension of the outer Fock
Hamiltonian on the finite-particle core.** -/
theorem outer_isPositiveSelfAdjointExtension {kappa : Fin 84 → ℝ} (hk : ∀ j, 0 ≤ kappa j) :
    IsPositiveSelfAdjointExtension (outerHam kappa) (outerComparison hk).op :=
  dsFriedComparison_isPositiveSelfAdjointExtension (fun n : ℕ => sectorPosSym hk n)
    fun _ => polyGaussCore_dense

/-! ## 5. The elliptic gravity Hamiltonian -/

/-- The elliptic-signature gravity Hamiltonian on the finite-particle core of the outer
Fock space. -/
def qgOuterEllipticHam : qgOuterCore →ₗ[ℂ] QgOuterFock.qgOuterFock := outerHam qgKappaElliptic

/-- The lifted Friedrichs comparison operator of the elliptic gravity Hamiltonian. -/
def qgOuterEllipticComparison : Comparison QgOuterFock.qgOuterFock :=
  outerComparison qgKappaElliptic_nonneg

/-- The domain of the lifted operator. -/
abbrev qgOuterEllipticDom : Submodule ℂ QgOuterFock.qgOuterFock := qgOuterEllipticComparison.dom

/-- The lifted elliptic gravity Hamiltonian on the outer Fock space. -/
abbrev qgOuterEllipticH : qgOuterEllipticDom →ₗ[ℂ] QgOuterFock.qgOuterFock := qgOuterEllipticComparison.op

set_option maxHeartbeats 1200000 in
-- the Friedrichs domains are ranges of completion-built resolvents: defeq checks are costly
/-- **The elliptic gravity Hamiltonian on the outer Fock space is essentially self-adjoint,
by the Faris–Lavine strategy.**

The `n`-particle Hamiltonian `Σ_p h^{(p)}` is positive for the elliptic signature
(`sectorHam_quadForm_nonneg`), so it has a Friedrichs extension, which is a Faris–Lavine
comparison operator on the sector; the lift of that family to the `ℓ²`-direct sum
`𝔉 = ⊕ₙ L²(ℝ^{84n})` is again one (`dsFriedComparison`), and Theorem 1 of Faris–Lavine
applies on `𝔉` with `c = 0`.  The resulting operator extends the outer Fock Hamiltonian on
the finite-particle core, and is positive and self-adjoint there. -/
theorem qgOuterEllipticFock_esa_farisLavine :
    EssentiallySelfAdjointOn qgOuterEllipticDom qgOuterEllipticH ∧
      IsPositiveSelfAdjointExtension qgOuterEllipticHam qgOuterEllipticH :=
  ⟨outer_esa_farisLavine _, outer_isPositiveSelfAdjointExtension _⟩

end

end BookProof.QgOuterFockElliptic


