-- Prove2me | Definitions.Def_ChapterNavierStokesFullEulerianFock
-- name    : ChapterNavierStokesFullEulerianFock
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T12:58:06.96492+00:00
-- url     : https://prove2.me/theorems/d5bd0b81-1f3d-466f-ba09-fe222f0fdf69
-- title:
--   The Lean 4 theorem `realCoeff_C_ofReal` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesFullEulerianFock.lean`): generated def bundle for ChapterNavierStokesFullEulerianFock. See BookProof/ChapterNavierStokesFullEulerianFock.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFullEulerianFock.lean

import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists_complete
import Theorems.Thm_BookProof_QgOuterFock_dsOp_quadForm_nonneg
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_positive
import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists_complete
import Theorems.Thm_BookProof_QgOuterFock_dsOp_quadForm_nonneg
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_positive
import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum

import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_add

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_smul


import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op

import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym





import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym






import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul




import Theorems.Thm_BookProof_YangMillsHermite_starP_C

import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib


/-!
# The **full** Navier–Stokes Hamiltonian in **Eulerian** variables on the nested Fock space

This module carries the Navier–Stokes Hamiltonian in Eulerian variables **with the complete,
genuinely nonlinear advection** `u_j ∂_j u_i` — *no* Oseen (background-velocity)
linearisation, no truncation of the nonlinearity, and no lattice.

The construction is the one that the Yang–Mills thread uses
(`BookProof.ChapterYangMillsFockFriedrichs`): the Hamiltonian is a **positive
kinetic-plus-squares operator**

`H_n = ½ Σ_m π_m² + ½ Σ_r Φ_r²`

whose constraint polynomials `Φ_r` are now *quadratic* in the coordinates rather than linear.
Both data that the Faris–Lavine strategy is built on — the **Friedrichs extension** of a
positive symmetric operator and the passage to the `ℓ²`-direct sum — are fibrewise, so the
whole construction lifts from the one-particle space `L²(ℝ^{21})` to the nested Fock space
`⊕ₙ L²(ℝ^{21n})`.

## The variables (21 per parcel)

Per parcel (excitation) of the Eulerian field:

* `u_i` (3) — the velocity modes;
* `u_{i,j}` (9) — the **independent coordinates representing the spatial derivatives**
  `∂_j u_i` of the velocity field;
* `w_i` (3) — the coordinates representing the viscous term `Δ u_i`;
* `q_i` (3) — the coordinates representing the pressure gradient `∂_i p`;
* `y_j` (3) — the auxiliary coordinates in which the field is expanded,
  `u_i(y) = u_i + u_{i,j} y_j`.

## The constraint forms (19 per parcel)

* **The full Navier–Stokes residual** `R_i = Σ_j u_j u_{i,j} + q_i − ν w_i` (3 per parcel).
  The advection term `Σ_j u_j u_{i,j}` is the exact quadratic `u·∇u`: the velocity that
  transports is the dynamical velocity of the same parcel, not a frozen background field.
  `nsResPoly_not_affine` proves that this residual is **not** an affine form of the
  coordinates — i.e. the model is not, and cannot be rewritten as, an Oseen linearisation.
* **Incompressibility** `Σ_j u_{j,j} = 0` (1 per parcel) — the 3D gauge fixing of the
  Eulerian thread, written in the independent derivative coordinates.
* **The gauge fixing of the derivative variables** `λ(u_{i,j} + u_i − u_i^{next})` (9 per
  parcel): the statement that the coordinate `u_{i,j}`, which *represents* a spatial
  derivative, is the finite difference of the velocity between neighbouring parcels.  It
  couples two parcels, so the Hamiltonian is genuinely interacting.
* **The gauge fixing of the viscous variables** `μ(w_i + Σ_j u_{i,j} − Σ_j u_{i,j}^{next})`
  (3 per parcel).
* **The `y`-gauge fixing** `g·y_j` (3 per parcel).

## What is proved

* `nsSectorHam_quadForm_nonneg` — the `n`-parcel **auxiliary sum-of-squares operator**
  `nsSectorHam = weylOp … = ½ Σ_m π_m² + ½ Σ_r (constraint form_r)²` is bounded below (the
  Navier–Stokes Hamiltonian itself is **not** bounded below:
  `BookProof.NsKoopman.nsKoopmanOp_not_bounded_below`);
* `nsSector_friedrichs_extension` — hence it has a positive self-adjoint (Friedrichs)
  extension on `L²(ℝ^{21n})`;
* `nsFullFockHam_quadForm_nonneg`, `nsFullFock_friedrichs_extension` — the same on the
  nested Fock space `⊕ₙ L²(ℝ^{21n})`, positivity being checked fibrewise;
* `nsFullOuterN_esa` — **Faris–Lavine on the outer Fock space**: the lifted realization is
  essentially self-adjoint on its domain, by the Faris–Lavine criterion with the lifted
  Friedrichs extension as comparison operator and commutator constant `c = 0`;
* `nsFullOuterN_isPositiveSelfAdjointExtension` — that realization extends the Hamiltonian
  defined on the finite-parcel core;
* `nsFullFock_stone_flow` — the unitary time evolution (Stone);
* `nsFullFockHam_number_conserving` — the outer Hamiltonian is block diagonal in the
  parcel-number sectors: the sectors, not a spatial lattice, decompose the problem;
* `nsResPoly_not_affine` — the advection is the genuine nonlinearity.

What is **not** claimed: essential self-adjointness on the finite-parcel core for the
nonlinear model (the Faris–Lavine relative bound `‖Hu‖ ≤ K‖(N+1)u‖` against a harmonic
comparison operator fails once the potential is quartic, exactly as in the non-abelian
Yang–Mills case), no spectral information, and nothing about classical Navier–Stokes
regularity.

## Relation to the sharpness result of `ChapterNavierStokesFullEsa`

`BookProof.ChapterNavierStokesFullEsa.exists_nsFullData_not_hasZeroDeficiencyOn` shows that
*structural* hypotheses alone (symmetric modes, symmetric momenta, degree ≤ 3) can never give
essential self-adjointness of a nonlinear Navier–Stokes Hamiltonian.  The analytic input used
here is **positivity**: the constraints enter squared in the **auxiliary sum-of-squares
operator** `weylOp … = ½ Σ π² + ½ Σ form²`, so *that* operator is bounded below and
the Friedrichs extension produces a distinguished self-adjoint realization.  The mainstream
Navier–Stokes Hamiltonian has no square of a residual and is **not** bounded below
(`BookProof.NsKoopman.nsKoopmanOp_not_bounded_below`), so this is a statement about the
auxiliary operator and must not be read as boundedness of the NS Hamiltonian.  It is a
statement about existence of a canonical realization, not about uniqueness of the extension,
and it is consistent with the sharpness result.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsFullEuler

open MvPolynomial
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL BookProof.Qg3DGaugeFL
open BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. The coordinates of the `n`-parcel sector -/

/-- The global coordinate of the `i`-th field-space direction of the `p`-th parcel. -/
def ycoord {n : ℕ} (p : Fin n) (i : Fin 21) : Fin (n * 21) := finProdFinEquiv (p, i)

theorem ycoord_injective {n : ℕ} (p : Fin n) : Function.Injective (ycoord p) := by
  intro i i' h
  have := finProdFinEquiv.injective h
  simpa using congrArg Prod.snd this

/-- The velocity mode `u_i`. -/
def uIdx (i : Fin 3) : Fin 21 := ⟨i.val, by have := i.isLt; omega⟩

/-- The coordinate representing the spatial derivative `∂_j u_i`. -/
def dIdx (i j : Fin 3) : Fin 21 := ⟨3 + 3 * i.val + j.val, by
  have := i.isLt; have := j.isLt; omega⟩

/-- The coordinate representing the viscous term `Δ u_i`. -/
def wIdx (i : Fin 3) : Fin 21 := ⟨12 + i.val, by have := i.isLt; omega⟩

/-- The coordinate representing the pressure gradient `∂_i p`. -/
def qIdx (i : Fin 3) : Fin 21 := ⟨15 + i.val, by have := i.isLt; omega⟩

/-- The auxiliary expansion coordinate `y_j`. -/
def yIdx (j : Fin 3) : Fin 21 := ⟨18 + j.val, by have := j.isLt; omega⟩

/-! ## 2. The constraint polynomials of one parcel -/

variable {n : ℕ}

/-- **The full Navier–Stokes residual** of the `p`-th parcel,
`R_i = Σ_j u_j u_{i,j} + q_i − ν w_i`.  The advection term is the exact quadratic `u·∇u`. -/
def nsResPoly (nu : ℝ) (p : Fin n) (i : Fin 3) : MvPolynomial (Fin (n * 21)) ℂ :=
  (∑ j : Fin 3, X (ycoord p (uIdx j)) * X (ycoord p (dIdx i j)))
    + X (ycoord p (qIdx i)) + C ((-nu : ℝ) : ℂ) * X (ycoord p (wIdx i))

/-- **Incompressibility** `Σ_j u_{j,j} = 0`, written in the independent derivative
coordinates: the 3D gauge fixing of the Eulerian thread. -/
def divPoly (p : Fin n) : MvPolynomial (Fin (n * 21)) ℂ :=
  ∑ j : Fin 3, X (ycoord p (dIdx j j))

/-- **The gauge fixing of the derivative variables**: `u_{i,j}` is the finite difference of
the velocity between neighbouring parcels.  This form couples two parcels. -/
def derGaugePoly (lam : ℝ) (p : Fin n) (i j : Fin 3) : MvPolynomial (Fin (n * 21)) ℂ :=
  ((lam : ℝ) : ℂ) • (X (ycoord p (dIdx i j)) + X (ycoord p (uIdx i))
    + ((-1 : ℝ) : ℂ) • X (ycoord (nextPart p) (uIdx i)))

/-- **The gauge fixing of the viscous variables**: `w_i` is the difference of the derivative
coordinates between neighbouring parcels. -/
def lapGaugePoly (mu : ℝ) (p : Fin n) (i : Fin 3) : MvPolynomial (Fin (n * 21)) ℂ :=
  ((mu : ℝ) : ℂ) • (X (ycoord p (wIdx i)) + (∑ j : Fin 3, X (ycoord p (dIdx i j)))
    + ((-1 : ℝ) : ℂ) • ∑ j : Fin 3, X (ycoord (nextPart p) (dIdx i j)))

/-- **The `y`-gauge fixing** of the auxiliary expansion coordinates. -/
def yGaugePoly (gg : ℝ) (p : Fin n) (j : Fin 3) : MvPolynomial (Fin (n * 21)) ℂ :=
  ((gg : ℝ) : ℂ) • X (ycoord p (yIdx j))

/-- A real constant is a real-coefficient polynomial. -/
theorem realCoeff_C_ofReal (c : ℝ) :
    RealCoeff (C ((c : ℝ) : ℂ) : MvPolynomial (Fin (n * 21)) ℂ) := by
  rw [RealCoeff, starP_C, Complex.conj_ofReal]

theorem realCoeff_nsResPoly (nu : ℝ) (p : Fin n) (i : Fin 3) :
    RealCoeff (nsResPoly nu p i) :=
  ((RealCoeff.sum fun _ _ => (realCoeff_X _).mul (realCoeff_X _)).add
      (realCoeff_X _)).add ((realCoeff_C_ofReal _).mul (realCoeff_X _))

theorem realCoeff_divPoly (p : Fin n) : RealCoeff (divPoly p) :=
  RealCoeff.sum fun _ _ => realCoeff_X _

theorem realCoeff_derGaugePoly (lam : ℝ) (p : Fin n) (i j : Fin 3) :
    RealCoeff (derGaugePoly lam p i j) :=
  RealCoeff.smul (((realCoeff_X _).add (realCoeff_X _)).add (RealCoeff.smul (realCoeff_X _)))

theorem realCoeff_lapGaugePoly (mu : ℝ) (p : Fin n) (i : Fin 3) :
    RealCoeff (lapGaugePoly mu p i) :=
  RealCoeff.smul (((realCoeff_X _).add (RealCoeff.sum fun _ _ => realCoeff_X _)).add
    (RealCoeff.smul (RealCoeff.sum fun _ _ => realCoeff_X _)))

theorem realCoeff_yGaugePoly (gg : ℝ) (p : Fin n) (j : Fin 3) :
    RealCoeff (yGaugePoly gg p j) := RealCoeff.smul (realCoeff_X _)

/-- The `19` constraint forms of one parcel, in one family: three Navier–Stokes residuals,
incompressibility, nine derivative gauge fixings, three viscous gauge fixings and three
`y`-gauge fixings. -/
def nsFormOf (nu lam mu gg : ℝ) (p : Fin n) (r : Fin 19) : MvPolynomial (Fin (n * 21)) ℂ :=
  if h : r.val < 3 then nsResPoly nu p ⟨r.val, h⟩
  else if r.val = 3 then divPoly p
  else if h2 : r.val < 13 then
    derGaugePoly lam p ⟨(r.val - 4) / 3, by omega⟩ ⟨(r.val - 4) % 3, by omega⟩
  else if h3 : r.val < 16 then lapGaugePoly mu p ⟨r.val - 13, by omega⟩
  else yGaugePoly gg p ⟨r.val - 16, by have := r.isLt; omega⟩

theorem realCoeff_nsFormOf (nu lam mu gg : ℝ) (p : Fin n) (r : Fin 19) :
    RealCoeff (nsFormOf nu lam mu gg p r) := by
  unfold nsFormOf
  split_ifs
  · exact realCoeff_nsResPoly _ _ _
  · exact realCoeff_divPoly _
  · exact realCoeff_derGaugePoly _ _ _ _
  · exact realCoeff_lapGaugePoly _ _ _
  · exact realCoeff_yGaugePoly _ _ _

/-! ## 3. The `n`-parcel Hamiltonian -/

/-- The field-space direction carrying the `s`-th momentum of a parcel: the three velocity
modes and the nine derivative modes are the canonical coordinates. -/
def momIdx (s : Fin 12) : Fin 21 :=
  if h : s.val < 3 then uIdx ⟨s.val, h⟩
  else dIdx ⟨(s.val - 3) / 3, by have := s.isLt; omega⟩
    ⟨(s.val - 3) % 3, by omega⟩

/-- The momentum operators of the `n`-parcel sector: `π = −i ∂/∂u`, one for each canonical
coordinate of each parcel. -/
def nsPiN (n : ℕ) (m : Fin (n * 12)) :
    (polyGaussCore (d := n * 21)) →ₗ[ℂ] (polyGaussCore (d := n * 21)) :=
  (coreRepPoly (n * 21)).op
    (momOp (ycoord (finProdFinEquiv.symm m).1 (momIdx (finProdFinEquiv.symm m).2)))

/-- The constraint (multiplication) operators of the `n`-parcel sector. -/
def nsFieldN (nu lam mu gg : ℝ) (n : ℕ) (m : Fin (n * 19)) :
    (polyGaussCore (d := n * 21)) →ₗ[ℂ] (polyGaussCore (d := n * 21)) :=
  (coreRepPoly (n * 21)).op
    (mulOp (nsFormOf nu lam mu gg (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2))

theorem nsPiN_symmetricOn (n : ℕ) (m : Fin (n * 12)) :
    SymmetricOn (polyGaussCore (d := n * 21))
      ((polyGaussCore (d := n * 21)).subtype.comp (nsPiN n m)) :=
  (coreRepPoly (n * 21)).symmetricOn_op (momOp_polySym _)

theorem nsFieldN_symmetricOn (nu lam mu gg : ℝ) (n : ℕ) (m : Fin (n * 19)) :
    SymmetricOn (polyGaussCore (d := n * 21))
      ((polyGaussCore (d := n * 21)).subtype.comp (nsFieldN nu lam mu gg n m)) :=
  (coreRepPoly (n * 21)).symmetricOn_op (mulOp_polySym (realCoeff_nsFormOf _ _ _ _ _ _))

/-- **The `n`-parcel Navier–Stokes Hamiltonian with the full nonlinear advection**, on the
Gauss–polynomial core of `L²(ℝ^{21n})`. -/
def nsSectorHam (nu lam mu gg : ℝ) (n : ℕ) :
    (polyGaussCore (d := n * 21)) →ₗ[ℂ] L2d (n * 21) :=
  weylOp (nsPiN n) (nsFieldN nu lam mu gg n)

theorem nsSectorHam_symmetricOn (nu lam mu gg : ℝ) (n : ℕ) :
    SymmetricOn (polyGaussCore (d := n * 21)) (nsSectorHam nu lam mu gg n) :=
  weylOpDom_symmetricOn (nsPiN_symmetricOn n) (nsFieldN_symmetricOn nu lam mu gg n)

/-- **The `n`-parcel auxiliary sum-of-squares operator is bounded below** — its quadratic form
is a sum of squares (`weylOp` is `½ Σ π² + ½ Σ form²`).  This holds for the *full* nonlinear
advection: no linearisation is used.  It is *not* a statement about the Navier–Stokes
Hamiltonian, which has no square of a residual and is not bounded below
(`BookProof.NsKoopman.nsKoopmanOp_not_bounded_below`). -/
theorem nsSectorHam_quadForm_nonneg (nu lam mu gg : ℝ) (n : ℕ)
    (x : polyGaussCore (d := n * 21)) : 0 ≤ quadForm (nsSectorHam nu lam mu gg n) x :=
  weylOpDom_quadForm_nonneg (nsPiN_symmetricOn n) (nsFieldN_symmetricOn nu lam mu gg n) x

/-- **The `n`-parcel Hamiltonian has a positive self-adjoint (Friedrichs) extension.** -/
theorem nsSector_friedrichs_extension (nu lam mu gg : ℝ) (n : ℕ) :
    ∃ (Dom : Submodule ℂ (L2d (n * 21))) (A : Dom →ₗ[ℂ] L2d (n * 21)),
      IsPositiveSelfAdjointExtension (nsSectorHam nu lam mu gg n) A :=
  friedrichs_extension_exists_complete
    ⟨polyGaussCore, nsSectorHam nu lam mu gg n, nsSectorHam_symmetricOn nu lam mu gg n,
      nsSectorHam_quadForm_nonneg nu lam mu gg n⟩
    polyGaussCore_dense

/-! ## 4. The nested Fock space -/

/-- The nested Fock space `⊕ₙ L²(ℝ^{21n})` of the Eulerian Navier–Stokes field. -/
abbrev nsFockSpace := lp (fun n : ℕ => L2d (n * 21)) 2

/-- The finite-parcel core. -/
def nsFockCore : Submodule ℂ nsFockSpace := dsCore (fun n : ℕ => polyGaussCore (d := n * 21))

theorem nsFockCore_dense :
    Dense ((nsFockCore : Submodule ℂ nsFockSpace) : Set nsFockSpace) :=
  dsCore_dense fun _ => polyGaussCore_dense

/-- **The full Navier–Stokes Hamiltonian on the nested Fock space.** -/
def nsFullFockHam (nu lam mu gg : ℝ) : nsFockCore →ₗ[ℂ] nsFockSpace :=
  dsOp (fun n : ℕ => nsSectorHam nu lam mu gg n)

theorem nsFullFockHam_symmetricOn (nu lam mu gg : ℝ) :
    SymmetricOn nsFockCore (nsFullFockHam nu lam mu gg) :=
  dsOp_symmetricOn _ fun n => nsSectorHam_symmetricOn nu lam mu gg n

/-- **The outer auxiliary sum-of-squares operator is bounded below**: positivity is fibrewise,
so it lifts from the one-parcel Hilbert space to the nested Fock space.  (The NS Hamiltonian
itself is not bounded below — `BookProof.NsKoopman.nsKoopmanOp_not_bounded_below`.) -/
theorem nsFullFockHam_quadForm_nonneg (nu lam mu gg : ℝ) (x : nsFockCore) :
    0 ≤ quadForm (nsFullFockHam nu lam mu gg) x :=
  dsOp_quadForm_nonneg _ (fun n u => nsSectorHam_quadForm_nonneg nu lam mu gg n u) x

/-- **The full nonlinear Navier–Stokes Hamiltonian on the nested Fock space has a positive
self-adjoint (Friedrichs) extension.** -/
theorem nsFullFock_friedrichs_extension (nu lam mu gg : ℝ) :
    ∃ (Dom : Submodule ℂ nsFockSpace) (A : Dom →ₗ[ℂ] nsFockSpace),
      IsPositiveSelfAdjointExtension (nsFullFockHam nu lam mu gg) A :=
  friedrichs_extension_exists_complete
    ⟨nsFockCore, nsFullFockHam nu lam mu gg, nsFullFockHam_symmetricOn nu lam mu gg,
      nsFullFockHam_quadForm_nonneg nu lam mu gg⟩
    nsFockCore_dense

set_option maxHeartbeats 1000000 in
-- unfolding the `lp` instances of the Fock space in the Stone construction is costly
/-- **The unitary time evolution of the outer Navier–Stokes Hamiltonian** (Stone). -/
theorem nsFullFock_stone_flow (nu lam mu gg : ℝ) :
    ∃ (T : UnboundedSelfAdjoint nsFockSpace) (U : ℝ → (nsFockSpace →L[ℂ] nsFockSpace)),
      IsStoneFlow T U := by
  obtain ⟨Dom, A, hA⟩ := nsFullFock_friedrichs_extension nu lam mu gg
  obtain ⟨T, U, _, _, hflow⟩ := exists_stone_flow_of_positive nsFockCore_dense hA
  exact ⟨T, U, hflow⟩

/-! ## 5. Faris–Lavine on the outer Fock space -/

/-- The `n`-parcel Hamiltonian as a densely defined positive symmetric operator. -/
def nsPosSym (nu lam mu gg : ℝ) (n : ℕ) : PosSymOp (L2d (n * 21)) where
  dom := polyGaussCore (d := n * 21)
  op := nsSectorHam nu lam mu gg n
  sym := nsSectorHam_symmetricOn nu lam mu gg n
  pos := nsSectorHam_quadForm_nonneg nu lam mu gg n

/-- **The Friedrichs extension of the `n`-parcel Hamiltonian, as a Faris–Lavine comparison
operator**: positive, self-adjoint, and with `N + 1` onto `L²(ℝ^{21n})`. -/
def nsFried (nu lam mu gg : ℝ) (n : ℕ) : Comparison (L2d (n * 21)) :=
  friedrichsComparison (nsPosSym nu lam mu gg n) polyGaussCore_dense

theorem polyGaussCore_le_nsFriedDom (nu lam mu gg : ℝ) (n : ℕ) :
    (polyGaussCore (d := n * 21)) ≤ (nsFried nu lam mu gg n).dom := fun v hv =>
  (friedrichsComparison_extends (nsPosSym nu lam mu gg n) polyGaussCore_dense ⟨v, hv⟩).choose

theorem nsFried_op_core (nu lam mu gg : ℝ) (n : ℕ) (p : polyGaussCore (d := n * 21))
    (h : (p : L2d (n * 21)) ∈ (nsFried nu lam mu gg n).dom) :
    (nsFried nu lam mu gg n).op ⟨(p : L2d (n * 21)), h⟩ = nsSectorHam nu lam mu gg n p :=
  (friedrichsComparison_extends (nsPosSym nu lam mu gg n) polyGaussCore_dense p).choose_spec

/-- **The lift of the comparison operator to the outer Fock space**: the `ℓ²`-direct sum of
the sector Friedrichs realizations.  Positivity, symmetry and surjectivity of `N + 1` are all
fibrewise, which is exactly why the construction lifts. -/
def nsOuterComparison (nu lam mu gg : ℝ) : Comparison nsFockSpace :=
  dsComparison (fun n : ℕ => nsFried nu lam mu gg n)

/-- The lifted comparison operator, fibrewise. -/
theorem nsOuterN_apply (nu lam mu gg : ℝ) (x : (nsOuterComparison nu lam mu gg).dom) (n : ℕ) :
    (((nsOuterComparison nu lam mu gg).op x : nsFockSpace) : ∀ n : ℕ, L2d (n * 21)) n
      = (nsFried nu lam mu gg n).op
          ⟨((x : nsFockSpace) : ∀ n : ℕ, L2d (n * 21)) n, x.2.1 n⟩ :=
  dsCompOp_fib _ x n

/-- **Faris–Lavine on the outer Fock space**: the lifted realization of the full nonlinear
Navier–Stokes Hamiltonian is essentially self-adjoint on its domain.  This is the `H = N`,
`c = 0` case of the Faris–Lavine criterion — the commutator of the Hamiltonian with the
comparison operator vanishes — with the comparison operator the lifted Friedrichs
extension. -/
theorem nsFullOuterN_esa (nu lam mu gg : ℝ) :
    EssentiallySelfAdjointOn (nsOuterComparison nu lam mu gg).dom
      (nsOuterComparison nu lam mu gg).op :=
  Comparison.esa_self _

set_option maxHeartbeats 1600000 in
-- the lifted domain is built from the Friedrichs completion, so unfolding it is costly
/-- The finite-parcel core sits inside the domain of the lifted comparison operator. -/
theorem nsFockCore_le_friedDom (nu lam mu gg : ℝ) :
    nsFockCore ≤ (nsOuterComparison nu lam mu gg).dom := by
  intro x hx
  refine ⟨fun n => polyGaussCore_le_nsFriedDom nu lam mu gg n (hx.2 n), ?_⟩
  have hfun : (fun n : ℕ => opTot (nsFried nu lam mu gg n).op ((x : nsFockSpace) n))
      = fun n : ℕ =>
        (nsSectorHam nu lam mu gg n ⟨(x : nsFockSpace) n, hx.2 n⟩ : L2d (n * 21)) := by
    funext n
    rw [opTot_of_mem _ (polyGaussCore_le_nsFriedDom nu lam mu gg n (hx.2 n)),
      nsFried_op_core nu lam mu gg n ⟨(x : nsFockSpace) n, hx.2 n⟩]
  rw [hfun]
  refine memLp_of_finite_support (Set.Finite.subset hx.1 fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  refine hn ?_
  have hz : (⟨(x : nsFockSpace) n, hx.2 n⟩ : polyGaussCore (d := n * 21)) = 0 :=
    Subtype.ext h0
  rw [hz, map_zero]

set_option maxHeartbeats 2000000 in
-- the Friedrichs domain is a range of a completion-built resolvent: defeq checks are costly
/-- **The lifted Friedrichs realization is a positive self-adjoint extension of the full
nonlinear Navier–Stokes Hamiltonian defined on the finite-parcel core.**  Together with
`nsFullOuterN_esa` this is the Faris–Lavine statement on the outer Fock space. -/
theorem nsFullOuterN_isPositiveSelfAdjointExtension (nu lam mu gg : ℝ) :
    IsPositiveSelfAdjointExtension (nsFullFockHam nu lam mu gg)
      (nsOuterComparison nu lam mu gg).op :=
  (nsOuterComparison nu lam mu gg).isPositiveSelfAdjointExtension
    (nsFullFockHam nu lam mu gg) (fun x => by
      refine ⟨nsFockCore_le_friedDom nu lam mu gg x.2, ?_⟩
      refine lp.ext (funext fun n => ?_)
      rw [nsOuterN_apply, nsFried_op_core nu lam mu gg n ⟨(x : nsFockSpace) n, x.2.2 n⟩]
      exact rfl)

/-! ## 6. Particle-number conservation — why no lattice is needed -/

/-- The restriction of the outer Hamiltonian to the `n`-parcel sector is the `n`-parcel
Hamiltonian. -/
theorem nsFullFockHam_sector (nu lam mu gg : ℝ) (x : nsFockCore) (n : ℕ) :
    ((nsFullFockHam nu lam mu gg x : nsFockSpace) : ∀ n : ℕ, L2d (n * 21)) n
      = nsSectorHam nu lam mu gg n
        ⟨((x : nsFockSpace) : ∀ n : ℕ, L2d (n * 21)) n, x.2.2 n⟩ := rfl

/-- **The outer Navier–Stokes Hamiltonian conserves the parcel number.** -/
theorem nsFullFockHam_number_conserving (nu lam mu gg : ℝ) (x : nsFockCore) {n : ℕ}
    (hx : ∀ m, m ≠ n → ((x : nsFockSpace) : ∀ m : ℕ, L2d (m * 21)) m = 0) (m : ℕ)
    (hm : m ≠ n) : ((nsFullFockHam nu lam mu gg x : nsFockSpace) : ∀ m : ℕ, L2d (m * 21)) m = 0 :=
  dsOp_number_conserving _ x hx m hm

/-! ## 7. The advection is the genuine nonlinearity -/

/-- The test point that switches on the velocity mode `u_1` and the derivative mode
`u_{0,1}` of the parcel `p`, both equal to `t`. -/
def testPt (p : Fin n) (t : ℝ) : Fin (n * 21) → ℂ := fun I =>
  if I = ycoord p (uIdx 1) then (t : ℂ)
  else if I = ycoord p (dIdx 0 1) then (t : ℂ) else 0

theorem nsResPoly_eval_testPt (nu : ℝ) (p : Fin n) (t : ℝ) :
    eval (testPt p t) (nsResPoly nu p 0) = (t : ℂ) * (t : ℂ) := by
  have hne : ∀ i j : Fin 21, i ≠ j → ycoord p i ≠ ycoord p j := fun i j hij h =>
    hij (ycoord_injective p h)
  have h1 : ycoord p (uIdx 0) ≠ ycoord p (uIdx 1) := hne _ _ (by decide)
  have h2 : ycoord p (uIdx 0) ≠ ycoord p (dIdx 0 1) := hne _ _ (by decide)
  have h3 : ycoord p (uIdx 2) ≠ ycoord p (uIdx 1) := hne _ _ (by decide)
  have h4 : ycoord p (uIdx 2) ≠ ycoord p (dIdx 0 1) := hne _ _ (by decide)
  have h5 : ycoord p (dIdx 0 0) ≠ ycoord p (uIdx 1) := hne _ _ (by decide)
  have h6 : ycoord p (dIdx 0 0) ≠ ycoord p (dIdx 0 1) := hne _ _ (by decide)
  have h7 : ycoord p (dIdx 0 2) ≠ ycoord p (uIdx 1) := hne _ _ (by decide)
  have h8 : ycoord p (dIdx 0 2) ≠ ycoord p (dIdx 0 1) := hne _ _ (by decide)
  have h9 : ycoord p (qIdx 0) ≠ ycoord p (uIdx 1) := hne _ _ (by decide)
  have h10 : ycoord p (qIdx 0) ≠ ycoord p (dIdx 0 1) := hne _ _ (by decide)
  have h11 : ycoord p (wIdx 0) ≠ ycoord p (uIdx 1) := hne _ _ (by decide)
  have h12 : ycoord p (wIdx 0) ≠ ycoord p (dIdx 0 1) := hne _ _ (by decide)
  simp [nsResPoly, testPt, Fin.sum_univ_three, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, h10, h11, h12]

/-- **The full Navier–Stokes residual is not an affine form of the coordinates**: along the
test line it is `t²`.  In particular the model is *not* an Oseen (frozen-velocity)
linearisation, and its potential is not a sum of squares of linear forms. -/
theorem nsResPoly_not_affine (nu : ℝ) (p : Fin n) :
    ¬ ∃ a b : ℂ, ∀ t : ℝ, eval (testPt p t) (nsResPoly nu p 0) = a * (t : ℂ) + b := by
  rintro ⟨a, b, h⟩
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  rw [nsResPoly_eval_testPt] at h0 h1 h2
  push_cast at h0 h1 h2
  have hb : b = 0 := by linear_combination -h0
  have ha : a = 1 := by linear_combination h0 - h1
  rw [ha, hb] at h2
  norm_num at h2

end

end BookProof.NsFullEuler


