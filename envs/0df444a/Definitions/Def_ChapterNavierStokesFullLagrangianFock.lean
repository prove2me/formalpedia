-- Prove2me | Definitions.Def_ChapterNavierStokesFullLagrangianFock
-- name    : ChapterNavierStokesFullLagrangianFock
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-27T12:57:58.619649+00:00
-- url     : https://prove2.me/theorems/4e03bc95-85f6-4f89-9997-67e6ac9a130d
-- title:
--   The Lean 4 theorem `realCoeff_C_ofReal` in the `?` chapter of the timepiece formalization
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterNavierStokesFullLagrangianFock.lean`): generated def bundle for ChapterNavierStokesFullLagrangianFock. See BookProof/ChapterNavierStokesFullLagrangianFock.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFullLagrangianFock.lean

import Theorems.Thm_BookProof_FriedrichsExtension_friedrichs_extension_exists_complete
import Theorems.Thm_BookProof_QgOuterFock_dsOp_quadForm_nonneg
import Theorems.Thm_BookProof_StoneBridge_exists_stone_flow_of_positive
import Theorems.Thm_BookProof_QgOuterFockFL_friedrichsComparison_extends
import Theorems.Thm_BookProof_QgOuterFockFL_Comparison_isPositiveSelfAdjointExtension
import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_add

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_mul

import Theorems.Thm_BookProof_YangMillsHermite_RealCoeff_sum

import Theorems.Thm_BookProof_YangMillsHermite_realCoeff_X




import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_symmetricOn_op

import Theorems.Thm_BookProof_YangMillsHermite_mulOp_polySym













import Theorems.Thm_BookProof_YangMillsHermite_starP_C







import Theorems.Thm_BookProof_YangMillsHermite_momOp_polySym


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
# The **full** Navier–Stokes Hamiltonian in **Lagrangian** variables on the nested Fock space

The companion of `BookProof.ChapterNavierStokesFullEulerianFock`: the same fluid, written in
Lagrangian (material) variables, again **without any approximation** — the pressure term
carries the exact Piola transform `cof(F)ᵀ ∇_a q`, which is *quadratic* in the deformation
gradient, and incompressibility is the exact `det F = 1`, which is *cubic*.  Neither is
linearised, no Oseen background velocity appears, and there is no lattice.

## The variables (36 per parcel)

* `ξ_i` (3) — the material position (value of the flow map) of the parcel;
* `v_i` (3) — the parcel velocity `∂_t ξ_i`;
* `a_i` (3) — the material acceleration `D v_i/Dt`;
* `F_{ij}` (9) — the **deformation gradient**, the independent coordinates representing the
  spatial derivatives `∂ξ_i/∂a_j` of the flow map;
* `V_{ij}` (9) — the independent coordinates representing the spatial derivatives
  `∂v_i/∂a_j` of the velocity;
* `S_i` (3) — the coordinates representing the viscous force `ν Δ v_i`;
* `q_i` (3) — the material pressure gradient `∂_i q`;
* `y_j` (3) — the auxiliary coordinates of the field expansion.

## The constraint forms (28 per parcel)

* **The Lagrangian momentum equation** `R_i = a_i + Σ_j cof(F)_{ji} q_j − S_i` (3 per
  parcel).  `cof(F)` is the exact cofactor matrix of the deformation gradient
  (`cofPoly`), so the pressure term is the exact Piola transform of the Eulerian pressure
  gradient — a *quadratic* coupling of the derivative variables to the pressure, with no
  linearisation.
* **Volume preservation** `det F − 1 = 0` (1 per parcel) — the exact incompressibility
  constraint in Lagrangian variables, a **cubic** polynomial in the derivative coordinates;
  `volumePoly_not_quadratic` shows that it is not equal to its familiar linearisation
  `tr F − 3`, nor to any quadratic form, along the isotropic line.
* **The gauge fixing of the derivative variables** `λ(F_{ij} − δ_{ij} + ξ_i − ξ_i^{next})`
  (9 per parcel) and `λ'(V_{ij} + v_i − v_i^{next})` (9 per parcel): the statements that the
  coordinates `F_{ij}` and `V_{ij}`, which *represent* spatial derivatives, are the finite
  differences of the flow map and of the velocity between neighbouring parcels.  They couple
  two parcels, so the Hamiltonian is genuinely interacting.
* **The gauge fixing of the viscous variables** `μ(S_i + Σ_j V_{ij} − Σ_j V_{ij}^{next})`
  (3 per parcel).
* **The `y`-gauge fixing** `g·y_j` (3 per parcel).

## What is proved

Exactly the list of the Eulerian module, for this model:
`lagSectorHam_quadForm_nonneg`, `lagSector_friedrichs_extension`,
`lagFullFockHam_quadForm_nonneg`, `lagFullFock_friedrichs_extension`,
`lagFullOuterN_esa` (**Faris–Lavine on the outer Fock space**, with the lifted Friedrichs
extension as comparison operator and `c = 0`),
`lagFullOuterN_isPositiveSelfAdjointExtension`, `lagFullFock_stone_flow`,
`lagFullFockHam_number_conserving`, and the nonlinearity witnesses
`detPoly_eval_testPt`, `volumePoly_not_quadratic`.

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

namespace BookProof.NsFullLagrangian

open MvPolynomial
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL BookProof.Qg3DGaugeFL
open BookProof.ChapterStoneResolvent

noncomputable section

/-! ## 1. The coordinates of the `n`-parcel sector -/

/-- The global coordinate of the `i`-th field-space direction of the `p`-th parcel. -/
def ycoord {n : ℕ} (p : Fin n) (i : Fin 36) : Fin (n * 36) := finProdFinEquiv (p, i)

theorem ycoord_injective {n : ℕ} (p : Fin n) : Function.Injective (ycoord p) := by
  intro i i' h
  have := finProdFinEquiv.injective h
  simpa using congrArg Prod.snd this

@[simp] theorem ycoord_inj_iff {n : ℕ} (p : Fin n) (i j : Fin 36) :
    ycoord p i = ycoord p j ↔ i = j :=
  ⟨fun h => ycoord_injective p h, fun h => by rw [h]⟩

/-- The material position `ξ_i`. -/
def xiIdx (i : Fin 3) : Fin 36 := ⟨i.val, by have := i.isLt; omega⟩

/-- The parcel velocity `v_i`. -/
def vIdx (i : Fin 3) : Fin 36 := ⟨3 + i.val, by have := i.isLt; omega⟩

/-- The material acceleration `a_i`. -/
def accIdx (i : Fin 3) : Fin 36 := ⟨6 + i.val, by have := i.isLt; omega⟩

/-- The deformation gradient `F_{ij}`. -/
def fIdx (i j : Fin 3) : Fin 36 := ⟨9 + 3 * i.val + j.val, by
  have := i.isLt; have := j.isLt; omega⟩

/-- The velocity gradient `V_{ij}`. -/
def vgIdx (i j : Fin 3) : Fin 36 := ⟨18 + 3 * i.val + j.val, by
  have := i.isLt; have := j.isLt; omega⟩

/-- The viscous force `S_i`. -/
def sIdx (i : Fin 3) : Fin 36 := ⟨27 + i.val, by have := i.isLt; omega⟩

/-- The material pressure gradient `q_i`. -/
def qIdx (i : Fin 3) : Fin 36 := ⟨30 + i.val, by have := i.isLt; omega⟩

/-- The auxiliary expansion coordinate `y_j`. -/
def yIdx (j : Fin 3) : Fin 36 := ⟨33 + j.val, by have := j.isLt; omega⟩

/-- Cyclic shift of a spatial index, used to write the cofactor matrix. -/
def cyc (i : Fin 3) (k : ℕ) : Fin 3 := ⟨(i.val + k) % 3, Nat.mod_lt _ (by norm_num)⟩

/-! ## 2. The constraint polynomials of one parcel -/

variable {n : ℕ}

/-- A real constant is a real-coefficient polynomial. -/
theorem realCoeff_C_ofReal (c : ℝ) :
    RealCoeff (C ((c : ℝ) : ℂ) : MvPolynomial (Fin (n * 36)) ℂ) := by
  rw [RealCoeff, starP_C, Complex.conj_ofReal]

/-- **The cofactor matrix of the deformation gradient**,
`cof(F)_{ij} = F_{i+1,j+1} F_{i+2,j+2} − F_{i+1,j+2} F_{i+2,j+1}` (indices mod 3).  It is the
exact quadratic in the derivative coordinates that the Piola transform of the pressure
gradient requires. -/
def cofPoly (p : Fin n) (i j : Fin 3) : MvPolynomial (Fin (n * 36)) ℂ :=
  X (ycoord p (fIdx (cyc i 1) (cyc j 1))) * X (ycoord p (fIdx (cyc i 2) (cyc j 2)))
    + C ((-1 : ℝ) : ℂ) *
      (X (ycoord p (fIdx (cyc i 1) (cyc j 2))) * X (ycoord p (fIdx (cyc i 2) (cyc j 1))))

/-- **The determinant of the deformation gradient**, expanded along the first row. -/
def detPoly (p : Fin n) : MvPolynomial (Fin (n * 36)) ℂ :=
  ∑ j : Fin 3, X (ycoord p (fIdx 0 j)) * cofPoly p 0 j

/-- **The Lagrangian momentum equation** `R_i = a_i + Σ_j cof(F)_{ji} q_j − S_i`: the
material acceleration, the exact Piola-transformed pressure gradient and the viscous
force. -/
def lagResPoly (p : Fin n) (i : Fin 3) : MvPolynomial (Fin (n * 36)) ℂ :=
  X (ycoord p (accIdx i)) + (∑ j : Fin 3, cofPoly p j i * X (ycoord p (qIdx j)))
    + C ((-1 : ℝ) : ℂ) * X (ycoord p (sIdx i))

/-- **Volume preservation** `det F − 1 = 0`, the exact incompressibility constraint in
Lagrangian variables. -/
def volumePoly (p : Fin n) : MvPolynomial (Fin (n * 36)) ℂ :=
  detPoly p + C ((-1 : ℝ) : ℂ)

/-- **The gauge fixing of the deformation-gradient variables**: `F_{ij} − δ_{ij}` is the
finite difference of the flow map between neighbouring parcels. -/
def fGaugePoly (lam : ℝ) (p : Fin n) (i j : Fin 3) : MvPolynomial (Fin (n * 36)) ℂ :=
  C ((lam : ℝ) : ℂ) * (X (ycoord p (fIdx i j)) + C ((if i = j then -1 else 0 : ℝ) : ℂ)
    + X (ycoord p (xiIdx i)) + C ((-1 : ℝ) : ℂ) * X (ycoord (nextPart p) (xiIdx i)))

/-- **The gauge fixing of the velocity-gradient variables**. -/
def vGaugePoly (lam : ℝ) (p : Fin n) (i j : Fin 3) : MvPolynomial (Fin (n * 36)) ℂ :=
  C ((lam : ℝ) : ℂ) * (X (ycoord p (vgIdx i j)) + X (ycoord p (vIdx i))
    + C ((-1 : ℝ) : ℂ) * X (ycoord (nextPart p) (vIdx i)))

/-- **The gauge fixing of the viscous variables**. -/
def sGaugePoly (mu : ℝ) (p : Fin n) (i : Fin 3) : MvPolynomial (Fin (n * 36)) ℂ :=
  C ((mu : ℝ) : ℂ) * (X (ycoord p (sIdx i)) + (∑ j : Fin 3, X (ycoord p (vgIdx i j)))
    + C ((-1 : ℝ) : ℂ) * ∑ j : Fin 3, X (ycoord (nextPart p) (vgIdx i j)))

/-- **The `y`-gauge fixing**. -/
def yGaugePoly (gg : ℝ) (p : Fin n) (j : Fin 3) : MvPolynomial (Fin (n * 36)) ℂ :=
  C ((gg : ℝ) : ℂ) * X (ycoord p (yIdx j))

theorem realCoeff_cofPoly (p : Fin n) (i j : Fin 3) : RealCoeff (cofPoly p i j) :=
  ((realCoeff_X _).mul (realCoeff_X _)).add
    ((realCoeff_C_ofReal _).mul ((realCoeff_X _).mul (realCoeff_X _)))

theorem realCoeff_detPoly (p : Fin n) : RealCoeff (detPoly p) :=
  RealCoeff.sum fun j _ => (realCoeff_X _).mul (realCoeff_cofPoly p 0 j)

theorem realCoeff_lagResPoly (p : Fin n) (i : Fin 3) : RealCoeff (lagResPoly p i) :=
  ((realCoeff_X _).add
      (RealCoeff.sum fun j _ => (realCoeff_cofPoly p j i).mul (realCoeff_X _))).add
    ((realCoeff_C_ofReal _).mul (realCoeff_X _))

theorem realCoeff_volumePoly (p : Fin n) : RealCoeff (volumePoly p) :=
  (realCoeff_detPoly p).add (realCoeff_C_ofReal _)

theorem realCoeff_fGaugePoly (lam : ℝ) (p : Fin n) (i j : Fin 3) :
    RealCoeff (fGaugePoly lam p i j) :=
  (realCoeff_C_ofReal _).mul
    ((((realCoeff_X _).add (realCoeff_C_ofReal _)).add (realCoeff_X _)).add
      ((realCoeff_C_ofReal _).mul (realCoeff_X _)))

theorem realCoeff_vGaugePoly (lam : ℝ) (p : Fin n) (i j : Fin 3) :
    RealCoeff (vGaugePoly lam p i j) :=
  (realCoeff_C_ofReal _).mul
    (((realCoeff_X _).add (realCoeff_X _)).add ((realCoeff_C_ofReal _).mul (realCoeff_X _)))

theorem realCoeff_sGaugePoly (mu : ℝ) (p : Fin n) (i : Fin 3) :
    RealCoeff (sGaugePoly mu p i) :=
  (realCoeff_C_ofReal _).mul
    (((realCoeff_X _).add (RealCoeff.sum fun _ _ => realCoeff_X _)).add
      ((realCoeff_C_ofReal _).mul (RealCoeff.sum fun _ _ => realCoeff_X _)))

theorem realCoeff_yGaugePoly (gg : ℝ) (p : Fin n) (j : Fin 3) :
    RealCoeff (yGaugePoly gg p j) := (realCoeff_C_ofReal _).mul (realCoeff_X _)

/-- The `28` constraint forms of one parcel, in one family. -/
def lagFormOf (lam lam' mu gg : ℝ) (p : Fin n) (r : Fin 28) : MvPolynomial (Fin (n * 36)) ℂ :=
  if h : r.val < 3 then lagResPoly p ⟨r.val, h⟩
  else if r.val = 3 then volumePoly p
  else if h2 : r.val < 13 then
    fGaugePoly lam p ⟨(r.val - 4) / 3, by omega⟩ ⟨(r.val - 4) % 3, by omega⟩
  else if h3 : r.val < 22 then
    vGaugePoly lam' p ⟨(r.val - 13) / 3, by omega⟩ ⟨(r.val - 13) % 3, by omega⟩
  else if h4 : r.val < 25 then sGaugePoly mu p ⟨r.val - 22, by omega⟩
  else yGaugePoly gg p ⟨r.val - 25, by have := r.isLt; omega⟩

theorem realCoeff_lagFormOf (lam lam' mu gg : ℝ) (p : Fin n) (r : Fin 28) :
    RealCoeff (lagFormOf lam lam' mu gg p r) := by
  unfold lagFormOf
  split_ifs
  · exact realCoeff_lagResPoly _ _
  · exact realCoeff_volumePoly _
  · exact realCoeff_fGaugePoly _ _ _ _
  · exact realCoeff_vGaugePoly _ _ _ _
  · exact realCoeff_sGaugePoly _ _ _
  · exact realCoeff_yGaugePoly _ _ _

/-! ## 3. The `n`-parcel Hamiltonian -/

/-- The field-space direction carrying the `s`-th momentum of a parcel: the flow map, the
velocity and their derivative coordinates are the canonical coordinates. -/
def momIdx (s : Fin 24) : Fin 36 :=
  if h : s.val < 3 then xiIdx ⟨s.val, h⟩
  else if h2 : s.val < 6 then vIdx ⟨s.val - 3, by omega⟩
  else if h3 : s.val < 15 then
    fIdx ⟨(s.val - 6) / 3, by omega⟩ ⟨(s.val - 6) % 3, by omega⟩
  else vgIdx ⟨(s.val - 15) / 3, by have := s.isLt; omega⟩ ⟨(s.val - 15) % 3, by omega⟩

/-- The momentum operators of the `n`-parcel sector. -/
def lagPiN (n : ℕ) (m : Fin (n * 24)) :
    (polyGaussCore (d := n * 36)) →ₗ[ℂ] (polyGaussCore (d := n * 36)) :=
  (coreRepPoly (n * 36)).op
    (momOp (ycoord (finProdFinEquiv.symm m).1 (momIdx (finProdFinEquiv.symm m).2)))

/-- The constraint (multiplication) operators of the `n`-parcel sector. -/
def lagFieldN (lam lam' mu gg : ℝ) (n : ℕ) (m : Fin (n * 28)) :
    (polyGaussCore (d := n * 36)) →ₗ[ℂ] (polyGaussCore (d := n * 36)) :=
  (coreRepPoly (n * 36)).op
    (mulOp (lagFormOf lam lam' mu gg (finProdFinEquiv.symm m).1 (finProdFinEquiv.symm m).2))

theorem lagPiN_symmetricOn (n : ℕ) (m : Fin (n * 24)) :
    SymmetricOn (polyGaussCore (d := n * 36))
      ((polyGaussCore (d := n * 36)).subtype.comp (lagPiN n m)) :=
  (coreRepPoly (n * 36)).symmetricOn_op (momOp_polySym _)

theorem lagFieldN_symmetricOn (lam lam' mu gg : ℝ) (n : ℕ) (m : Fin (n * 28)) :
    SymmetricOn (polyGaussCore (d := n * 36))
      ((polyGaussCore (d := n * 36)).subtype.comp (lagFieldN lam lam' mu gg n m)) :=
  (coreRepPoly (n * 36)).symmetricOn_op (mulOp_polySym (realCoeff_lagFormOf _ _ _ _ _ _))

/-- **The `n`-parcel Navier–Stokes Hamiltonian in Lagrangian variables**, with the exact
Piola pressure term and the exact `det F = 1` constraint. -/
def lagSectorHam (lam lam' mu gg : ℝ) (n : ℕ) :
    (polyGaussCore (d := n * 36)) →ₗ[ℂ] L2d (n * 36) :=
  weylOp (lagPiN n) (lagFieldN lam lam' mu gg n)

theorem lagSectorHam_symmetricOn (lam lam' mu gg : ℝ) (n : ℕ) :
    SymmetricOn (polyGaussCore (d := n * 36)) (lagSectorHam lam lam' mu gg n) :=
  weylOpDom_symmetricOn (lagPiN_symmetricOn n) (lagFieldN_symmetricOn lam lam' mu gg n)

/-- **The `n`-parcel Lagrangian auxiliary sum-of-squares operator is bounded below.**  Its
quadratic form is a sum of squares (`lagSectorHam = weylOp … = ½ Σ π² + ½ Σ form²`), which is
*not* an assertion that the Navier–Stokes Hamiltonian is bounded below — it is not
(`BookProof.NsKoopman.nsKoopmanOp_not_bounded_below`). -/
theorem lagSectorHam_quadForm_nonneg (lam lam' mu gg : ℝ) (n : ℕ)
    (x : polyGaussCore (d := n * 36)) : 0 ≤ quadForm (lagSectorHam lam lam' mu gg n) x :=
  weylOpDom_quadForm_nonneg (lagPiN_symmetricOn n) (lagFieldN_symmetricOn lam lam' mu gg n) x

/-- **The `n`-parcel Lagrangian Hamiltonian has a positive self-adjoint (Friedrichs)
extension.** -/
theorem lagSector_friedrichs_extension (lam lam' mu gg : ℝ) (n : ℕ) :
    ∃ (Dom : Submodule ℂ (L2d (n * 36))) (A : Dom →ₗ[ℂ] L2d (n * 36)),
      IsPositiveSelfAdjointExtension (lagSectorHam lam lam' mu gg n) A :=
  friedrichs_extension_exists_complete
    ⟨polyGaussCore, lagSectorHam lam lam' mu gg n, lagSectorHam_symmetricOn lam lam' mu gg n,
      lagSectorHam_quadForm_nonneg lam lam' mu gg n⟩
    polyGaussCore_dense

/-! ## 4. The nested Fock space -/

/-- The nested Fock space `⊕ₙ L²(ℝ^{36n})` of the Lagrangian Navier–Stokes field. -/
abbrev lagFockSpace := lp (fun n : ℕ => L2d (n * 36)) 2

/-- The finite-parcel core. -/
def lagFockCore : Submodule ℂ lagFockSpace := dsCore (fun n : ℕ => polyGaussCore (d := n * 36))

theorem lagFockCore_dense :
    Dense ((lagFockCore : Submodule ℂ lagFockSpace) : Set lagFockSpace) :=
  dsCore_dense fun _ => polyGaussCore_dense

/-- **The full Lagrangian Navier–Stokes Hamiltonian on the nested Fock space.** -/
def lagFullFockHam (lam lam' mu gg : ℝ) : lagFockCore →ₗ[ℂ] lagFockSpace :=
  dsOp (fun n : ℕ => lagSectorHam lam lam' mu gg n)

theorem lagFullFockHam_symmetricOn (lam lam' mu gg : ℝ) :
    SymmetricOn lagFockCore (lagFullFockHam lam lam' mu gg) :=
  dsOp_symmetricOn _ fun n => lagSectorHam_symmetricOn lam lam' mu gg n

/-- **The outer Lagrangian auxiliary sum-of-squares operator is bounded below** — positivity is
fibrewise.  (The NS Hamiltonian itself is not bounded below:
`BookProof.NsKoopman.nsKoopmanOp_not_bounded_below`.) -/
theorem lagFullFockHam_quadForm_nonneg (lam lam' mu gg : ℝ) (x : lagFockCore) :
    0 ≤ quadForm (lagFullFockHam lam lam' mu gg) x :=
  dsOp_quadForm_nonneg _ (fun n u => lagSectorHam_quadForm_nonneg lam lam' mu gg n u) x

/-- **The full Lagrangian Navier–Stokes Hamiltonian on the nested Fock space has a positive
self-adjoint (Friedrichs) extension.** -/
theorem lagFullFock_friedrichs_extension (lam lam' mu gg : ℝ) :
    ∃ (Dom : Submodule ℂ lagFockSpace) (A : Dom →ₗ[ℂ] lagFockSpace),
      IsPositiveSelfAdjointExtension (lagFullFockHam lam lam' mu gg) A :=
  friedrichs_extension_exists_complete
    ⟨lagFockCore, lagFullFockHam lam lam' mu gg, lagFullFockHam_symmetricOn lam lam' mu gg,
      lagFullFockHam_quadForm_nonneg lam lam' mu gg⟩
    lagFockCore_dense

set_option maxHeartbeats 1000000 in
-- unfolding the `lp` instances of the Fock space in the Stone construction is costly
/-- **The unitary time evolution of the outer Lagrangian Hamiltonian** (Stone). -/
theorem lagFullFock_stone_flow (lam lam' mu gg : ℝ) :
    ∃ (T : UnboundedSelfAdjoint lagFockSpace) (U : ℝ → (lagFockSpace →L[ℂ] lagFockSpace)),
      IsStoneFlow T U := by
  obtain ⟨Dom, A, hA⟩ := lagFullFock_friedrichs_extension lam lam' mu gg
  obtain ⟨T, U, _, _, hflow⟩ := exists_stone_flow_of_positive lagFockCore_dense hA
  exact ⟨T, U, hflow⟩

/-! ## 5. Faris–Lavine on the outer Fock space -/

/-- The `n`-parcel Hamiltonian as a densely defined positive symmetric operator. -/
def lagPosSym (lam lam' mu gg : ℝ) (n : ℕ) : PosSymOp (L2d (n * 36)) where
  dom := polyGaussCore (d := n * 36)
  op := lagSectorHam lam lam' mu gg n
  sym := lagSectorHam_symmetricOn lam lam' mu gg n
  pos := lagSectorHam_quadForm_nonneg lam lam' mu gg n

/-- **The Friedrichs extension of the `n`-parcel Hamiltonian as a Faris–Lavine comparison
operator.** -/
def lagFried (lam lam' mu gg : ℝ) (n : ℕ) : Comparison (L2d (n * 36)) :=
  friedrichsComparison (lagPosSym lam lam' mu gg n) polyGaussCore_dense

theorem polyGaussCore_le_lagFriedDom (lam lam' mu gg : ℝ) (n : ℕ) :
    (polyGaussCore (d := n * 36)) ≤ (lagFried lam lam' mu gg n).dom := fun v hv =>
  (friedrichsComparison_extends (lagPosSym lam lam' mu gg n) polyGaussCore_dense ⟨v, hv⟩).choose

theorem lagFried_op_core (lam lam' mu gg : ℝ) (n : ℕ) (p : polyGaussCore (d := n * 36))
    (h : (p : L2d (n * 36)) ∈ (lagFried lam lam' mu gg n).dom) :
    (lagFried lam lam' mu gg n).op ⟨(p : L2d (n * 36)), h⟩ = lagSectorHam lam lam' mu gg n p :=
  (friedrichsComparison_extends (lagPosSym lam lam' mu gg n) polyGaussCore_dense p).choose_spec

/-- **The lift of the comparison operator to the outer Fock space.** -/
def lagOuterComparison (lam lam' mu gg : ℝ) : Comparison lagFockSpace :=
  dsComparison (fun n : ℕ => lagFried lam lam' mu gg n)

/-- The lifted comparison operator, fibrewise. -/
theorem lagOuterN_apply (lam lam' mu gg : ℝ) (x : (lagOuterComparison lam lam' mu gg).dom)
    (n : ℕ) :
    (((lagOuterComparison lam lam' mu gg).op x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n
      = (lagFried lam lam' mu gg n).op
          ⟨((x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n, x.2.1 n⟩ :=
  dsCompOp_fib _ x n

/-- **Faris–Lavine on the outer Fock space**: the lifted realization of the full Lagrangian
Navier–Stokes Hamiltonian is essentially self-adjoint on its domain — the `H = N`, `c = 0`
case of the criterion, with the lifted Friedrichs extension as comparison operator. -/
theorem lagFullOuterN_esa (lam lam' mu gg : ℝ) :
    EssentiallySelfAdjointOn (lagOuterComparison lam lam' mu gg).dom
      (lagOuterComparison lam lam' mu gg).op :=
  Comparison.esa_self _

set_option maxHeartbeats 1600000 in
-- the lifted domain is built from the Friedrichs completion, so unfolding it is costly
/-- The finite-parcel core sits inside the domain of the lifted comparison operator. -/
theorem lagFockCore_le_friedDom (lam lam' mu gg : ℝ) :
    lagFockCore ≤ (lagOuterComparison lam lam' mu gg).dom := by
  intro x hx
  refine ⟨fun n => polyGaussCore_le_lagFriedDom lam lam' mu gg n (hx.2 n), ?_⟩
  have hfun : (fun n : ℕ => opTot (lagFried lam lam' mu gg n).op ((x : lagFockSpace) n))
      = fun n : ℕ =>
        (lagSectorHam lam lam' mu gg n ⟨(x : lagFockSpace) n, hx.2 n⟩ : L2d (n * 36)) := by
    funext n
    rw [opTot_of_mem _ (polyGaussCore_le_lagFriedDom lam lam' mu gg n (hx.2 n)),
      lagFried_op_core lam lam' mu gg n ⟨(x : lagFockSpace) n, hx.2 n⟩]
  rw [hfun]
  refine memLp_of_finite_support (Set.Finite.subset hx.1 fun n hn => ?_)
  simp only [Set.mem_setOf_eq] at hn ⊢
  intro h0
  refine hn ?_
  have hz : (⟨(x : lagFockSpace) n, hx.2 n⟩ : polyGaussCore (d := n * 36)) = 0 :=
    Subtype.ext h0
  rw [hz, map_zero]

set_option maxHeartbeats 2000000 in
-- the Friedrichs domain is a range of a completion-built resolvent: defeq checks are costly
/-- **The lifted Friedrichs realization is a positive self-adjoint extension of the full
Lagrangian Navier–Stokes Hamiltonian defined on the finite-parcel core.** -/
theorem lagFullOuterN_isPositiveSelfAdjointExtension (lam lam' mu gg : ℝ) :
    IsPositiveSelfAdjointExtension (lagFullFockHam lam lam' mu gg)
      (lagOuterComparison lam lam' mu gg).op :=
  (lagOuterComparison lam lam' mu gg).isPositiveSelfAdjointExtension
    (lagFullFockHam lam lam' mu gg) (fun x => by
      refine ⟨lagFockCore_le_friedDom lam lam' mu gg x.2, ?_⟩
      refine lp.ext (funext fun n => ?_)
      rw [lagOuterN_apply, lagFried_op_core lam lam' mu gg n ⟨(x : lagFockSpace) n, x.2.2 n⟩]
      exact rfl)

/-! ## 6. Particle-number conservation — why no lattice is needed -/



/-- **The outer Lagrangian Hamiltonian conserves the parcel number.** -/
theorem lagFullFockHam_number_conserving (lam lam' mu gg : ℝ) (x : lagFockCore) {n : ℕ}
    (hx : ∀ m, m ≠ n → ((x : lagFockSpace) : ∀ m : ℕ, L2d (m * 36)) m = 0) (m : ℕ) (hm : m ≠ n) :
    ((lagFullFockHam lam lam' mu gg x : lagFockSpace) : ∀ m : ℕ, L2d (m * 36)) m = 0 :=
  dsOp_number_conserving _ x hx m hm

/-! ## 7. The incompressibility constraint is genuinely cubic -/

/-- The isotropic value assignment on the coordinates of one parcel: `F = t·I`, all other
coordinates zero. -/
def locVal (t : ℝ) (k : Fin 36) : ℂ :=
  if k = fIdx 0 0 ∨ k = fIdx 1 1 ∨ k = fIdx 2 2 then (t : ℂ) else 0

/-- The isotropic test point `F = t·I` on the parcel `p`. -/
def testPt (p : Fin n) (t : ℝ) : Fin (n * 36) → ℂ := fun I =>
  if (finProdFinEquiv.symm I).1 = p then locVal t (finProdFinEquiv.symm I).2 else 0









end

end BookProof.NsFullLagrangian


