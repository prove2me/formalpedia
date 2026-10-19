-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
-- name    : OAI_GroupTheory_Kervaire_MatrixShifts
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:27:32.665056+00:00
-- url     : https://prove2.me/theorems/7b3a48b9-6d89-4bff-bb48-4bd8125352b5
-- title:
--   Scalar matrices and labelled shifts
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   On $\ell^2(D\times A)$:
--
--   1. **Matrix units.** Coordinate projections and matrix units acting on the $D$ factor.
--   2. **Scalar tensor.** A complex $D\times D$ matrix $M$ acting as $M\otimes1$. It is multiplicative and $*$-preserving, unitary when $M$ is, and has trace $\mathrm{tr}\,M$.
--   3. **Labelled shift.** For a permutation $\sigma$ of $D$ and labels $a:D\to A$, the unitary induced by the coordinate permutation $(d,x)\mapsto(\sigma d,\,a(d)x)$.
--   4. **Weighted shift.** The labelled shift composed with a scalar diagonal $\mathrm{diag}(u)$:
--   $$
--   W(\sigma,u,a)=\mathrm{Shift}(\sigma,a)\,\mathrm{diag}(u).
--   $$
--   These matrices model the corner structure of a ribbon diagram.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/MatrixShifts.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/MatrixShifts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate

namespace KervaireMatrix

section
open KervaireRegular
open scoped Classical
variable {D A : Type*}

/-- Projection to a scalar coordinate, on the actual product-index regular Hilbert space. -/
def coordinateProjection (i : D) : Operator D A := by
  classical
  let L : Space D A →ₗ[ℂ] Space D A := {
    toFun := fun f => ⟨fun p => if p.1 = i then f p else 0,
      (lp.memℓp f).mono' (by intro p; split_ifs <;> simp)⟩
    map_add' := by
      intro f g
      ext p
      change (if p.1 = i then f p + g p else 0) =
        (if p.1 = i then f p else 0) + (if p.1 = i then g p else 0)
      split_ifs <;> simp
    map_smul' := by intro c f; ext p; by_cases h : p.1 = i <;> simp [h] }
  exact L.mkContinuous 1 (fun f => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) (fun p => by
      change ‖ite (p.1 = i) (f p) 0‖ ≤ _
      split_ifs <;> simp))

@[simp] theorem coordinateProjection_apply (i d : D) (f : Space D A) (a : A) :
    coordinateProjection i f (d,a) = if d = i then f (d,a) else 0 := by
  classical
  rfl

/-- The scalar matrix unit, continuously acting on all (possibly uncountable) group coordinates. -/
def matrixUnit (i j : D) : Operator D A := by
  classical
  exact (coordinateProjection i).comp
    (reindex (Equiv.prodCongr (Equiv.swap i j) (Equiv.refl A))).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem matrixUnit_apply (i j d : D) (f : Space D A) (a : A) :
    matrixUnit i j f (d,a) = if d = i then f (j,a) else 0 := by
  classical
  simp only [matrixUnit, ContinuousLinearMap.comp_apply, coordinateProjection_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
    reindex_apply, Equiv.prodCongr_symm, Equiv.symm_swap, Equiv.refl_symm,
    Equiv.prodCongr_apply]
  split_ifs with h
  · subst d; simp
  · rfl

/-- Equality of operators on the standard orthonormal basis. -/
theorem ext_delta {T U : Operator D A}
    (h : ∀ p : D × A, T (delta p) = U (delta p)) : T = U := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ENNReal) ≠ ⊤)
  intro p
  apply ContinuousLinearMap.ext
  intro c
  have hc : lp.single (E := fun _ : D × A => ℂ) 2 p c = c • delta p := by
    ext q
    simp [delta, Pi.single_apply]
  change T (lp.single 2 p c) = U (lp.single 2 p c)
  rw [hc, map_smul, map_smul, h]

/-- Matrix coefficients suffice to establish an adjoint identity. -/
theorem star_eq_of_coefficients {T U : Operator D A}
    (h : ∀ p q : D × A, star (T (delta p) q) = U (delta q) p) : star T = U := by
  apply ext_delta
  intro q
  ext p
  calc
    (star T) (delta q) p = inner ℂ (delta p) ((star T) (delta q)) :=
      (inner_delta_left _ _).symm
    _ = inner ℂ (T (delta p)) (delta q) := by
      rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
    _ = star (T (delta p) q) := inner_delta_right _ _
    _ = U (delta q) p := h p q

@[simp] theorem matrixUnit_star (i j : D) : star (matrixUnit (A := A) i j) = matrixUnit j i := by
  classical
  apply star_eq_of_coefficients
  rintro ⟨d,a⟩ ⟨e,b⟩
  simp only [matrixUnit_apply]
  by_cases he : e = i <;> by_cases hd : d = j
  · subst e; subst d
    simp [delta, Pi.single_apply, eq_comm]
  · simp [he,hd,delta,Prod.mk.injEq,Ne.symm hd]
  · simp [he,hd,delta,Prod.mk.injEq,Ne.symm he]
  · simp [he,hd]

variable [Fintype D]

/-- Scalar matrices embedded without any finite/countable assumption on the group. -/
def scalarTensor (M : Matrix D D ℂ) : Operator D A :=
  ∑ i, ∑ j, M i j • matrixUnit i j

@[simp] theorem scalarTensor_apply (M : Matrix D D ℂ) (f : Space D A) (d : D) (a : A) :
    scalarTensor M f (d,a) = ∑ j, M d j * f (j,a) := by
  classical
  change (∑ i, ∑ j, M i j • matrixUnit (A := A) i j) f (d,a) = _
  simp only [sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp [Finset.sum_ite_irrel]

@[simp] theorem scalarTensor_one : scalarTensor (1 : Matrix D D ℂ) = (1 : Operator D A) := by
  classical
  ext f ⟨d,a⟩
  simp [Matrix.one_apply]

@[simp] theorem scalarTensor_mul (M N : Matrix D D ℂ) :
    scalarTensor (A := A) (M*N) = scalarTensor M * scalarTensor N := by
  ext f ⟨d,a⟩
  simp only [scalarTensor_apply, mul_apply_eq_comp, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_assoc _ _ _

@[simp] theorem scalarTensor_star (M : Matrix D D ℂ) :
    star (scalarTensor (A := A) M) = scalarTensor (star M) := by
  classical
  apply star_eq_of_coefficients
  rintro ⟨sourceIndex,sourceElement⟩ ⟨targetIndex,targetElement⟩
  by_cases heq : sourceElement = targetElement
  · subst targetElement
    simp [delta, Pi.single_apply, Prod.mk.injEq]
  · simp [delta, Prod.mk.injEq, heq, Ne.symm heq]

variable [Group A]

/-- The scalar trace on tensoring with the regular identity is unnormalized matrix trace. -/
@[simp] theorem trace_scalarTensor (M : Matrix D D ℂ) :
    trace (scalarTensor (A := A) M) = Matrix.trace M := by
  classical
  simp only [trace_apply, inner_delta_left, scalarTensor_apply, Matrix.trace]
  simp [delta, Pi.single_apply, Prod.mk.injEq]

omit [Group A] in
/-- Unitary scalar matrices remain unitary in the full regular operator algebra. -/
theorem scalarTensor_mem_unitary {M : Matrix D D ℂ} (hM : M ∈ Matrix.unitaryGroup D ℂ) :
    scalarTensor (A := A) M ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff] at hM ⊢
  constructor
  · rw [scalarTensor_star, ← scalarTensor_mul, hM.1, scalarTensor_one]
  · rw [scalarTensor_star, ← scalarTensor_mul, hM.2, scalarTensor_one]

end

open KervaireRegular
open scoped Classical
variable {D A : Type*} [Group A]

/-- The coordinate permutation underlying a group-labelled shift.  Labels act
on the left so that the operator commutes with every right translation. -/
def labelledPermutation (σ : Equiv.Perm D) (a : D → A) : Equiv.Perm (D × A) where
  toFun p := (σ p.1, a p.1 * p.2)
  invFun p := (σ.symm p.1, (a (σ.symm p.1))⁻¹ * p.2)
  left_inv p := by simp
  right_inv p := by simp

/-- A corner-labelled permutation on the actual arbitrary-group Hilbert space. -/
def labelledShift (σ : Equiv.Perm D) (a : D → A) : Operator D A :=
  (reindex (labelledPermutation σ a)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem labelledShift_apply (σ : Equiv.Perm D) (a : D → A)
    (f : Space D A) (d : D) (x : A) :
    labelledShift σ a f (d,x) = f (σ.symm d, (a (σ.symm d))⁻¹ * x) := rfl

@[simp] theorem labelledShift_delta (σ : Equiv.Perm D) (a : D → A) (d : D) (x : A) :
    labelledShift σ a (delta (d,x)) = delta (σ d,a d*x) :=
  reindex_delta _ _

/-- This representation is unitary without dimensional or cardinality assumptions. -/
theorem labelledShift_unitary (σ : Equiv.Perm D) (a : D → A) :
    labelledShift σ a ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff]
  have hs : star (labelledShift σ a) =
      (reindex (labelledPermutation σ a)).symm.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact LinearIsometryEquiv.adjoint_eq_symm _
  rw [hs]
  constructor <;> ext f p <;> simp [labelledShift, mul_apply_eq_comp]

@[simp] theorem labelledShift_one :
    labelledShift (Equiv.refl D) (fun _ => (1 : A)) = 1 := by
  ext f ⟨d,x⟩
  simp

variable [Fintype D]

/-- A scalar diagonal on the finite coordinate set. -/
def scalarDiagonal (u : D → ℂ) : Operator D A :=
  scalarTensor (Matrix.diagonal u)

omit [Group A] in
@[simp] theorem scalarDiagonal_apply (u : D → ℂ) (f : Space D A) (d : D) (x : A) :
    scalarDiagonal u f (d,x) = u d * f (d,x) := by
  classical
  simp [scalarDiagonal, Matrix.diagonal]

omit [Group A] in
@[simp] theorem scalarDiagonal_delta (u : D → ℂ) (d : D) (x : A) :
    scalarDiagonal u (delta (d,x)) = u d • delta (d,x) := by
  classical
  ext ⟨e,y⟩
  by_cases h : (e,y) = (d,x)
  · cases h
    simp [delta]
  · simp [delta, Ne.symm h]

omit [Group A] in
@[simp] theorem scalarDiagonal_one : scalarDiagonal (A := A) (fun _ : D => 1) = 1 := by
  ext f ⟨d,x⟩
  simp

omit [Group A] in
@[simp] theorem scalarDiagonal_mul (u v : D → ℂ) :
    scalarDiagonal (A := A) u * scalarDiagonal v = scalarDiagonal (u*v) := by
  ext f ⟨d,x⟩
  simp [mul_apply_eq_comp, mul_assoc]

omit [Group A] in
@[simp] theorem scalarDiagonal_star (u : D → ℂ) :
    star (scalarDiagonal (A := A) u) = scalarDiagonal (star u) := by
  dsimp [scalarDiagonal]
  rw [scalarTensor_star]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j; simp
  · simp [Matrix.star_apply, Matrix.diagonal, h, Ne.symm h]

omit [Group A] in
theorem scalarDiagonal_unitary (u : D → ℂ) (hu : ∀ d, u d ∈ unitary ℂ) :
    scalarDiagonal (A := A) u ∈ unitary (Operator D A) := by
  rw [Unitary.mem_iff, scalarDiagonal_star, scalarDiagonal_mul, scalarDiagonal_mul]
  have h1 : star u * u = 1 := funext fun d => (Unitary.mem_iff.mp (hu d)).1
  have h2 : u * star u = 1 := funext fun d => (Unitary.mem_iff.mp (hu d)).2
  rw [h1,h2]
  exact ⟨scalarDiagonal_one,scalarDiagonal_one⟩

/-- This includes both shifts: `S` has coefficient labels,
while `Theta` has only scalar phase labels. -/
def weightedShift (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A) : Operator D A :=
  labelledShift σ a * scalarDiagonal u

@[simp] theorem weightedShift_apply (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (f : Space D A) (d : D) (x : A) :
    weightedShift σ u a f (d,x) =
      u (σ.symm d) * f (σ.symm d, (a (σ.symm d))⁻¹*x) := by
  simp [weightedShift, mul_apply_eq_comp]

@[simp] theorem weightedShift_delta (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (d : D) (x : A) :
    weightedShift σ u a (delta (d,x)) = u d • delta (σ d,a d*x) := by
  simp [weightedShift,mul_apply_eq_comp]

theorem weightedShift_unitary (σ : Equiv.Perm D) (u : D → ℂ) (a : D → A)
    (hu : ∀ d, u d ∈ unitary ℂ) : weightedShift σ u a ∈ unitary (Operator D A) :=
  mul_mem (labelledShift_unitary σ a) (scalarDiagonal_unitary u hu)

end KervaireMatrix
namespace KervaireSpectral
@[simp] theorem scalarRotation_nat (j : ℕ) : scalarRotation j = 1 := by
  unfold scalarRotation
  rw [show ((2 * Real.pi * (j : ℝ) : ℝ) : ℂ) * Complex.I =
    (j : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_nat_mul_two_pi_mul_I j

end KervaireSpectral

end

end OAI


