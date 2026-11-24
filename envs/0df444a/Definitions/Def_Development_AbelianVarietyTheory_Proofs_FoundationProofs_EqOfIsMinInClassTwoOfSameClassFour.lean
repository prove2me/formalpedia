-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:00:42.577707+00:00
-- url     : https://prove2.me/theorems/945542c7-3827-4401-999b-a59551bc6f4c
-- title:
--   Eq Of Is Min In Class Two Of Same Class Four
-- statement:
--   Definitions and structural lemmas for Eq Of Is Min In Class Two Of Same Class Four, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Theorems.Thm_GlobalTheory_IsSiegel_mk

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
section Unique
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}
theorem eq_polar_div_two (Q : QuadraticMap ℤ X ℝ) (x : X) : Q x = polar Q x x / 2 := by
  rw [polar_self, two_smul]; ring
end Unique
section Gram
variable {X : Type*} [AddCommGroup X] {ι : Type*}
def gram {R : Type*} [CommRing R] [Module R X] [Module R ℝ] (Q : QuadraticMap R X ℝ) (e : ι → X) :
    Matrix ι ι ℝ :=
  Matrix.of fun i j => polar Q (e i) (e j)
@[simp] theorem gram_apply {R : Type*} [CommRing R] [Module R X] [Module R ℝ]
    (Q : QuadraticMap R X ℝ) (e : ι → X) (i j : ι) : gram Q e i j = polar Q (e i) (e j) := rfl
theorem gram_isHermitian {R : Type*} [CommRing R] [Module R X] [Module R ℝ]
    (Q : QuadraticMap R X ℝ) (e : ι → X) : (gram Q e).IsHermitian := by
  ext i j
  simp [polar_comm Q (e j)]
theorem polar_sum_smul {R : Type*} [CommRing R] [Module R X] [Algebra R ℝ] [Fintype ι]
    (Q : QuadraticMap R X ℝ) (e : ι → X) (x y : ι → R) :
    polar Q (∑ i, x i • e i) (∑ i, y i • e i) =
      (fun i => algebraMap R ℝ (x i)) ⬝ᵥ (gram Q e *ᵥ fun i => algebraMap R ℝ (y i)) := by
  rw [← polarBilin_apply_apply, LinearMap.map_sum₂]
  simp only [map_sum, map_smul, LinearMap.smul_apply, polarBilin_apply_apply, dotProduct, mulVec,
    gram_apply, Algebra.smul_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring
def realExtension (Q : QuadraticMap ℤ X ℝ) : QuadraticForm ℝ (ℝ ⊗[ℤ] X) :=
  (1 / 2 : ℝ) • LinearMap.BilinMap.toQuadraticMap (LinearMap.liftBaseChangeEquiv ℝ
    ((LinearMap.liftBaseChangeEquiv ℝ (R := ℤ) (M := X) (N := ℝ)).toLinearMap.restrictScalars ℤ ∘ₗ
      Q.polarBilin))
@[simp] theorem realExtension_one_tmul (Q : QuadraticMap ℤ X ℝ) (x : X) :
    realExtension Q (1 ⊗ₜ x) = Q x := by
  rw [eq_polar_div_two Q]
  simp [realExtension]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
theorem gram_eq_of_comp {Q : QuadraticMap ℤ X ℝ} {P : QuadraticForm ℝ V} (φ : X →+ V)
    (h : ∀ x, P (φ x) = Q x) (e : ι → X) : gram Q e = gram P (fun i => φ (e i)) := by
  ext i j
  simp only [gram_apply, polar, ← map_add φ, h]
theorem dotProduct_gram_mulVec [Fintype ι] (P : QuadraticForm ℝ V) (v : ι → V) (x : ι → ℝ) :
    x ⬝ᵥ (gram P v *ᵥ x) = 2 * P (∑ i, x i • v i) := by
  have := polar_sum_smul P v x x
  rw [polar_self, two_smul] at this
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at this
  rw [← this, two_mul]
theorem gram_posDef_of_linearIndependent [Finite ι] {P : QuadraticForm ℝ V} (hP : P.PosDef)
    {v : ι → V} (hv : LinearIndependent ℝ v) : (gram P v).PosDef := by
  have := Fintype.ofFinite ι
  refine posDef_iff_dotProduct_mulVec.mpr ⟨gram_isHermitian P v, fun x hx => ?_⟩
  rw [star_trivial, dotProduct_gram_mulVec]
  refine mul_pos two_pos (hP _ fun h => hx ?_)
  exact funext (Fintype.linearIndependent_iff.mp hv x h)
theorem gram_posDef_iff [Finite ι] (P : QuadraticForm ℝ V) (v : Module.Basis ι ℝ V) :
    (gram P v).PosDef ↔ P.PosDef := by
  have := Fintype.ofFinite ι
  refine ⟨fun h y hy => ?_, fun h => gram_posDef_of_linearIndependent h v.linearIndependent⟩
  have h1 := h.dotProduct_mulVec_pos (x := v.equivFun y) (by simpa using hy)
  rw [star_trivial, dotProduct_gram_mulVec, v.sum_equivFun] at h1
  linarith
theorem realExtension_posDef_iff [Finite ι] (Q : QuadraticMap ℤ X ℝ) (e : Module.Basis ι ℤ X) :
    (realExtension Q).PosDef ↔ (gram Q e).PosDef := by
  rw [← gram_posDef_iff _ (Algebra.TensorProduct.basis ℝ e),
    gram_eq_of_comp (TensorProduct.mk ℤ ℝ X 1).toAddMonoidHom (realExtension_one_tmul Q) e]
  have : ⇑(Algebra.TensorProduct.basis ℝ e) = fun i => (1 : ℝ) ⊗ₜ[ℤ] e i :=
    funext fun i => Algebra.TensorProduct.basis_apply e i
  rw [this]
  rfl
end Gram
section Rational
variable {X : Type*} [AddCommGroup X] {ι : Type*} {Q : QuadraticMap ℤ X ℝ}
def ofIntBilin (β : LinearMap.BilinForm ℤ X) : QuadraticMap ℤ X ℝ :=
  (1 / 2 : ℝ) • (Int.castAddHom ℝ).toIntLinearMap.compQuadraticMap β.toQuadraticMap
@[simp] theorem ofIntBilin_apply (β : LinearMap.BilinForm ℤ X) (x : X) :
    ofIntBilin β x = (β x x : ℝ) / 2 := by
  simp [ofIntBilin]
  ring
end Rational
section Exists
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ}
end Exists
section Matrix
open ReciprocityTheory.ReducedBases (toReal SameClass IsMinInClass IsUniqueMinInClass)
variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}
def ofMatrix (A : Matrix (Fin d) (Fin d) ℝ) : QuadraticMap ℤ (Fin d → ℤ) ℝ :=
  (1 / 2 : ℝ) • LinearMap.BilinMap.toQuadraticMap (LinearMap.mk₂ ℤ (ReciprocityTheory.ReducedBases.polar A)
    (fun x y z => by simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, add_mul, Finset.sum_add_distrib])
    (fun n x y => by
      simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, Finset.mul_sum, mul_assoc])
    (fun x y z => by
      simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, mul_add, Finset.sum_add_distrib])
    (fun n x y => by
      simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, Finset.mul_sum, mul_left_comm]))
@[simp] theorem ofMatrix_apply (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) :
    ofMatrix A x = ReciprocityTheory.ReducedBases.Q A x := by
  change (1 / 2 : ℝ) * ReciprocityTheory.ReducedBases.polar A x x = ReciprocityTheory.ReducedBases.polar A x x / 2
  ring
theorem polar_ofMatrix (hA : A.IsHermitian) (x y : Fin d → ℤ) :
    polar (ofMatrix A) x y = ReciprocityTheory.ReducedBases.polar A x y := by
  have hs : ReciprocityTheory.ReducedBases.polar A y x = ReciprocityTheory.ReducedBases.polar A x y := by
    have hT : Aᵀ = A := by simpa using hA.eq
    rw [ReciprocityTheory.ReducedBases.polar, ReciprocityTheory.ReducedBases.polar, dotProduct_mulVec, ← mulVec_transpose, hT,
      dotProduct_comm]
  have ha : toReal (x + y) = toReal x + toReal y := by funext i; simp [toReal]
  simp only [polar, ofMatrix_apply, ReciprocityTheory.ReducedBases.Q]
  simp only [ReciprocityTheory.ReducedBases.polar, ha, mulVec_add, dotProduct_add, add_dotProduct] at hs ⊢
  linarith
theorem gram_ofMatrix (hA : A.IsHermitian) : gram (ofMatrix A) (Pi.basisFun ℤ (Fin d)) = A := by
  ext i j
  rw [gram_apply, polar_ofMatrix hA]
  simp [ReciprocityTheory.ReducedBases.polar, toReal, dotProduct, mulVec, Pi.single_apply]
theorem realExtension_ofMatrix_posDef (hA : A.PosDef) : (realExtension (ofMatrix A)).PosDef := by
  rwa [realExtension_posDef_iff _ (Pi.basisFun ℤ (Fin d)), gram_ofMatrix hA.isHermitian]
example : (realExtension (ofMatrix !![2, 1; 1, 2])).PosDef := by
  refine realExtension_ofMatrix_posDef (posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · have : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (by funext i; fin_cases i <;> simp [h.1, h.2])
    simp [dotProduct, mulVec, Fin.sum_univ_two]
    rcases this with h | h <;>
      nlinarith [sq_pos_of_ne_zero h, sq_nonneg (x 0 + x 1), sq_nonneg (x 0), sq_nonneg (x 1)]
end Matrix
end GlobalTheory.ClassMin
end


