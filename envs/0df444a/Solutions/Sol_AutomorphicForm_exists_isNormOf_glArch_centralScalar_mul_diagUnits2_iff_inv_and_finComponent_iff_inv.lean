-- Prove2me | solution 1 for AutomorphicForm.exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/6c1f0d32-12ca-51fb-b9d6-2d2f1d8aacc8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_AutomorphicForm_WeightedOrbitalRelation
import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

namespace E8A
namespace TW

section T1

variable (K : Type) [Field K] [NumberField K]

theorem adelicWeyl_val_apply (i j : Fin 2) :
    ((AutomorphicForm.adelicWeyl (𝓞 K) K : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      if i = j then 0 else 1 := by
  have : ((AutomorphicForm.adelicWeyl (𝓞 K) K : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j =
      algebraMap K (AdeleRing (𝓞 K) K) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) i j) := rfl
  rw [this]
  fin_cases i <;> fin_cases j <;> simp

theorem adelicWeyl_inv :
    (AutomorphicForm.adelicWeyl (𝓞 K) K)⁻¹ = AutomorphicForm.adelicWeyl (𝓞 K) K := by
  show (AutomorphicForm.globalPoints (𝓞 K) K AutomorphicForm.gl2Weyl)⁻¹ = AutomorphicForm.globalPoints (𝓞 K) K AutomorphicForm.gl2Weyl
  rw [← map_inv, AutomorphicForm.gl2Weyl_inv]

theorem val_centralScalar_mul_diagUnits2 (z a b : (AdeleRing (𝓞 K) K)ˣ) :
    ((AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 a b : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![(z : AdeleRing (𝓞 K) K) * a, 0; 0, (z : AdeleRing (𝓞 K) K) * b] := by
  rw [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.centralScalar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply]

theorem gamma_inv_eq_conj (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1 =
      AutomorphicForm.adelicWeyl (𝓞 K) K *
        (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) *
        (AutomorphicForm.adelicWeyl (𝓞 K) K)⁻¹ := by
  rw [adelicWeyl_inv]
  have hu1 : (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) * (algebraMap K (AdeleRing (𝓞 K) K) ((u : K)⁻¹)) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ u.ne_zero, map_one]
  apply Units.ext
  simp only [Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AutomorphicForm.centralScalar, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      adelicWeyl_val_apply, Units.coe_map, MonoidHom.coe_coe, mul_assoc, hu1]

theorem glArch_gamma_apply (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2
        (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) : GL (Fin 2) (InfiniteAdeleRing K)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j =
      ((!![(z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K), 0; 0, (z : AdeleRing (𝓞 K) K)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 := by
  rw [AdelicLevel.glArch_apply, val_centralScalar_mul_diagUnits2]
  simp [Units.coe_map, MonoidHom.coe_coe]

theorem isRegularSemisimple_glArch_gamma (u : Kˣ) (hu : (u : K) ≠ 1) (z : (AdeleRing (𝓞 K) K)ˣ) :
    AutomorphicForm.IsRegularSemisimple (AdelicLevel.glArch (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) := by
  unfold AutomorphicForm.IsRegularSemisimple
  rw [Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [glArch_gamma_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  have h0 : ((0 : AdeleRing (𝓞 K) K).1) = 0 := rfl
  rw [h0, mul_zero, sub_zero]
  have key : IsUnit (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 - ((z : AdeleRing (𝓞 K) K)).1) := by
    have h1 : ((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 - ((z : AdeleRing (𝓞 K) K)).1 =
        AdelicLevel.adeleArch (𝓞 K) K ((z : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) ((u : K) - 1))) := by
      rw [map_sub, map_one, mul_sub, mul_one]; rfl
    rw [h1]
    exact (z.isUnit.mul (((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu)).map _))).map _
  have : (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 + ((z : AdeleRing (𝓞 K) K)).1) ^ 2 -
      4 * (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 * ((z : AdeleRing (𝓞 K) K)).1) =
      (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).1 - ((z : AdeleRing (𝓞 K) K)).1) ^ 2 := by ring
  rw [this]
  exact key.pow 2

theorem finComponent_gamma_apply (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) (i j : Fin 2) :
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      ((!![(z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K), 0; 0, (z : AdeleRing (𝓞 K) K)] :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := by
  rw [AdelicLevel.finComponent_apply, AdelicLevel.glFin_apply, val_centralScalar_mul_diagUnits2]
  simp [Units.coe_map, MonoidHom.coe_coe]

theorem isRegularSemisimple_finComponent_gamma (u : Kˣ) (hu : (u : K) ≠ 1)
    (z : (AdeleRing (𝓞 K) K)ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    AutomorphicForm.IsRegularSemisimple (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) ∧
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 = 0 ∧
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K
      (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold AutomorphicForm.IsRegularSemisimple
    rw [Matrix.trace_fin_two, Matrix.det_fin_two]
    simp only [finComponent_gamma_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    have h0 : ((0 : AdeleRing (𝓞 K) K).2) v = 0 := rfl
    rw [h0, mul_zero, sub_zero]
    have key : IsUnit ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v - (((z : AdeleRing (𝓞 K) K)).2) v) := by
      have h1 : (((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v - (((z : AdeleRing (𝓞 K) K)).2) v =
          AdelicLevel.finAdeleEval (𝓞 K) K v (AdelicLevel.adeleFin (𝓞 K) K
            ((z : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) ((u : K) - 1)))) := by
        rw [map_sub, map_one, mul_sub, mul_one, map_sub, map_sub]; rfl
      rw [h1]
      exact ((z.isUnit.mul (((isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hu)).map _))).map _).map _
    have : ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v + (((z : AdeleRing (𝓞 K) K)).2) v) ^ 2 -
        4 * ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v * (((z : AdeleRing (𝓞 K) K)).2) v) =
        ((((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (u : K)).2) v - (((z : AdeleRing (𝓞 K) K)).2) v) ^ 2 := by ring
    rw [this]
    exact key.pow 2
  · rw [finComponent_gamma_apply]; rfl
  · rw [finComponent_gamma_apply]; rfl

end T1

section Generic

variable {A : Type*} [CommRing A]

theorem weyl_mul_self (w : GL (Fin 2) A) (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) : w * w = 1 := by
  apply Units.ext
  simp only [Units.val_mul, hw, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem weyl_inv_eq (w : GL (Fin 2) A) (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) : w⁻¹ = w :=
  inv_eq_of_mul_eq_one_left (weyl_mul_self w hw)

theorem map_weyl {B : Type*} [CommRing B] (φ : A →+* B) (w : GL (Fin 2) A)
    (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) :
    ((Matrix.GeneralLinearGroup.map φ w : GL (Fin 2) B) : Matrix (Fin 2) (Fin 2) B) = !![0, 1; 1, 0] := by
  ext i j
  change φ ((w : Matrix (Fin 2) (Fin 2) A) i j) = _
  rw [hw]
  fin_cases i <;> fin_cases j <;> simp

theorem weight_weyl_mul {F : Type*} [NormedField F] (w : GL (Fin 2) F)
    (hw : (w : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0]) (y : GL (Fin 2) F) :
    AutomorphicForm.LocalWeight.weight (w * y) = AutomorphicForm.LocalWeight.weight y := by
  unfold AutomorphicForm.LocalWeight.weight AdelicHeight.rowMaxNorm
  have h00 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 0 = (y : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 0 1 = (y : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 0 = (y : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) 1 1 = (y : Matrix (Fin 2) (Fin 2) F) 0 1 := by
    simp [Units.val_mul, hw, Matrix.mul_apply, Fin.sum_univ_two]
  have hdet : ‖((w * y : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det‖ = ‖(y : Matrix (Fin 2) (Fin 2) F).det‖ := by
    rw [Units.val_mul, Matrix.det_mul, norm_mul, hw]
    simp [Matrix.det_fin_two]
  rw [h00, h01, h10, h11, hdet, mul_comm (max _ _) (max _ _)]

theorem conj_mem_integralUnitsSet_iff (U : Set A) (w g : GL (Fin 2) A)
    (hw : (w : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0]) :
    w * g * w⁻¹ ∈ AutomorphicForm.integralUnitsSet U ↔ g ∈ AutomorphicForm.integralUnitsSet U := by
  have hwi : ((w⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![0, 1; 1, 0] := by
    rw [weyl_inv_eq _ hw, hw]
  have perm : ∀ (M : Matrix (Fin 2) (Fin 2) A),
      (!![0, 1; 1, 0] * M * !![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) A) = !![M 1 1, M 1 0; M 0 1, M 0 0] := fun M => by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, Matrix.vecHead, Matrix.vecTail]
  have hval : ((w * g * w⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1, ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0;
        ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1, ((g : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0] := by
    rw [Units.val_mul, Units.val_mul, hw, hwi]; exact perm _
  have hinv : (((w * g * w⁻¹)⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      !![((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 1, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 1 0;
        ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 1, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) 0 0] := by
    rw [show (w * g * w⁻¹)⁻¹ = w * g⁻¹ * w⁻¹ by rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc], Units.val_mul,
      Units.val_mul, hw, hwi]
    exact perm _
  simp only [AutomorphicForm.mem_integralUnitsSet, hval, hinv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using h1 1 1
      · simpa using h1 1 0
      · simpa using h1 0 1
      · simpa using h1 0 0
    · fin_cases i <;> fin_cases j
      · simpa using h2 1 1
      · simpa using h2 1 0
      · simpa using h2 0 1
      · simpa using h2 0 0
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using h1 1 1
      · simpa using h1 1 0
      · simpa using h1 0 1
      · simpa using h1 0 0
    · fin_cases i <;> fin_cases j
      · simpa using h2 1 1
      · simpa using h2 1 0
      · simpa using h2 0 1
      · simpa using h2 0 0

end Generic

section T2

theorem sigmaGL_toTensorGL (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (g : GL (Fin 2) A) :
    AutomorphicForm.sigmaGL K L A σ (AutomorphicForm.toTensorGL K L A g) = AutomorphicForm.toTensorGL K L A g := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change AutomorphicForm.sigmaTensor K L A σ
      ((Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)) =
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom ((g : Matrix (Fin 2) (Fin 2) A) i j)
  simp [AutomorphicForm.sigmaTensor, Algebra.TensorProduct.includeRight_apply]

theorem normString_conj_of_sigmaGL_eq (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (G δ : GL (Fin 2) (L ⊗[K] A)) (hG : AutomorphicForm.sigmaGL K L A σ G = G) :
    AutomorphicForm.normString K L A σ (G * δ * G⁻¹) = G * AutomorphicForm.normString K L A σ δ * G⁻¹ := by
  unfold AutomorphicForm.normString
  have hiter : ∀ i : ℕ, (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (G * δ * G⁻¹) =
      G * ((⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ) * G⁻¹ := by
    intro i
    induction i with
    | zero => rfl
    | succ n ih => rw [Function.iterate_succ_apply', ih, map_mul, map_mul, map_inv, hG, Function.iterate_succ_apply']
  have hmap : (List.range (Module.finrank K L)).map (fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] (G * δ * G⁻¹)) =
      ((List.range (Module.finrank K L)).map (fun i => (⇑(AutomorphicForm.sigmaGL K L A σ))^[i] δ)).map (MulAut.conj G) := by
    rw [List.map_map]
    congr 1
    funext i
    rw [Function.comp_apply, MulAut.conj_apply, hiter]
  rw [hmap, ← map_list_prod, MulAut.conj_apply]

end T2

section Weyl

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit L in
theorem adelicWeyl_val :
    ((AutomorphicForm.adelicWeyl (𝓞 K) K : GL (Fin 2) (AdeleRing (𝓞 K) K)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) =
      !![0, 1; 1, 0] :=
  map_weyl (algebraMap K (AdeleRing (𝓞 K) K)) AutomorphicForm.gl2Weyl AutomorphicForm.gl2Weyl_val

omit L in
theorem glArch_adelicWeyl_val :
    ((AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) : GL (Fin 2) (InfiniteAdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) = !![0, 1; 1, 0] :=
  map_weyl _ _ (adelicWeyl_val K)

omit L in
theorem finComponent_adelicWeyl_val (v : HeightOneSpectrum (𝓞 K)) :
    ((AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) :
      GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; 1, 0] := by
  have h1 := map_weyl (AdelicLevel.adeleFin (𝓞 K) K) _ (adelicWeyl_val K)
  exact map_weyl _ _ h1

theorem toTensorGL_glArch_adelicWeyl_val :
    ((AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
      Matrix (Fin 2) (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) = !![0, 1; 1, 0] :=
  map_weyl _ _ (glArch_adelicWeyl_val K)

theorem toTensorGL_finComponent_adelicWeyl_val (v : HeightOneSpectrum (𝓞 K)) :
    ((AutomorphicForm.toTensorGL K L (v.adicCompletion K)
        (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) :
        GL (Fin 2) (L ⊗[K] v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (L ⊗[K] v.adicCompletion K)) = !![0, 1; 1, 0] :=
  map_weyl _ _ (finComponent_adelicWeyl_val K v)

theorem archIdentGL_toTensorGL_glArch_adelicWeyl :
    AutomorphicForm.archIdentGL K L (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) =
      AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) := by
  apply Units.ext
  have h1 : ((AutomorphicForm.archIdentGL K L (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K)
        (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) : GL (Fin 2) (InfiniteAdeleRing L)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) = !![0, 1; 1, 0] :=
    map_weyl (AutomorphicForm.archIdent K L) _ (toTensorGL_glArch_adelicWeyl_val K L)
  rw [h1, glArch_adelicWeyl_val L]

theorem archWeight_toTensorGL_adelicWeyl_mul (y : GL (Fin 2) (L ⊗[K] InfiniteAdeleRing K)) :
    (-Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L
          (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * y)))
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
            (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) *
              AutomorphicForm.archIdentGL K L
                (AutomorphicForm.toTensorGL K L (InfiniteAdeleRing K) (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) * y)))) =
      (-Real.log (AutomorphicForm.WindowedSiegel.archHeight L (AutomorphicForm.archIdentGL K L y))
        - Real.log (AutomorphicForm.WindowedSiegel.archHeight L
            (AdelicLevel.glArch (𝓞 L) L (AutomorphicForm.adelicWeyl (𝓞 L) L) * AutomorphicForm.archIdentGL K L y))) := by
  rw [map_mul, archIdentGL_toTensorGL_glArch_adelicWeyl, ← mul_assoc,
    weyl_mul_self _ (glArch_adelicWeyl_val L), one_mul]
  ring

theorem semiLocalWeight_toTensorGL_weyl_mul (v : HeightOneSpectrum (𝓞 K)) (x : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.semiLocalWeight K L v
        (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * x) =
      AutomorphicForm.semiLocalWeight K L v x := by
  unfold AutomorphicForm.semiLocalWeight
  congr 1
  funext w
  rw [map_mul]
  exact weight_weyl_mul _ (map_weyl _ _ (toTensorGL_finComponent_adelicWeyl_val K L v)) _

theorem conj_mem_semiLocalIntegralSet_iff (v : HeightOneSpectrum (𝓞 K)) (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) :
    AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))) * t *
        (AutomorphicForm.toTensorGL K L (v.adicCompletion K)
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))))⁻¹ ∈
        AutomorphicForm.semiLocalIntegralSet K L v ↔
      t ∈ AutomorphicForm.semiLocalIntegralSet K L v :=
  conj_mem_integralUnitsSet_iff _ _ _ (toTensorGL_finComponent_adelicWeyl_val K L v)

end Weyl

section T3

theorem isNormOf_conj (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (g γ : GL (Fin 2) A) (δ : GL (Fin 2) (L ⊗[K] A))
    (h : AutomorphicForm.IsNormOf K L A σ γ δ) : AutomorphicForm.IsNormOf K L A σ (g * γ * g⁻¹) δ := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y * (AutomorphicForm.toTensorGL K L A g)⁻¹, ?_⟩
  unfold AutomorphicForm.IsNormConjugator at hy ⊢
  rw [map_mul, map_mul, map_inv, hy, mul_inv_rev, inv_inv]
  group

theorem exists_isNormOf_conj_iff (K L : Type) [Field K] [Field L] [Algebra K L] (A : Type) [CommRing A] [Algebra K A]
    (σ : L ≃ₐ[K] L) (g γ : GL (Fin 2) A) :
    (∃ δ, AutomorphicForm.IsNormOf K L A σ (g * γ * g⁻¹) δ) ↔ (∃ δ, AutomorphicForm.IsNormOf K L A σ γ δ) := by
  constructor
  · rintro ⟨δ, h⟩
    refine ⟨δ, ?_⟩
    have := isNormOf_conj K L A σ g⁻¹ _ δ h
    simpa [mul_assoc] using this
  · rintro ⟨δ, h⟩
    exact ⟨δ, isNormOf_conj K L A σ g γ δ h⟩

end T3

end E8A.TW

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)
open scoped TensorProduct TensorProduct.RightActions

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (σ : L ≃ₐ[K] L) (u : Kˣ) (z : (AdeleRing (𝓞 K) K)ˣ) :
    ((∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) δ) ↔
      (∃ δ, AutomorphicForm.IsNormOf K L (InfiniteAdeleRing K) σ (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) δ)) ∧
    (∀ v : HeightOneSpectrum (𝓞 K),
      (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))) δ) ↔
      (∃ δ, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) * diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1))) δ)) := by
  have e := E8A.TW.gamma_inv_eq_conj K u z
  constructor
  · have h1 : AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K
          (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1) =
        AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K) *
          AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z *
            diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1) *
          (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))⁻¹ := by
      rw [e, map_mul, map_mul, map_inv]
    rw [h1]
    exact (E8A.TW.exists_isNormOf_conj_iff K L (InfiniteAdeleRing K) σ
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K))
      (AdelicLevel.glArch (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1))).symm
  · intro v
    have h2 : AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K
          (z * Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) *
          diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u⁻¹) 1)) =
        AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)) *
          AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z *
            diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)) *
          (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))⁻¹ := by
      rw [e, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
    rw [h2]
    exact (E8A.TW.exists_isNormOf_conj_iff K L (v.adicCompletion K) σ
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.adelicWeyl (𝓞 K) K)))
      (AdelicLevel.finComponent (𝓞 K) K v (AdelicLevel.glFin (𝓞 K) K (AutomorphicForm.centralScalar (𝓞 K) K z *
        diagUnits2 (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) u) 1)))).symm

end S_AutomorphicForm_exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv
end P2MW
export P2MW.S_AutomorphicForm_exists_isNormOf_glArch_centralScalar_mul_diagUnits2_iff_inv_and_finComponent_iff_inv (solution)
