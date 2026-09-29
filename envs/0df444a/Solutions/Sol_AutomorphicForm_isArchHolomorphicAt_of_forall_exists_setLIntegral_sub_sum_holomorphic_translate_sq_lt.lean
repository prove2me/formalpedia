-- Prove2me | solution 1 for AutomorphicForm.isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/cba76961-17e9-53b4-81f0-f9bdf0766c8d

import Mathlib
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Theorems.Thm_AutomorphicForm_exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
import Theorems.Thm_AutomorphicForm_ArchWeightOne_central_eq_coe_of_forall_mdifferentiable
import Theorems.Thm_AutomorphicForm_ArchWeightOne_intervalIntegral_exp_neg_mul_translate_rotation_eq
import Theorems.Thm_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
namespace P2MW.S_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal Manifold Pointwise

noncomputable section

namespace FamilyRigiditySol

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion Matrix

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal)

abbrev eR : w.Completion ≃+* ℝ := ringEquivRealOfIsReal hw

abbrev toW : GL (Fin 2) ℝ →* GL (Fin 2) w.Completion :=
  Matrix.GeneralLinearGroup.map (eR hw).symm.toRingHom

def iotaR : GL (Fin 2) ℝ →* AdelicGL2 (𝓞 K) K :=
  (adelicArchGLInclAt K w).comp (toW hw)

theorem iotaR_apply (m : GL (Fin 2) ℝ) : iotaR hw m = adelicArchGLInclAt K w (toW hw m) := rfl

omit [NumberField K] in
theorem toW_apply (m : GL (Fin 2) ℝ) (i j : Fin 2) :
    (toW hw m : Matrix (Fin 2) (Fin 2) w.Completion) i j = (eR hw).symm (m i j) := rfl

theorem incl_fst (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      i j).1 = archMatrixUpdate K w (k : Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl

theorem incl_snd (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      i j).2 = (1 : Matrix (Fin 2) (Fin 2) _) i j := rfl

theorem incl_fst_self (k : GL (Fin 2) w.Completion) (i j : Fin 2) :
    (((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      i j).1 w = (k : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  rw [incl_fst, archMatrixUpdate_apply_self]

theorem incl_fst_of_ne (k : GL (Fin 2) w.Completion) (i j : Fin 2) {v : InfinitePlace K}
    (hv : v ≠ w) :
    (((adelicArchGLInclAt K w k : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))
      i j).1 v = (1 : Matrix (Fin 2) (Fin 2) v.Completion) i j := by
  rw [incl_fst, archMatrixUpdate_apply_of_ne _ _ _ _ _ hv]

theorem norm_eR_symm (x : ℝ) : ‖(eR hw).symm x‖ = ‖x‖ := by
  rw [← norm_ringEquivRealOfIsReal hw ((eR hw).symm x), RingEquiv.apply_symm_apply]

theorem continuous_eR_symm : Continuous (eR hw).symm :=
  (AddMonoidHomClass.isometry_of_norm ((eR hw).symm) (norm_eR_symm hw)).continuous

theorem continuous_eR : Continuous (eR hw) :=
  (AddMonoidHomClass.isometry_of_norm (eR hw) (norm_ringEquivRealOfIsReal hw)).continuous

theorem continuous_incl : Continuous (adelicArchGLInclAt K w) := by
  have hval : ∀ (f : GL (Fin 2) w.Completion → GL (Fin 2) w.Completion), Continuous f →
      Continuous (fun k => ((adelicArchGLInclAt K w (f k) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K))) := by
    intro f hf
    refine continuous_pi fun i => continuous_pi fun j => ?_
    have h1 : Continuous fun k => (((adelicArchGLInclAt K w (f k) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 := by
      refine continuous_pi fun v => ?_
      by_cases hv : v = w
      · subst hv
        simp_rw [incl_fst_self]
        exact (Units.continuous_val.comp hf).matrix_elem i j
      · simp_rw [incl_fst_of_ne _ _ _ hv]
        exact continuous_const
    have h2 : Continuous fun k => (((adelicArchGLInclAt K w (f k) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 := by
      simp_rw [incl_snd]; exact continuous_const
    have : (fun k => ((adelicArchGLInclAt K w (f k) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j)
        = fun k => ((((adelicArchGLInclAt K w (f k) : AdelicGL2 (𝓞 K) K) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1,
          (((adelicArchGLInclAt K w (f k) : AdelicGL2 (𝓞 K) K) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2) := rfl
    rw [this]
    exact h1.prodMk h2
  refine Units.continuous_iff.mpr ⟨hval id continuous_id, ?_⟩
  have : (fun k => (((adelicArchGLInclAt K w k)⁻¹ : AdelicGL2 (𝓞 K) K) :
      Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)))
      = fun k => ((adelicArchGLInclAt K w k⁻¹ : AdelicGL2 (𝓞 K) K) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) := by
    funext k; rw [map_inv]
  rw [this]
  exact hval _ continuous_inv

theorem continuous_toW : Continuous (toW hw) :=
  Continuous.units_map _ ((continuous_id.matrix_map (continuous_eR_symm hw)) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) ℝ => m.map (eR hw).symm.toRingHom)

theorem continuous_iotaR : Continuous (iotaR hw) :=
  continuous_incl.comp (continuous_toW hw)

abbrev rotAB (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
    (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
        exact one_ne_zero)

theorem rotAB_mem (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) : rotAB a b hab ∈ rowIsometrySubgroup₀ ℝ := by
  rw [mem_rowIsometrySubgroup₀_iff]
  have hdet : ((rotAB a b hab : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    show Matrix.det !![a, b; -b, a] = 1
    rw [Matrix.det_fin_two_of]; nlinarith [hab]
  refine ⟨hdet, ?_, ?_⟩
  · rw [hdet, norm_one]
  · intro x y
    show ‖x * a + y * -b‖ ^ 2 + ‖x * b + y * a‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [hab]

theorem toW_rotAB_mem (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    toW hw (rotAB a b hab) ∈ rowIsometrySubgroup₀ w.Completion := by
  have h := map_mem_rowIsometrySubgroup₀_of_normPreserving (eR hw).symm (norm_eR_symm hw)
    (rotAB a b hab) (rotAB_mem a b hab)
  have heq : glEquivOfRingEquiv (eR hw).symm (rotAB a b hab) = toW hw (rotAB a b hab) := by
    apply Units.ext; ext i j; rfl
  rwa [heq] at h

theorem archWeightOneAt_toW_rotAB (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((archWeightOneAt hw ⟨toW hw (rotAB a b hab), toW_rotAB_mem hw a b hab⟩ : ℂˣ) : ℂ)
      = ⟨a, b⟩ := by
  show firstRowℂ _ = _
  simp only [firstRowℂ, rowIsometrySubgroup₀Map, MonoidHom.coe_mk, OneHom.coe_mk,
    glEquivOfRingEquiv_apply_entry]
  apply Complex.ext
  · show (eR hw) ((toW hw (rotAB a b hab) : Matrix (Fin 2) (Fin 2) w.Completion) 0 0) = a
    rw [toW_apply, RingEquiv.apply_symm_apply]; rfl
  · show (eR hw) ((toW hw (rotAB a b hab) : Matrix (Fin 2) (Fin 2) w.Completion) 0 1) = b
    rw [toW_apply, RingEquiv.apply_symm_apply]; rfl

open scoped Classical in

def archIdele : (w.Completion)ˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (((MonoidHom.inl (InfiniteAdeleRing K) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K))).comp
    (MonoidHom.mulSingle (fun v : InfinitePlace K => v.Completion) w))

theorem centralScalar_val (u : (AdeleRing (𝓞 K) K)ˣ) (i j : Fin 2) :
    ((centralScalar (𝓞 K) K u : AdelicGL2 (𝓞 K) K) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j
      = if i = j then (u : AdeleRing (𝓞 K) K) else 0 := by
  show Matrix.diagonal (fun _ => (u : AdeleRing (𝓞 K) K)) i j = _
  rw [Matrix.diagonal_apply]

open scoped Classical in
theorem archIdele_fst_self (x : (w.Completion)ˣ) :
    ((archIdele (K := K) x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 w = x := by
  show Pi.mulSingle (M := fun v : InfinitePlace K => v.Completion) w (x : w.Completion) w = x
  exact Pi.mulSingle_eq_same _ _

open scoped Classical in
theorem archIdele_fst_of_ne (x : (w.Completion)ˣ) {v : InfinitePlace K} (hv : v ≠ w) :
    ((archIdele (K := K) x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 v = 1 := by
  show Pi.mulSingle (M := fun v : InfinitePlace K => v.Completion) w (x : w.Completion) v = 1
  exact Pi.mulSingle_eq_of_ne hv _

theorem archIdele_snd (x : (w.Completion)ˣ) :
    ((archIdele (K := K) x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 = 1 := rfl

theorem incl_scalar (x : (w.Completion)ˣ) :
    adelicArchGLInclAt K w (Matrix.GeneralLinearGroup.scalar (Fin 2) x)
      = centralScalar (𝓞 K) K (archIdele (K := K) x) := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  ·
    funext v
    rw [show ((((centralScalar (𝓞 K) K (archIdele (K := K) x)) : AdelicGL2 (𝓞 K) K) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 v
        = (if i = j then ((archIdele (K := K) x : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)
            else 0).1 v by rw [centralScalar_val]]
    by_cases hv : v = w
    · subst hv
      rw [incl_fst_self]
      show Matrix.diagonal (fun _ => (x : v.Completion)) i j = _
      by_cases hij : i = j
      · subst hij; rw [Matrix.diagonal_apply_eq, if_pos rfl, archIdele_fst_self]
      · rw [Matrix.diagonal_apply_ne _ hij, if_neg hij]; rfl
    · rw [incl_fst_of_ne _ _ _ hv]
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq, if_pos rfl, archIdele_fst_of_ne _ hv]
      · rw [Matrix.one_apply_ne hij, if_neg hij]; rfl
  ·
    rw [incl_snd, centralScalar_val]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, if_pos rfl, archIdele_snd]
    · rw [Matrix.one_apply_ne hij, if_neg hij]; rfl

theorem centralScalar_comm (u : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K) :
    g * centralScalar (𝓞 K) K u = centralScalar (𝓞 K) K u * g := by
  apply Units.ext
  show (g : Matrix _ _ _) * Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K)
    = Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) * (g : Matrix _ _ _)
  exact ((Matrix.scalar_commute (u : AdeleRing (𝓞 K) K) (fun r => Commute.all _ r) _).eq).symm

theorem archComponent_glArch_apply (h : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    (archComponent K w (glArch (𝓞 K) K h) : Matrix (Fin 2) (Fin 2) w.Completion) i j
      = ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w := rfl

theorem adele_fst_add (x y : AdeleRing (𝓞 K) K) : (x + y).1 = x.1 + y.1 := rfl
theorem adele_fst_mul (x y : AdeleRing (𝓞 K) K) : (x * y).1 = x.1 * y.1 := rfl
theorem adele_snd_add (x y : AdeleRing (𝓞 K) K) : (x + y).2 = x.2 + y.2 := rfl
theorem adele_snd_mul (x y : AdeleRing (𝓞 K) K) : (x * y).2 = x.2 * y.2 := rfl
theorem infAdele_add_apply (x y : InfiniteAdeleRing K) (v : InfinitePlace K) :
    (x + y) v = x v + y v := rfl
theorem infAdele_mul_apply (x y : InfiniteAdeleRing K) (v : InfinitePlace K) :
    (x * y) v = x v * y v := rfl

theorem incl_comm_of_archComponent_eq_one (h : AdelicGL2 (𝓞 K) K)
    (hh : archComponent K w (glArch (𝓞 K) K h) = 1) (k : GL (Fin 2) w.Completion) :
    h * adelicArchGLInclAt K w k = adelicArchGLInclAt K w k * h := by
  have hh' : ∀ i j : Fin 2, ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).1 w
      = (1 : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
    intro i j
    rw [← archComponent_glArch_apply, hh]; rfl
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · funext v
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, adele_fst_add, adele_fst_mul,
      infAdele_add_apply, infAdele_mul_apply]
    by_cases hv : v = w
    · subst hv
      simp only [incl_fst_self, hh']
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
    · simp only [incl_fst_of_ne _ _ _ hv]
      fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]
  · simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, adele_snd_add, adele_snd_mul,
      incl_snd]
    fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

def wComp (h : AdelicGL2 (𝓞 K) K) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.map (eR hw).toRingHom (archComponent K w (glArch (𝓞 K) K h))

def flat (h : AdelicGL2 (𝓞 K) K) : AdelicGL2 (𝓞 K) K := h * (iotaR hw (wComp hw h))⁻¹

theorem toW_map_eR (a : GL (Fin 2) w.Completion) :
    toW hw (Matrix.GeneralLinearGroup.map (eR hw).toRingHom a) = a := by
  apply Units.ext; ext i j
  exact (eR hw).symm_apply_apply _

theorem wComp_iotaR (m : GL (Fin 2) ℝ) : wComp hw (iotaR hw m) = m := by
  unfold wComp
  rw [iotaR_apply, show adelicArchGLInclAt K w (toW hw m)
      = adelicArchGLIncl K (archGLIncl K w (toW hw m)) from rfl,
    glArch_adelicArchGLIncl, archComponent_archGLIncl_self]
  apply Units.ext; ext i j
  simp [Matrix.GeneralLinearGroup.map, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem archComponent_glArch_iotaR (m : GL (Fin 2) ℝ) :
    archComponent K w (glArch (𝓞 K) K (iotaR hw m)) = toW hw m := by
  rw [iotaR_apply, show adelicArchGLInclAt K w (toW hw m)
      = adelicArchGLIncl K (archGLIncl K w (toW hw m)) from rfl,
    glArch_adelicArchGLIncl, archComponent_archGLIncl_self]

theorem archComponent_glArch_flat (h : AdelicGL2 (𝓞 K) K) :
    archComponent K w (glArch (𝓞 K) K (flat hw h)) = 1 := by
  unfold flat
  rw [map_mul, map_mul, map_inv, map_inv, archComponent_glArch_iotaR]
  unfold wComp
  rw [toW_map_eR, mul_inv_cancel]

theorem flat_mul_iotaR_wComp (h : AdelicGL2 (𝓞 K) K) : flat hw h * iotaR hw (wComp hw h) = h := by
  unfold flat; rw [inv_mul_cancel_right]

theorem flat_comm (h : AdelicGL2 (𝓞 K) K) (m : GL (Fin 2) ℝ) :
    flat hw h * iotaR hw m = iotaR hw m * flat hw h :=
  incl_comm_of_archComponent_eq_one _ (archComponent_glArch_flat hw h) _

theorem continuous_wComp : Continuous (wComp hw) := by
  unfold wComp
  refine (Continuous.units_map _ ?_).comp
    ((continuous_archComponent K w).comp (continuous_glArch (𝓞 K) K))
  exact ((continuous_id.matrix_map (continuous_eR hw)) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) w.Completion => m.map (eR hw).toRingHom)

theorem continuous_flat : Continuous (flat hw) := by
  unfold flat
  exact continuous_id.mul ((continuous_iotaR hw).comp (continuous_wComp hw)).inv

abbrev rot (θ : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]
    (by rw [Matrix.det_fin_two_of, show Real.cos θ * Real.cos θ - Real.sin θ * -Real.sin θ
          = Real.cos θ ^ 2 + Real.sin θ ^ 2 by ring, Real.cos_sq_add_sin_sq]
        exact one_ne_zero)

theorem rot_eq_rotAB (θ : ℝ) : rot θ = rotAB (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ) :=
  rfl

def coeff (h : GL (Fin 2) ℝ) : ℂ :=
  if 0 < ((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) then
      2 * Real.pi * (2 * (((Matrix.GeneralLinearGroup.det h : ℝˣ) : ℝ) : ℂ) /
        (((h 0 0 + h 1 1 : ℝ) : ℂ) + ((h 1 0 - h 0 1 : ℝ) : ℂ) * Complex.I))
    else 0

def fib (φ : AdelicGL2 (𝓞 K) K → ℂ) (A : AdelicGL2 (𝓞 K) K) : GL (Fin 2) ℝ → ℂ :=
  fun m => φ (A * iotaR hw m)

theorem fib_apply (φ : AdelicGL2 (𝓞 K) K → ℂ) (A : AdelicGL2 (𝓞 K) K) (m : GL (Fin 2) ℝ) :
    fib hw φ A m = φ (A * iotaR hw m) := rfl

theorem continuous_fib {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (A : AdelicGL2 (𝓞 K) K) :
    Continuous (fib hw φ A) :=
  hφ.comp (continuous_const.mul (continuous_iotaR hw))

theorem fib_rot {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφw : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ)
    (A : AdelicGL2 (𝓞 K) K) (g : GL (Fin 2) ℝ) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    fib hw φ A (g * Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; -b, a]
        (by rw [Matrix.det_fin_two_of, show a * a - b * -b = a ^ 2 + b ^ 2 by ring, hab]
            exact one_ne_zero)) = (⟨a, b⟩ : ℂ) * fib hw φ A g := by
  have h := hφw ⟨toW hw (rotAB a b hab), toW_rotAB_mem hw a b hab⟩ (A * iotaR hw g)
  rw [archWeightOneAt_toW_rotAB] at h
  simpa [fib, map_mul, mul_assoc, iotaR_apply] using h

def omegaR (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (t : ℝˣ) : ℂ :=
  ((ξ ⟨archIdele (K := K) (Units.map (eR hw).symm.toRingHom.toMonoidHom t), trivial⟩ : ℂˣ) : ℂ)

theorem toW_scalar (t : ℝˣ) :
    toW hw (Matrix.GeneralLinearGroup.scalar (Fin 2) t)
      = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map (eR hw).symm.toRingHom.toMonoidHom t) := by
  apply Units.ext; ext i j
  show (eR hw).symm ((Matrix.scalar (Fin 2) (t : ℝ)) i j) = (Matrix.scalar (Fin 2) _) i j
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.diagonal_apply_ne _ hij]

theorem fib_cen {φ : AdelicGL2 (𝓞 K) K → ℂ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    (hξ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (A : AdelicGL2 (𝓞 K) K) (g : GL (Fin 2) ℝ) (t : ℝˣ) :
    fib hw φ A (g * Matrix.GeneralLinearGroup.scalar (Fin 2) t) = omegaR hw ξ t * fib hw φ A g := by
  simp only [fib, map_mul, iotaR_apply, toW_scalar, incl_scalar, ← mul_assoc]
  rw [centralScalar_comm]
  exact hξ.central_transform ⟨_, trivial⟩ _

theorem fib_hol {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφhol : IsArchHolomorphicAt w hw φ)
    (A : AdelicGL2 (𝓞 K) K) (m : GL (Fin 2) ℝ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * fib hw φ A (m * Matrix.GeneralLinearGroup.mkOfDetNeZero
        !![(z.im : ℝ), (z.re : ℝ); 0, 1] (by simp [Matrix.det_fin_two_of]; exact z.im_ne_zero)) := by
  have h := hφhol (A * iotaR hw m)
  convert h using 2 with z
  simp only [fib, map_mul, mul_assoc]
  rfl

theorem proj_translate {φ : AdelicGL2 (𝓞 K) K → ℂ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    (hφ : Continuous φ) (hξ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ)
    (hφw : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ) (hφhol : IsArchHolomorphicAt w hw φ)
    (x h : AdelicGL2 (𝓞 K) K) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(θ * Complex.I)) * φ (x * iotaR hw (rot θ) * h))
      = coeff (wComp hw h) * φ (x * flat hw h) := by
  by_cases h0 : ∀ y, φ y = 0
  · simp [h0]
  push Not at h0
  obtain ⟨y0, hy0⟩ := h0

  have hω : ∀ t : ℝˣ, 0 < (t : ℝ) → omegaR hw ξ t = ((t : ℝ) : ℂ) := by
    intro t ht
    refine AutomorphicForm.ArchWeightOne.central_eq_coe_of_forall_mdifferentiable
      (fib hw φ y0) (omegaR hw ξ) (fib_rot hw hφw y0) (fun g t _ => fib_cen hw hξ y0 g t)
      (fib_hol hw hφhol y0) ⟨1, ?_⟩ t ht
    simpa [fib] using hy0

  have hint : ∀ θ : ℝ, φ (x * iotaR hw (rot θ) * h)
      = fib hw φ (x * flat hw h) (1 * rot θ * wComp hw h) := by
    intro θ
    rw [fib_apply, one_mul, map_mul]
    conv_lhs => rw [← flat_mul_iotaR_wComp hw h]
    rw [mul_assoc x, ← mul_assoc (iotaR hw (rot θ)), ← flat_comm hw h (rot θ)]
    simp only [mul_assoc]
  simp_rw [hint]
  rw [AutomorphicForm.ArchWeightOne.intervalIntegral_exp_neg_mul_translate_rotation_eq
    (fib hw φ (x * flat hw h)) (continuous_fib hw hφ _) (fib_rot hw hφw _)
    (fun g t ht => by rw [fib_cen hw hξ, hω t ht]) (fib_hol hw hφhol _) (wComp hw h) 1]
  simp [coeff, fib, map_one]

theorem hol_translate_flat {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφhol : IsArchHolomorphicAt w hw φ)
    (g h : AdelicGL2 (𝓞 K) K) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : UpperHalfPlane =>
      ((z.im : ℝ) : ℂ)⁻¹ * φ (g * adelicArchGLInclAt K w
        (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
          (iwasawaSectionGL z)) * flat hw h) := by
  have h1 := hφhol (g * flat hw h)
  convert h1 using 2 with z
  congr 2
  rw [mul_assoc, mul_assoc]
  congr 1
  exact (flat_comm hw h (iwasawaSectionGL z)).symm

section Analysis

variable (K)

local instance instMSgl : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
local instance instBSgl : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
local instance instHaar : (adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

abbrev μK : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

variable {K}

theorem continuous_iwasawaSectionGL : Continuous (fun z : UpperHalfPlane => iwasawaSectionGL z) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j
    · simpa [iwasawaSectionGL] using UpperHalfPlane.continuous_im
    · simpa [iwasawaSectionGL] using UpperHalfPlane.continuous_re
    · simp [iwasawaSectionGL]; exact continuous_const
    · simp [iwasawaSectionGL]; exact continuous_const
  · have hinv : ∀ z : UpperHalfPlane, (((iwasawaSectionGL z)⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
        = !![(z.im : ℝ)⁻¹, -(z.re : ℝ) * (z.im : ℝ)⁻¹; 0, 1] := by
      intro z
      have hdet : (!![(z.im : ℝ), (z.re : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ).det = z.im := by
        simp [Matrix.det_fin_two_of]
      rw [Matrix.coe_units_inv]
      show (!![(z.im : ℝ), (z.re : ℝ); 0, 1] : Matrix (Fin 2) (Fin 2) ℝ)⁻¹ = _
      rw [Matrix.inv_def, hdet, Matrix.adjugate_fin_two_of, Ring.inverse_eq_inv']
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply] <;> field_simp
    simp_rw [hinv]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j
    · have h__af := (UpperHalfPlane.continuous_im.inv₀ (fun z => z.im_ne_zero))
      simp at h__af ⊢
      exact h__af
    · simp
      exact ((UpperHalfPlane.continuous_re.mul
        (UpperHalfPlane.continuous_im.inv₀ (fun z => z.im_ne_zero))).neg)
    · simp; exact continuous_const
    · simp; exact continuous_const

theorem continuous_coeff : Continuous coeff := by
  have hdet : Continuous fun m : GL (Fin 2) ℝ => ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) :=
    (Units.continuous_val.matrix_det : Continuous fun m : GL (Fin 2) ℝ =>
      (m : Matrix (Fin 2) (Fin 2) ℝ).det)
  have hent : ∀ i j : Fin 2, Continuous fun m : GL (Fin 2) ℝ => (m i j : ℝ) := fun i j =>
    Units.continuous_val.matrix_elem i j
  have hD : Continuous fun m : GL (Fin 2) ℝ =>
      (((m 0 0 + m 1 1 : ℝ) : ℂ) + ((m 1 0 - m 0 1 : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  have hbranch : ∀ m : GL (Fin 2) ℝ, 0 < ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) →
      ContinuousAt (fun m : GL (Fin 2) ℝ =>
        2 * (Real.pi : ℂ) * (2 * (((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) : ℂ) /
          (((m 0 0 + m 1 1 : ℝ) : ℂ) + ((m 1 0 - m 0 1 : ℝ) : ℂ) * Complex.I))) m := by
    intro m hm
    have hne : (((m 0 0 + m 1 1 : ℝ) : ℂ) + ((m 1 0 - m 0 1 : ℝ) : ℂ) * Complex.I) ≠ 0 := by
      intro h0
      have hre := congrArg Complex.re h0
      have him := congrArg Complex.im h0
      simp at hre him
      have hd : ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) = m 0 0 * m 1 1 - m 0 1 * m 1 0 := by
        show (m : Matrix (Fin 2) (Fin 2) ℝ).det = _
        rw [Matrix.det_fin_two]
      rw [hd] at hm
      have h1 : (m 1 1 : ℝ) = -(m 0 0 : ℝ) := by linarith
      have h2 : (m 1 0 : ℝ) = (m 0 1 : ℝ) := by linarith
      rw [h1, h2] at hm
      nlinarith [sq_nonneg (m 0 0 : ℝ), sq_nonneg (m 0 1 : ℝ)]
    have hnum : Continuous fun m : GL (Fin 2) ℝ =>
        (2 * (((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp hdet)
    exact continuousAt_const.mul ((hnum.continuousAt).div hD.continuousAt hne)
  rw [continuous_iff_continuousAt]
  intro m
  by_cases hm : 0 < ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ)
  · have hopen : IsOpen {m : GL (Fin 2) ℝ | 0 < ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ)} :=
      isOpen_lt continuous_const hdet
    refine (hbranch m hm).congr ?_
    filter_upwards [hopen.mem_nhds hm] with m' hm'
    simp only [coeff]
    rw [if_pos hm']
  · have hne : ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) ≠ 0 := Units.ne_zero _
    have hlt : ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) < 0 := lt_of_le_of_ne (not_lt.mp hm) hne
    have hopen : IsOpen {m : GL (Fin 2) ℝ | ((Matrix.GeneralLinearGroup.det m : ℝˣ) : ℝ) < 0} :=
      isOpen_lt hdet continuous_const
    refine (continuousAt_const (y := (0 : ℂ))).congr ?_
    filter_upwards [hopen.mem_nhds hlt] with m' hm'
    simp only [coeff]
    rw [if_neg (not_lt.mpr (le_of_lt hm'))]

def Pint (f : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(θ * Complex.I)) * f (x * iotaR hw (rot θ))

theorem norm_exp_neg_mul_I (θ : ℝ) : ‖Complex.exp (-(θ * Complex.I))‖ = 1 := by
  rw [show -((θ : ℂ) * Complex.I) = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem continuous_rot : Continuous rot := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · have hinv : ∀ θ : ℝ, ((rot θ)⁻¹ : GL (Fin 2) ℝ) = rot (-θ) := by
      intro θ
      rw [inv_eq_iff_mul_eq_one]
      apply Units.ext
      show (!![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ] : Matrix (Fin 2) (Fin 2) ℝ) *
        !![Real.cos (-θ), Real.sin (-θ); -Real.sin (-θ), Real.cos (-θ)] = 1
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Real.cos_neg, Real.sin_neg] <;>
        nlinarith [Real.cos_sq_add_sin_sq θ]
    simp_rw [hinv]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem Pint_of_weightOne {f : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : HasArchCharacterAt₀ K w (archWeightOneAt hw) f) (x : AdelicGL2 (𝓞 K) K) :
    Pint hw f x = (2 * Real.pi : ℂ) * f x := by
  unfold Pint
  have hint : ∀ θ : ℝ, Complex.exp (-(θ * Complex.I)) * f (x * iotaR hw (rot θ)) = f x := by
    intro θ
    have h := fib_rot hw hf x 1 (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ)
    simp only [fib, one_mul, map_one, mul_one] at h
    rw [show rot θ = rotAB (Real.cos θ) (Real.sin θ) (Real.cos_sq_add_sin_sq θ) from rfl, h,
      ← mul_assoc]
    have : Complex.exp (-(θ * Complex.I)) * (⟨Real.cos θ, Real.sin θ⟩ : ℂ) = 1 := by
      rw [show (⟨Real.cos θ, Real.sin θ⟩ : ℂ) = Complex.exp (θ * Complex.I) by
        apply Complex.ext <;> simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]]
      rw [← Complex.exp_add]; simp
    rw [this, one_mul]
  simp_rw [hint]
  rw [intervalIntegral.integral_const]
  simp

theorem norm_Pint_le {f : AdelicGL2 (𝓞 K) K → ℂ} {x : AdelicGL2 (𝓞 K) K} {ε : ℝ}
    (h : ∀ θ : ℝ, θ ∈ Set.Icc 0 (2 * Real.pi) → ‖f (x * iotaR hw (rot θ))‖ ≤ ε) :
    ‖Pint hw f x‖ ≤ ε * (2 * Real.pi) := by
  unfold Pint
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (C := ε) (f := fun θ => Complex.exp (-(θ * Complex.I)) * f (x * iotaR hw (rot θ))) ?_
  · simpa [abs_of_nonneg h2π] using this
  intro θ hθ
  rw [Set.uIoc_of_le h2π] at hθ
  rw [norm_mul, norm_exp_neg_mul_I, one_mul]
  exact h θ ⟨hθ.1.le, hθ.2⟩

theorem Pint_sub {f g : AdelicGL2 (𝓞 K) K → ℂ} {x : AdelicGL2 (𝓞 K) K}
    (hf : Continuous fun θ : ℝ => f (x * iotaR hw (rot θ)))
    (hg : Continuous fun θ : ℝ => g (x * iotaR hw (rot θ))) :
    Pint hw (f - g) x = Pint hw f x - Pint hw g x := by
  unfold Pint
  rw [← intervalIntegral.integral_sub]
  · simp [mul_sub]
  · exact ((Complex.continuous_exp.comp (by fun_prop)).mul hf).intervalIntegrable _ _
  · exact ((Complex.continuous_exp.comp (by fun_prop)).mul hg).intervalIntegrable _ _

variable (K) in

def conv (V₀ : Set (AdelicGL2 (𝓞 K) K)) (f : AdelicGL2 (𝓞 K) K → ℂ) (α : AdelicGL2 (𝓞 K) K → ℝ)
    (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∫ y in V₀, f (x * y) * (α y : ℂ) ∂μK K

theorem conv_sub {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : IsCompact V₀) {f g : AdelicGL2 (𝓞 K) K → ℂ}
    (hf : Continuous f) (hg : Continuous g) {α : AdelicGL2 (𝓞 K) K → ℝ} (hα : Continuous α)
    (x : AdelicGL2 (𝓞 K) K) :
    conv K V₀ (f - g) α x = conv K V₀ f α x - conv K V₀ g α x := by
  unfold conv
  rw [← integral_sub]
  · simp [sub_mul]
  · exact ((hf.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_ofReal.comp hα)).continuousOn.integrableOn_compact hV₀
  · exact ((hg.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_ofReal.comp hα)).continuousOn.integrableOn_compact hV₀

theorem enorm_conv_le {V₀ C : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : IsCompact V₀) (hC : IsCompact C)
    {F : AdelicGL2 (𝓞 K) K → ℂ} (hF : Continuous F) {α : AdelicGL2 (𝓞 K) K → ℝ} (hα : Continuous α)
    {x : AdelicGL2 (𝓞 K) K} (hx : x ∈ C) :
    ‖conv K V₀ F α x‖ₑ ≤
      (∫⁻ y in C * V₀, ‖F y‖ₑ ^ (2 : ℝ) ∂μK K) ^ (1 / 2 : ℝ) *
        (∫⁻ y in V₀, ‖(α y : ℂ)‖ₑ ^ (2 : ℝ) ∂μK K) ^ (1 / 2 : ℝ) := by
  have hV₀m : MeasurableSet V₀ := hV₀.isClosed.measurableSet
  have hCVm : MeasurableSet (C * V₀) := (hC.mul hV₀).isClosed.measurableSet
  have hFm : AEMeasurable (fun y => ‖F (x * y)‖ₑ) ((μK K).restrict V₀) :=
    (hF.comp (continuous_const.mul continuous_id)).enorm.aemeasurable
  have hαm : AEMeasurable (fun y => ‖(α y : ℂ)‖ₑ) ((μK K).restrict V₀) :=
    (Complex.continuous_ofReal.comp hα).enorm.aemeasurable
  calc ‖conv K V₀ F α x‖ₑ
      ≤ ∫⁻ y in V₀, ‖F (x * y) * (α y : ℂ)‖ₑ ∂μK K := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y in V₀, ((fun y => ‖F (x * y)‖ₑ) * (fun y => ‖(α y : ℂ)‖ₑ)) y ∂μK K := by
        simp_rw [Pi.mul_apply, enorm_mul]
    _ ≤ (∫⁻ y in V₀, ‖F (x * y)‖ₑ ^ (2 : ℝ) ∂μK K) ^ (1 / 2 : ℝ) *
          (∫⁻ y in V₀, ‖(α y : ℂ)‖ₑ ^ (2 : ℝ) ∂μK K) ^ (1 / 2 : ℝ) := by
        have := ENNReal.lintegral_mul_le_Lp_mul_Lq ((μK K).restrict V₀)
          Real.HolderConjugate.two_two hFm hαm
        simpa using this
    _ ≤ _ := by
        refine mul_le_mul_left (ENNReal.rpow_le_rpow ?_ (by norm_num)) _

        calc ∫⁻ y in V₀, ‖F (x * y)‖ₑ ^ (2 : ℝ) ∂μK K
            = ∫⁻ y, V₀.indicator (fun y => ‖F (x * y)‖ₑ ^ (2 : ℝ)) y ∂μK K :=
              (lintegral_indicator hV₀m _).symm
          _ ≤ ∫⁻ y, (C * V₀).indicator (fun y => ‖F y‖ₑ ^ (2 : ℝ)) (x * y) ∂μK K := by
              refine lintegral_mono fun y => ?_
              by_cases hy : y ∈ V₀
              · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Set.mul_mem_mul hx hy)]
              · rw [Set.indicator_of_notMem hy]; exact zero_le
          _ = ∫⁻ y, (C * V₀).indicator (fun y => ‖F y‖ₑ ^ (2 : ℝ)) y ∂μK K :=
              lintegral_mul_left_eq_self _ x
          _ = ∫⁻ y in C * V₀, ‖F y‖ₑ ^ (2 : ℝ) ∂μK K := lintegral_indicator hCVm _

theorem exists_nhds_norm_conv_sub_le {V₀ C : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : IsCompact V₀)
    (hC : IsCompact C) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ V ∈ nhds (1 : AdelicGL2 (𝓞 K) K), ∀ α : AdelicGL2 (𝓞 K) K → ℝ, Continuous α → (∀ y, 0 ≤ α y) →
      (∀ y ∉ V, α y = 0) → (∀ y ∉ V₀, α y = 0) → ∫ y in V₀, α y ∂μK K = 1 →
        ∀ x ∈ C, ‖conv K V₀ f α x - f x‖ ≤ ε := by

  obtain ⟨u, v, hu, hv, hCu, h1v, huv⟩ := generalized_tube_lemma hC (isCompact_singleton (x := (1 :
    AdelicGL2 (𝓞 K) K))) (n := {p : AdelicGL2 (𝓞 K) K × AdelicGL2 (𝓞 K) K | ‖f (p.1 * p.2) - f p.1‖ < ε})
    (isOpen_lt ((hf.comp continuous_mul).sub (hf.comp continuous_fst)).norm continuous_const)
    (by rintro ⟨x, y⟩ ⟨hx, hy⟩; simp only [Set.mem_singleton_iff] at hy; subst hy; simpa using hε)
  refine ⟨v, hv.mem_nhds (h1v rfl), fun α hαc hα0 hαv hαV hα1 x hx => ?_⟩
  have hV₀m : MeasurableSet V₀ := hV₀.isClosed.measurableSet
  have hint : IntegrableOn (fun y => f (x * y) * (α y : ℂ)) V₀ (μK K) :=
    ((hf.comp (continuous_const.mul continuous_id)).mul
      (Complex.continuous_ofReal.comp hαc)).continuousOn.integrableOn_compact hV₀
  have hintα : IntegrableOn (fun y => (α y : ℂ)) V₀ (μK K) :=
    (Complex.continuous_ofReal.comp hαc).continuousOn.integrableOn_compact hV₀
  have hintαr : IntegrableOn α V₀ (μK K) := hαc.continuousOn.integrableOn_compact hV₀
  have hfx : f x = ∫ y in V₀, f x * (α y : ℂ) ∂μK K := by
    rw [integral_const_mul]
    have : (∫ y in V₀, (α y : ℂ) ∂μK K) = ((∫ y in V₀, α y ∂μK K : ℝ) : ℂ) := integral_ofReal
    rw [this, hα1]; simp
  have hsub : conv K V₀ f α x - f x = ∫ y in V₀, (f (x * y) - f x) * (α y : ℂ) ∂μK K := by
    simp_rw [sub_mul]
    rw [integral_sub hint (hintα.const_mul _), ← hfx]
    rfl
  rw [hsub]
  calc ‖∫ y in V₀, (f (x * y) - f x) * (α y : ℂ) ∂μK K‖
      ≤ ∫ y in V₀, ε * α y ∂μK K := by
        refine norm_integral_le_of_norm_le (hintαr.const_mul ε) ?_
        filter_upwards [ae_restrict_mem hV₀m] with y hy
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hα0 y)]
        by_cases hyv : y ∈ v
        · have : (x, y) ∈ u ×ˢ v := ⟨hCu hx, hyv⟩
          have := huv this
          simp only [Set.mem_setOf_eq] at this
          exact mul_le_mul_of_nonneg_right this.le (hα0 y)
        · rw [hαv y hyv]; simp
    _ = ε := by rw [integral_const_mul, hα1, mul_one]

theorem continuous_conv_rot {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : IsCompact V₀)
    {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) {α : AdelicGL2 (𝓞 K) K → ℝ} (hα : Continuous α)
    (x : AdelicGL2 (𝓞 K) K) :
    Continuous fun θ : ℝ => conv K V₀ f α (x * iotaR hw (rot θ)) := by
  unfold conv
  have hc : Continuous (Function.uncurry fun (θ : ℝ) (y : AdelicGL2 (𝓞 K) K) =>
      f (x * iotaR hw (rot θ) * y) * (α y : ℂ)) := by
    apply Continuous.mul
    · exact hf.comp (((continuous_const.mul ((continuous_iotaR hw).comp continuous_rot)).comp
        continuous_fst).mul continuous_snd)
    · exact Complex.continuous_ofReal.comp (hα.comp continuous_snd)
  exact continuous_parametric_integral_of_continuous hc hV₀

theorem Pint_conv_translate {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : IsCompact V₀)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    (hφ : Continuous φ) (hξ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ)
    (hφw : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ) (hφhol : IsArchHolomorphicAt w hw φ)
    {α : AdelicGL2 (𝓞 K) K → ℝ} (hα : Continuous α) (q x : AdelicGL2 (𝓞 K) K) :
    Pint hw (conv K V₀ (fun y => φ (y * q)) α) x
      = ∫ y in V₀, (α y : ℂ) * (coeff (wComp hw (y * q)) * φ (x * flat hw (y * q))) ∂μK K := by
  have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hV₀m : MeasurableSet V₀ := hV₀.isClosed.measurableSet
  haveI : IsFiniteMeasure ((μK K).restrict V₀) := isFiniteMeasure_restrict.mpr hV₀.measure_lt_top.ne
  set f : ℝ → AdelicGL2 (𝓞 K) K → ℂ := fun θ y =>
    Complex.exp (-(θ * Complex.I)) * (φ (x * iotaR hw (rot θ) * y * q) * (α y : ℂ)) with hf
  have hfc : Continuous (Function.uncurry f) := by
    apply Continuous.mul
    · exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul
        continuous_const).neg
    apply Continuous.mul
    · exact hφ.comp ((((continuous_const.mul ((continuous_iotaR hw).comp continuous_rot)).comp
        continuous_fst).mul continuous_snd).mul continuous_const)
    · exact Complex.continuous_ofReal.comp (hα.comp continuous_snd)

  set μ₁ : Measure ℝ := volume.restrict (Set.Ioc 0 (2 * Real.pi)) with hμ₁
  have hint : Integrable (Function.uncurry f) (μ₁.prod ((μK K).restrict V₀)) := by
    obtain ⟨M, hM⟩ := (isCompact_Icc.prod hV₀).exists_bound_of_continuousOn
      (s := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ V₀) hfc.continuousOn
    have hae : ∀ᵐ p ∂(μ₁.prod ((μK K).restrict V₀)), p ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) ×ˢ V₀ := by
      rw [ae_iff]
      have hsub : {p : ℝ × AdelicGL2 (𝓞 K) K | ¬p ∈ Set.Ioc (0 : ℝ) (2 * Real.pi) ×ˢ V₀}
          ⊆ (Set.Ioc (0 : ℝ) (2 * Real.pi))ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ V₀ᶜ := by
        intro p hp
        simp only [Set.mem_prod, not_and_or, Set.mem_setOf_eq] at hp
        rcases hp with hp | hp
        · exact Or.inl ⟨hp, trivial⟩
        · exact Or.inr ⟨trivial, hp⟩
      refine measure_mono_null hsub ?_
      refine le_antisymm ((measure_union_le _ _).trans ?_) bot_le
      rw [Measure.prod_prod, Measure.prod_prod]
      have h1 : μ₁ (Set.Ioc (0 : ℝ) (2 * Real.pi))ᶜ = 0 := by
        rw [hμ₁, Measure.restrict_apply measurableSet_Ioc.compl]; simp
      have h2 : (μK K).restrict V₀ V₀ᶜ = 0 := by
        rw [Measure.restrict_apply hV₀m.compl]; simp
      rw [h1, h2]; simp
    refine Integrable.mono' (integrable_const M) hfc.aestronglyMeasurable ?_
    filter_upwards [hae] with p hp
    exact hM p ⟨Set.Ioc_subset_Icc_self hp.1, hp.2⟩

  have hL : Pint hw (conv K V₀ (fun y => φ (y * q)) α) x
      = ∫ θ, ∫ y, f θ y ∂((μK K).restrict V₀) ∂μ₁ := by
    unfold Pint conv
    rw [intervalIntegral.integral_of_le h2π]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [← integral_const_mul]
  rw [hL, integral_integral_swap hint]
  refine setIntegral_congr_fun hV₀m fun y _ => ?_

  have hP := proj_translate hw hφ hξ hφw hφhol x (y * q)
  rw [hμ₁, ← intervalIntegral.integral_of_le h2π]
  have : (fun θ : ℝ => f θ y) = fun θ : ℝ =>
      (Complex.exp (-(θ * Complex.I)) * φ (x * iotaR hw (rot θ) * (y * q))) * (α y : ℂ) := by
    funext θ; simp only [hf, mul_assoc]
  rw [this, intervalIntegral.integral_mul_const, hP]
  ring

abbrev iotaS (z : UpperHalfPlane) : AdelicGL2 (𝓞 K) K :=
  adelicArchGLInclAt K w (Matrix.GeneralLinearGroup.map (ringEquivRealOfIsReal hw).symm.toRingHom
    (iwasawaSectionGL z))

theorem continuous_iotaS : Continuous (iotaS hw) :=
  (continuous_iotaR hw).comp continuous_iwasawaSectionGL

theorem continuousOn_ofComplex :
    ContinuousOn (fun z : ℂ => UpperHalfPlane.ofComplex z) {z : ℂ | 0 < z.im} :=
  fun _ hz => (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) hz).continuousAt.continuousWithinAt

theorem differentiableOn_slice_integral {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : IsCompact V₀)
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : Continuous φ) (hφhol : IsArchHolomorphicAt w hw φ)
    {α : AdelicGL2 (𝓞 K) K → ℝ} (hα : Continuous α) (hαV : ∀ y ∉ V₀, α y = 0)
    (g q : AdelicGL2 (𝓞 K) K) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ y in V₀, (α y : ℂ) * (coeff (wComp hw (y * q)) *
      ((((UpperHalfPlane.ofComplex z).im : ℝ) : ℂ)⁻¹ *
        φ (g * iotaS hw (UpperHalfPlane.ofComplex z) * flat hw (y * q)))) ∂μK K)
      {z : ℂ | 0 < z.im} := by
  haveI : IsFiniteMeasure ((μK K).restrict V₀) := isFiniteMeasure_restrict.mpr hV₀.measure_lt_top.ne
  refine Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
    ((μK K).restrict V₀) UpperHalfPlane.isOpen_upperHalfPlaneSet hV₀ _ ?_ ?_ ?_
  ·
    have hof : ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => UpperHalfPlane.ofComplex p.1)
        ({z : ℂ | 0 < z.im} ×ˢ Set.univ) :=
      continuousOn_ofComplex.comp continuous_fst.continuousOn (fun p hp => hp.1)
    apply ContinuousOn.mul
    · exact (Complex.continuous_ofReal.comp (hα.comp continuous_snd)).continuousOn
    apply ContinuousOn.mul
    · exact (continuous_coeff.comp ((continuous_wComp hw).comp
        (continuous_snd.mul continuous_const))).continuousOn
    apply ContinuousOn.mul
    · refine ContinuousOn.inv₀ ?_ (fun p _ => ?_)
      · exact Complex.continuous_ofReal.comp_continuousOn (UpperHalfPlane.continuous_im.comp_continuousOn hof)
      · exact_mod_cast (UpperHalfPlane.ofComplex p.1).im_ne_zero
    · refine hφ.comp_continuousOn ?_
      exact ((continuousOn_const.mul ((continuous_iotaS hw).comp_continuousOn hof)).mul
        ((continuous_flat hw).comp (continuous_snd.mul continuous_const)).continuousOn)
  · intro z _ y hy
    simp [hαV y hy]
  · intro y
    refine DifferentiableOn.const_mul (DifferentiableOn.const_mul ?_ _) _
    have h := hol_translate_flat hw hφhol g (y * q)
    rw [UpperHalfPlane.mdifferentiable_iff] at h
    exact h

theorem isLsXi_translate {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (h : AdelicGL2 (𝓞 K) K) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ (fun y => φ (y * h)) :=
  ⟨fun γ g => by simpa [mul_assoc] using hφ.left_invariant γ (g * h),
   fun z g => by simpa [mul_assoc] using hφ.central_transform z (g * h)⟩

theorem isLsXi_sub_sum {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ}
    {φ' : AdelicGL2 (𝓞 K) K → ℂ} {n : ℕ} {ψ : Fin n → AdelicGL2 (𝓞 K) K → ℂ}
    (hψ : ∀ i, IsLsXiFunction (𝓞 K) K ⊤ ξ (ψ i)) (hφ' : IsLsXiFunction (𝓞 K) K ⊤ ξ φ')
    (x : Fin n → AdelicGL2 (𝓞 K) K) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ (fun y => φ' y - ∑ i, ψ i (y * x i)) := by
  refine ⟨fun γ g => ?_, fun z g => ?_⟩
  · simp only [hφ'.left_invariant]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [(isLsXi_translate (hψ i) (x i)).left_invariant]
  · rw [hφ'.central_transform, mul_sub, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by
      rw [(isLsXi_translate (hψ i) (x i)).central_transform]

variable (K) in

def Bump (V₀ : Set (AdelicGL2 (𝓞 K) K)) : Type :=
  {α : AdelicGL2 (𝓞 K) K → ℝ // Continuous α ∧ (∀ y, 0 ≤ α y) ∧ (∀ y ∉ V₀, α y = 0) ∧
    ∫ y in V₀, α y ∂μK K = 1}

theorem exists_bump {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : V₀ ∈ nhds (1 : AdelicGL2 (𝓞 K) K))
    {V : Set (AdelicGL2 (𝓞 K) K)} (hV : V ∈ nhds (1 : AdelicGL2 (𝓞 K) K)) :
    ∃ α : Bump K V₀, ∀ y ∉ V, α.1 y = 0 := by
  haveI := IsTopologicalGroup.regularSpace (AdelicGL2 (𝓞 K) K)
  set W := interior (V ∩ V₀) with hW
  have hW1 : (1 : AdelicGL2 (𝓞 K) K) ∈ W := mem_interior_iff_mem_nhds.mpr (Filter.inter_mem hV hV₀)
  obtain ⟨f, hf1, hf0, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : AdelicGL2 (𝓞 K) K))) isOpen_interior.isClosed_compl
    (Set.disjoint_singleton_left.mpr (fun h => h hW1))
  have hfW : ∀ y ∉ W, f y = 0 := fun y hy => hf0 hy
  have hfV₀ : ∀ y ∉ V₀, f y = 0 := fun y hy => hfW y (fun h => hy (interior_subset h).2)
  have hfV : ∀ y ∉ V, f y = 0 := fun y hy => hfW y (fun h => hy (interior_subset h).1)
  set c : ℝ := ∫ y in V₀, f y ∂μK K with hc
  have hcpos : 0 < c := by
    rw [hc, setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => hfV₀ y hy)]
    exact f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc (fun y => (hf01 y).1)
      (by rw [hf1 rfl]; simp)
  refine ⟨⟨fun y => f y / c, f.continuous.div_const c, fun y => div_nonneg (hf01 y).1 hcpos.le,
    fun y hy => by simp [hfV₀ y hy], ?_⟩, fun y hy => by simp [hfV y hy]⟩
  rw [integral_div, ← hc, div_self hcpos.ne']

variable (K) in

def bumpFilter (V₀ : Set (AdelicGL2 (𝓞 K) K)) : Filter (Bump K V₀) :=
  (nhds (1 : AdelicGL2 (𝓞 K) K)).lift' fun V => {α : Bump K V₀ | ∀ y ∉ V, α.1 y = 0}

theorem bump_mono {V₀ : Set (AdelicGL2 (𝓞 K) K)} :
    Monotone fun V : Set (AdelicGL2 (𝓞 K) K) => {α : Bump K V₀ | ∀ y ∉ V, α.1 y = 0} :=
  fun _ _ hVV' _ hα y hy => hα y (fun h => hy (hVV' h))

theorem bumpFilter_neBot {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : V₀ ∈ nhds (1 : AdelicGL2 (𝓞 K) K)) :
    (bumpFilter K V₀).NeBot :=
  (Filter.lift'_neBot_iff bump_mono).mpr fun _ hV => exists_bump hV₀ hV

theorem eventually_bumpFilter {V₀ : Set (AdelicGL2 (𝓞 K) K)} {p : Bump K V₀ → Prop}
    {V : Set (AdelicGL2 (𝓞 K) K)} (hV : V ∈ nhds (1 : AdelicGL2 (𝓞 K) K))
    (h : ∀ α : Bump K V₀, (∀ y ∉ V, α.1 y = 0) → p α) : ∀ᶠ α in bumpFilter K V₀, p α :=
  (Filter.eventually_lift'_iff bump_mono).mpr ⟨V, hV, fun α hα => h α hα⟩

theorem Pint_conv_sum {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀ : IsCompact V₀)
    {n : ℕ} {ψ : Fin n → AdelicGL2 (𝓞 K) K → ℂ} (hψ : ∀ i, Continuous (ψ i))
    {α : AdelicGL2 (𝓞 K) K → ℝ} (hα : Continuous α)
    (xs : Fin n → AdelicGL2 (𝓞 K) K) (x : AdelicGL2 (𝓞 K) K) :
    Pint hw (conv K V₀ (fun y => ∑ i, ψ i (y * xs i)) α) x
      = ∑ i, Pint hw (conv K V₀ (fun y => ψ i (y * xs i)) α) x := by
  have hconv : ∀ x', conv K V₀ (fun y => ∑ i, ψ i (y * xs i)) α x'
      = ∑ i, conv K V₀ (fun y => ψ i (y * xs i)) α x' := by
    intro x'
    unfold conv
    simp only [Finset.sum_mul]
    rw [integral_finsetSum]
    intro i _
    exact ((hψ i).comp ((continuous_const.mul continuous_id).mul
      continuous_const)).mul (Complex.continuous_ofReal.comp hα) |>.continuousOn.integrableOn_compact hV₀
  unfold Pint
  simp_rw [hconv, Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  intro i _
  refine (Continuous.mul (Complex.continuous_exp.comp (by fun_prop)) ?_).intervalIntegrable _ _
  exact continuous_conv_rot hw hV₀ ((hψ i).comp (continuous_id.mul continuous_const)) hα x

theorem exists_bound_im_inv {Kc : Set ℂ} (hKc : IsCompact Kc) (hKcU : Kc ⊆ {z : ℂ | 0 < z.im}) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ Kc, ‖((((UpperHalfPlane.ofComplex z).im : ℝ) : ℂ))⁻¹‖ ≤ M := by
  have hcont : ContinuousOn (fun z : ℂ => ((((UpperHalfPlane.ofComplex z).im : ℝ) : ℂ))⁻¹) Kc := by
    refine ContinuousOn.inv₀ ?_ (fun z _ => by exact_mod_cast (UpperHalfPlane.ofComplex z).im_ne_zero)
    exact Complex.continuous_ofReal.comp_continuousOn
      (UpperHalfPlane.continuous_im.comp_continuousOn (continuousOn_ofComplex.mono hKcU))
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hcont
  exact ⟨max M 0, le_max_right _ _, fun z hz => (hM z hz).trans (le_max_left _ _)⟩

theorem isCompact_base (g : AdelicGL2 (𝓞 K) K) {Kc : Set ℂ} (hKc : IsCompact Kc)
    (hKcU : Kc ⊆ {z : ℂ | 0 < z.im}) :
    IsCompact ((fun p : ℂ × ℝ => g * iotaS hw (UpperHalfPlane.ofComplex p.1) * iotaR hw (rot p.2)) ''
      (Kc ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) := by
  refine (hKc.prod isCompact_Icc).image_of_continuousOn ?_
  refine ContinuousOn.mul (continuousOn_const.mul ?_) ?_
  · exact (continuous_iotaS hw).comp_continuousOn
      ((continuousOn_ofComplex.mono hKcU).comp continuous_fst.continuousOn (fun p hp => hp.1))
  · exact (((continuous_iotaR hw).comp continuous_rot).comp continuous_snd).continuousOn

theorem norm_slice_sub_le {f₁ f₂ : AdelicGL2 (𝓞 K) K → ℂ} {x : AdelicGL2 (𝓞 K) K}
    (h₁ : Continuous fun θ : ℝ => f₁ (x * iotaR hw (rot θ)))
    (h₂ : Continuous fun θ : ℝ => f₂ (x * iotaR hw (rot θ))) {δ M : ℝ} (c : ℂ) (hc : ‖c‖ ≤ M)
    (hδ : ∀ θ : ℝ, θ ∈ Set.Icc 0 (2 * Real.pi) → ‖f₁ (x * iotaR hw (rot θ)) - f₂ (x * iotaR hw (rot θ))‖ ≤ δ) :
    dist (c * Pint hw f₁ x) (c * Pint hw f₂ x) ≤ M * (δ * (2 * Real.pi)) := by
  rw [dist_eq_norm, ← mul_sub, norm_mul, ← Pint_sub hw h₁ h₂]
  have hP := norm_Pint_le hw (f := f₁ - f₂) (x := x) (ε := δ) (fun θ hθ => by simpa using hδ θ hθ)
  have hδ0 : 0 ≤ δ * (2 * Real.pi) :=
    le_trans (norm_nonneg _) hP
  exact mul_le_mul hc hP (norm_nonneg _) ((norm_nonneg c).trans hc)

def sl (f : AdelicGL2 (𝓞 K) K → ℂ) (g : AdelicGL2 (𝓞 K) K) : ℂ → ℂ := fun z =>
  ((((UpperHalfPlane.ofComplex z).im : ℝ) : ℂ))⁻¹ *
    Pint hw f (g * iotaS hw (UpperHalfPlane.ofComplex z))

theorem isOpen_U : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im

theorem final_arith {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) :
    M * (ε / (2 * (M * (2 * Real.pi) + 1)) * (2 * Real.pi)) < ε := by
  have hpi := Real.pi_pos
  have hden : 0 < 2 * (M * (2 * Real.pi) + 1) := by positivity
  rw [show M * (ε / (2 * (M * (2 * Real.pi) + 1)) * (2 * Real.pi))
      = ε * ((M * (2 * Real.pi)) / (2 * (M * (2 * Real.pi) + 1))) by field_simp]
  have h1 : (M * (2 * Real.pi)) / (2 * (M * (2 * Real.pi) + 1)) < 1 := by
    rw [div_lt_one hden]; nlinarith
  calc ε * ((M * (2 * Real.pi)) / (2 * (M * (2 * Real.pi) + 1))) < ε * 1 :=
        mul_lt_mul_of_pos_left h1 hε
    _ = ε := mul_one ε

theorem tendsto_sl_conv {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀c : IsCompact V₀)
    {φ' : AdelicGL2 (𝓞 K) K → ℂ} (hφ' : Continuous φ') (g : AdelicGL2 (𝓞 K) K) :
    TendstoLocallyUniformlyOn (fun α : Bump K V₀ => sl hw (conv K V₀ φ' α.1) g) (sl hw φ' g)
      (bumpFilter K V₀) {z : ℂ | 0 < z.im} := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_U]
  intro Kc hKcU hKc
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨M, hM0, hM⟩ := exists_bound_im_inv hKc hKcU
  have hC' := isCompact_base hw g hKc hKcU
  set δ := ε / (2 * (M * (2 * Real.pi) + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨V, hV, hVp⟩ := exists_nhds_norm_conv_sub_le hV₀c hC' hφ' hδpos
  refine eventually_bumpFilter hV fun α hαV z hz => ?_
  set x := g * iotaS hw (UpperHalfPlane.ofComplex z) with hx
  have key : ∀ θ : ℝ, θ ∈ Set.Icc 0 (2 * Real.pi) →
      ‖φ' (x * iotaR hw (rot θ)) - conv K V₀ φ' α.1 (x * iotaR hw (rot θ))‖ ≤ δ := by
    intro θ hθ
    rw [norm_sub_rev]
    exact hVp α.1 α.2.1 α.2.2.1 hαV α.2.2.2.1 α.2.2.2.2 _ ⟨(z, θ), ⟨hz, hθ⟩, rfl⟩
  have h₁ : Continuous fun θ : ℝ => φ' (x * iotaR hw (rot θ)) :=
    hφ'.comp (continuous_const.mul ((continuous_iotaR hw).comp continuous_rot))
  have h₂ := continuous_conv_rot hw hV₀c hφ' α.2.1 x
  exact (norm_slice_sub_le hw h₁ h₂ _ (hM z hz) key).trans_lt (final_arith hM0 hε)

theorem differentiableOn_sl_conv (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {φ' : AdelicGL2 (𝓞 K) K → ℂ} (hφ' : Continuous φ')
    (hLs' : IsLsXiFunction (𝓞 K) K ⊤ ξ φ')
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (n : ℕ) (ψ : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (x : Fin n → AdelicGL2 (𝓞 K) K),
        (∀ i, Continuous (ψ i) ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ (ψ i) ∧
          HasArchCharacterAt₀ K w (archWeightOneAt hw) (ψ i) ∧ IsArchHolomorphicAt w hw (ψ i)) ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖φ' y - ∑ i, ψ i (y * x i)‖₊ : ℝ≥0∞) ^ 2 ∂(μK K) < ε)
    {V₀ : Set (AdelicGL2 (𝓞 K) K)} (hV₀c : IsCompact V₀) (α : Bump K V₀) (g : AdelicGL2 (𝓞 K) K) :
    DifferentiableOn ℂ (sl hw (conv K V₀ φ' α.1) g) {z : ℂ | 0 < z.im} := by
  have hV₀m : MeasurableSet V₀ := hV₀c.isClosed.measurableSet

  have hεn : ∀ n : ℕ, (0 : ℝ≥0∞) < (((n : ℝ≥0∞) + 1))⁻¹ := fun n => ENNReal.inv_pos.mpr (by simp)
  choose m ψ xs hψ hsl using fun n : ℕ => happrox _ (hεn n)
  set hfun : ℕ → AdelicGL2 (𝓞 K) K → ℂ := fun n y => ∑ i, ψ n i (y * xs n i) with hhfun
  have hfun_cont : ∀ n, Continuous (hfun n) := fun n =>
    continuous_finsetSum _ fun i _ => (hψ n i).1.comp (continuous_id.mul continuous_const)
  set Fn : ℕ → AdelicGL2 (𝓞 K) K → ℂ := fun n y => φ' y - hfun n y with hFn
  have hFn_cont : ∀ n, Continuous (Fn n) := fun n => hφ'.sub (hfun_cont n)
  have hFn_Ls : ∀ n, IsLsXiFunction (𝓞 K) K ⊤ ξ (Fn n) := fun n =>
    isLsXi_sub_sum (fun i => (hψ n i).2.1) hLs' (xs n)
  have hFn_D : ∀ n, ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
      ‖Fn n y‖ₑ ^ (2 : ℝ) ∂μK K < ((n : ℝ≥0∞) + 1)⁻¹ := fun n => by
    simpa [hFn, hhfun, enorm_eq_nnnorm] using hsl n

  have hdiffn : ∀ n, DifferentiableOn ℂ (sl hw (conv K V₀ (hfun n) α.1) g) {z : ℂ | 0 < z.im} := by
    intro n
    have hform : ∀ z ∈ {z : ℂ | 0 < z.im}, sl hw (conv K V₀ (hfun n) α.1) g z
        = ∑ i, ∫ y in V₀, (α.1 y : ℂ) * (coeff (wComp hw (y * xs n i)) *
          ((((UpperHalfPlane.ofComplex z).im : ℝ) : ℂ)⁻¹ *
            ψ n i (g * iotaS hw (UpperHalfPlane.ofComplex z) * flat hw (y * xs n i)))) ∂μK K := by
      intro z _
      simp only [sl]
      rw [Pint_conv_sum hw hV₀c (fun i => (hψ n i).1) α.2.1 (xs n), Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pint_conv_translate hw hV₀c (hψ n i).1 (hψ n i).2.1 (hψ n i).2.2.1 (hψ n i).2.2.2 α.2.1
        (xs n i), ← integral_const_mul]
      congr 1
      funext y
      ring
    refine DifferentiableOn.congr ?_ hform
    exact DifferentiableOn.fun_sum fun i _ =>
      differentiableOn_slice_integral hw hV₀c (hψ n i).1 (hψ n i).2.2.2 α.2.1 α.2.2.2.1 g (xs n i)

  have htend : TendstoLocallyUniformlyOn (fun n => sl hw (conv K V₀ (hfun n) α.1) g)
      (sl hw (conv K V₀ φ' α.1) g) Filter.atTop {z : ℂ | 0 < z.im} := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_U]
    intro Kc hKcU hKc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨M, hM0, hM⟩ := exists_bound_im_inv hKc hKcU
    have hC' := isCompact_base hw g hKc hKcU
    set C' := (fun p : ℂ × ℝ => g * iotaS hw (UpperHalfPlane.ofComplex p.1) * iotaR hw (rot p.2)) ''
      (Kc ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) with hC'def
    obtain ⟨N, hN⟩ :=
      AutomorphicForm.exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_coversModCentre
        K c u d₁ d₂ T hd hcov ξ (hC'.mul hV₀c)

    have hAα : (∫⁻ y in V₀, ‖(α.1 y : ℂ)‖ₑ ^ (2 : ℝ) ∂μK K) ^ (1 / 2 : ℝ) ≠ ⊤ := by
      obtain ⟨Mα, hMα⟩ := hV₀c.exists_bound_of_continuousOn
        (Complex.continuous_ofReal.comp α.2.1).continuousOn
      refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ne_of_lt ?_)
      calc ∫⁻ y in V₀, ‖(α.1 y : ℂ)‖ₑ ^ (2 : ℝ) ∂μK K
          ≤ ∫⁻ _ in V₀, ENNReal.ofReal Mα ^ (2 : ℝ) ∂μK K := by
            refine lintegral_mono_ae ?_
            filter_upwards [ae_restrict_mem hV₀m] with y hy
            refine ENNReal.rpow_le_rpow ?_ (by norm_num)
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hMα y hy)
        _ = ENNReal.ofReal Mα ^ (2 : ℝ) * μK K V₀ := by
            rw [lintegral_const, Measure.restrict_apply_univ]
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num)
            ENNReal.ofReal_ne_top) hV₀c.measure_lt_top
    set A := (∫⁻ y in V₀, ‖(α.1 y : ℂ)‖ₑ ^ (2 : ℝ) ∂μK K) ^ (1 / 2 : ℝ) with hA
    set e : ℕ → ℝ≥0∞ := fun n => (ENNReal.ofReal N * ((n : ℝ≥0∞) + 1)⁻¹) ^ (1 / 2 : ℝ) * A with he
    have he0 : Filter.Tendsto e Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
        have := ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
        refine this.congr fun n => ?_
        simp [Function.comp]
      have h2 : Filter.Tendsto (fun n : ℕ => ENNReal.ofReal N * ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop
          (nhds 0) := by
        simpa using ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
      have h3 : Filter.Tendsto (fun n : ℕ => (ENNReal.ofReal N * ((n : ℝ≥0∞) + 1)⁻¹) ^ (1 / 2 : ℝ))
          Filter.atTop (nhds 0) := by
        have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h2
        simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this ⊢
        exact this
      simpa [he] using ENNReal.Tendsto.mul_const h3 (Or.inr hAα)
    set δ := ε / (2 * (M * (2 * Real.pi) + 1)) with hδdef
    have hδpos : 0 < δ := by positivity
    have hev : ∀ᶠ n in Filter.atTop, e n < ENNReal.ofReal δ :=
      he0.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hδpos))
    filter_upwards [hev] with n hn z hz

    have hsmall : ∀ x' ∈ C', ‖conv K V₀ (Fn n) α.1 x'‖ < δ := by
      intro x' hx'
      have h1 := enorm_conv_le hV₀c hC' (hFn_cont n) α.2.1 hx'
      have h2 : ∫⁻ y in C' * V₀, ‖Fn n y‖ₑ ^ (2 : ℝ) ∂μK K ≤ ENNReal.ofReal N * ((n : ℝ≥0∞) + 1)⁻¹ := by
        have h := hN (Fn n) (hFn_Ls n) (hFn_cont n)
        have hD := (hFn_D n).le
        simp only [enorm_eq_nnnorm, ENNReal.rpow_ofNat] at hD ⊢
        exact h.trans (mul_le_mul' le_rfl hD)
      have h3 : ‖conv K V₀ (Fn n) α.1 x'‖ₑ < ENNReal.ofReal δ := by
        refine lt_of_le_of_lt (h1.trans ?_) hn
        exact mul_le_mul_left (ENNReal.rpow_le_rpow h2 (by norm_num)) _
      rw [← ofReal_norm] at h3
      exact (ENNReal.ofReal_lt_ofReal_iff hδpos).mp h3
    set x := g * iotaS hw (UpperHalfPlane.ofComplex z) with hx
    have key : ∀ θ : ℝ, θ ∈ Set.Icc 0 (2 * Real.pi) →
        ‖conv K V₀ φ' α.1 (x * iotaR hw (rot θ)) - conv K V₀ (hfun n) α.1 (x * iotaR hw (rot θ))‖
          ≤ δ := by
      intro θ hθ
      rw [← conv_sub hV₀c hφ' (hfun_cont n) α.2.1]
      exact (hsmall _ ⟨(z, θ), ⟨hz, hθ⟩, rfl⟩).le
    have h₁ := continuous_conv_rot hw hV₀c hφ' α.2.1 x
    have h₂ := continuous_conv_rot hw hV₀c (hfun_cont n) α.2.1 x
    exact (norm_slice_sub_le hw h₁ h₂ _ (hM z hz) key).trans_lt (final_arith hM0 hε)
  exact htend.differentiableOn (Filter.Eventually.of_forall hdiffn) isOpen_U

theorem main (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    {φ' : AdelicGL2 (𝓞 K) K → ℂ} (hφ' : Continuous φ')
    (hLs' : IsLsXiFunction (𝓞 K) K ⊤ ξ φ')
    (hφ'w : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ')
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (n : ℕ) (ψ : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (x : Fin n → AdelicGL2 (𝓞 K) K),
        (∀ i, Continuous (ψ i) ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ (ψ i) ∧
          HasArchCharacterAt₀ K w (archWeightOneAt hw) (ψ i) ∧ IsArchHolomorphicAt w hw (ψ i)) ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖φ' y - ∑ i, ψ i (y * x i)‖₊ : ℝ≥0∞) ^ 2 ∂(μK K) < ε) :
    IsArchHolomorphicAt w hw φ' := by
  intro g
  obtain ⟨V₀, hV₀c, hV₀n⟩ := exists_compact_mem_nhds (1 : AdelicGL2 (𝓞 K) K)
  haveI := bumpFilter_neBot (K := K) hV₀n
  rw [UpperHalfPlane.mdifferentiable_iff]
  have hS₀ : DifferentiableOn ℂ (sl hw φ' g) {z : ℂ | 0 < z.im} :=
    (tendsto_sl_conv hw hV₀c hφ' g).differentiableOn (Filter.Eventually.of_forall fun α =>
      differentiableOn_sl_conv hw c u d₁ d₂ T hd hcov ξ hφ' hLs' happrox hV₀c α g)
      isOpen_U
  refine (hS₀.const_mul ((2 * Real.pi : ℂ)⁻¹)).congr fun z hz => ?_
  simp only [Function.comp_apply, sl, Pint_of_weightOne hw hφ'w]
  have h2π : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  field_simp

end Analysis

end FamilyRigiditySol

end

open FamilyRigiditySol in
theorem solution
    (K : Type) [Field K] [NumberField K] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (φ' : AdelicGL2 (𝓞 K) K → ℂ) (hφ' : Continuous φ') (hφ'ξ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ')
    (w : InfinitePlace K) (hw : w.IsReal)
    (hφ'w : HasArchCharacterAt₀ K w (archWeightOneAt hw) φ')
    (happrox : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (n : ℕ) (ψ : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (x : Fin n → AdelicGL2 (𝓞 K) K),
        (∀ i, Continuous (ψ i) ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ (ψ i) ∧
          HasArchCharacterAt₀ K w (archWeightOneAt hw) (ψ i) ∧ IsArchHolomorphicAt w hw (ψ i)) ∧
        ∫⁻ y in ⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂,
            (‖φ' y - ∑ i, ψ i (y * x i)‖₊ : ℝ≥0∞) ^ 2 ∂(adelicGLHaar (Fin 2) (𝓞 K) K) < ε) :
    IsArchHolomorphicAt w hw φ' := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := glBorel (Fin 2) (𝓞 K) K
  exact FamilyRigiditySol.main hw c u d₁ d₂ T hd hcov ξ hφ' hφ'ξ hφ'w happrox

end S_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt
end P2MW
export P2MW.S_AutomorphicForm_isArchHolomorphicAt_of_forall_exists_setLIntegral_sub_sum_holomorphic_translate_sq_lt (solution)
