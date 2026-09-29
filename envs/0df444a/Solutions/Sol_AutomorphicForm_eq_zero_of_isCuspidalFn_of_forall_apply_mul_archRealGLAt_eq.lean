-- Prove2me | solution 1 for AutomorphicForm.eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/9f34ed9c-26ce-5473-81f2-314be38842a0

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul
import Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain"

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "CarrierPins productionPinsOf AdelicGL2 globalPoints unipotentGL2 unipotentGL2_coe unipotentGL2_zero unipotentGL2_add IsCuspidalFn archRealGLAt eq_of_glArch_eq_of_glFin_eq archRealProjAt archGLIncl archComponent_archGLIncl_self archComponent_archGLIncl_of_ne glArch_adelicArchGLIncl glFin_adelicArchGLIncl glEquivOfRingEquiv glEquivOfRingEquiv_apply_entry hasSum_whittakerCoefficient whittakerCoefficient whittakerCoefficient_zero_eq_constantTerm whittakerCoefficient_unipotentGL2_mul continuous_unipotentGL2"
namespace Ws46
namespace FLAT
p2m_open "AutomorphicForm"

theorem map_unipotentGL2 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    Matrix.GeneralLinearGroup.map f (unipotentGL2 x) = unipotentGL2 (f x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change f ((unipotentGL2 x : Matrix (Fin 2) (Fin 2) R) i j) =
    (unipotentGL2 (f x) : Matrix (Fin 2) (Fin 2) S) i j
  simp only [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem glEquivOfRingEquiv_unipotentGL2 {K L : Type*} [NormedField K] [NormedField L] (e : K ≃+* L) (x : K) :
    glEquivOfRingEquiv e (unipotentGL2 x) = unipotentGL2 (e x) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glEquivOfRingEquiv_apply_entry]
  simp only [unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

section RealPlace

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsReal)

omit [NumberField F] in
theorem glArch_ext {g h : GL (Fin 2) (InfiniteAdeleRing F)}
    (H : ∀ v : InfinitePlace F, archComponent F v g = archComponent F v h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => funext fun v => ?_)
  have := congrFun (congrFun (congrArg
    (fun m : GL (Fin 2) v.Completion => (m : Matrix (Fin 2) (Fin 2) v.Completion)) (H v)) i) j
  rwa [archComponent_apply, archComponent_apply] at this

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) : glFin (𝓞 F) F (archRealGLAt hw m) = 1 :=
  glFin_adelicArchGLIncl F _

theorem glArch_archRealGLAt (m : GL (Fin 2) ℝ) :
    glArch (𝓞 F) F (archRealGLAt hw m) =
      archGLIncl F w (glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m) :=
  glArch_adelicArchGLIncl F _

theorem archComponent_archRealGLAt_self (m : GL (Fin 2) ℝ) :
    archComponent F w (glArch (𝓞 F) F (archRealGLAt hw m)) =
      glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm m := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_self]

theorem archComponent_archRealGLAt_of_ne {v : InfinitePlace F} (hv : v ≠ w) (m : GL (Fin 2) ℝ) :
    archComponent F v (glArch (𝓞 F) F (archRealGLAt hw m)) = 1 := by
  rw [glArch_archRealGLAt, archComponent_archGLIncl_of_ne F hv]

theorem symm_apply_archRealProjAt (y : AdelicGL2 (𝓞 F) F) :
    glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm (archRealProjAt hw y) =
      archComponent F w (glArch (𝓞 F) F y) := by
  show glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm
    (glEquivOfRingEquiv (ringEquivRealOfIsReal hw) (archComponent F w (glArch (𝓞 F) F y))) = _
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [glEquivOfRingEquiv_apply_entry, glEquivOfRingEquiv_apply_entry]
  exact (ringEquivRealOfIsReal hw).symm_apply_apply _

theorem archRealGLAt_mul (h : GL (Fin 2) ℝ) (y : AdelicGL2 (𝓞 F) F) :
    archRealGLAt hw h * y = y * archRealGLAt hw ((archRealProjAt hw y)⁻¹ * h * archRealProjAt hw y) := by
  refine eq_of_glArch_eq_of_glFin_eq (glArch_ext fun v => ?_) ?_
  · simp only [map_mul, map_inv]
    by_cases hv : v = w
    · subst hv
      simp only [archComponent_archRealGLAt_self, symm_apply_archRealProjAt]
      rw [mul_assoc, mul_inv_cancel_left]
    · simp only [archComponent_archRealGLAt_of_ne hw hv, inv_one, one_mul, mul_one]
  · simp only [map_mul, map_inv, glFin_archRealGLAt, inv_one, one_mul, mul_one]

omit [NumberField F] in
theorem det_conj_eq_one (h a : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    Matrix.GeneralLinearGroup.det (a⁻¹ * h * a) = 1 := by
  rw [map_mul, map_mul, map_inv, hh, mul_one, inv_mul_cancel]

open scoped Classical in

theorem archRealGLAt_unipotentGL2 (t : ℝ) :
    archRealGLAt hw (unipotentGL2 t) =
      unipotentGL2 (show (AdeleRing (𝓞 F) F) from
        (Pi.single w ((ringEquivRealOfIsReal hw).symm t), 0)) := by
  refine eq_of_glArch_eq_of_glFin_eq (glArch_ext fun v => ?_) ?_
  ·
    have hR : archComponent F v (glArch (𝓞 F) F (unipotentGL2 (show (AdeleRing (𝓞 F) F) from
        (Pi.single w ((ringEquivRealOfIsReal hw).symm t), 0)))) =
        unipotentGL2 ((Pi.single w ((ringEquivRealOfIsReal hw).symm t) : InfiniteAdeleRing F) v) := by
      rw [glArch, map_unipotentGL2, archComponent, map_unipotentGL2]
      rfl
    rw [hR]
    by_cases hv : v = w
    · subst hv
      rw [archComponent_archRealGLAt_self, glEquivOfRingEquiv_unipotentGL2, Pi.single_eq_same]
    · rw [archComponent_archRealGLAt_of_ne hw hv, Pi.single_eq_of_ne hv, unipotentGL2_zero]
  · rw [glFin_archRealGLAt, glFin, map_unipotentGL2]
    symm
    show unipotentGL2 (0 : FiniteAdeleRing (𝓞 F) F) = 1
    exact unipotentGL2_zero

open scoped Classical in

theorem algebraMap_mul_lineAdele (α : F) (t : ℝ) :
    algebraMap F (AdeleRing (𝓞 F) F) α *
        (show (AdeleRing (𝓞 F) F) from (Pi.single w ((ringEquivRealOfIsReal hw).symm t), 0)) =
      (show (AdeleRing (𝓞 F) F) from
        (Pi.single w ((ringEquivRealOfIsReal hw).symm
          (ringEquivRealOfIsReal hw ((algebraMap F (AdeleRing (𝓞 F) F) α).1 w) * t)), 0)) := by
  refine Prod.ext (funext fun v => ?_) ?_
  · change (algebraMap F (AdeleRing (𝓞 F) F) α).1 v *
        (Pi.single w ((ringEquivRealOfIsReal hw).symm t) : (j : InfinitePlace F) → j.Completion) v =
      (Pi.single w ((ringEquivRealOfIsReal hw).symm
        (ringEquivRealOfIsReal hw ((algebraMap F (AdeleRing (𝓞 F) F) α).1 w) * t)) :
          (j : InfinitePlace F) → j.Completion) v
    by_cases hv : v = w
    · subst hv
      rw [Pi.single_eq_same, Pi.single_eq_same, map_mul, RingEquiv.symm_apply_apply]
    · rw [Pi.single_eq_of_ne hv, Pi.single_eq_of_ne hv, mul_zero]
  · show (algebraMap F (AdeleRing (𝓞 F) F) α).2 * 0 = 0
    exact mul_zero _

theorem ringEquivRealOfIsReal_algebraMap_ne_zero {α : F} (hα : α ≠ 0) :
    ringEquivRealOfIsReal hw ((algebraMap F (AdeleRing (𝓞 F) F) α).1 w) ≠ 0 := by
  have h1 : (algebraMap F (AdeleRing (𝓞 F) F) α).1 w ≠ 0 := by
    have := (map_ne_zero_iff _ (RingHom.injective
      ((archEval F w).comp ((adeleArch (𝓞 F) F).comp (algebraMap F (AdeleRing (𝓞 F) F)))))).mpr hα
    exact this
  exact (map_ne_zero_iff _ (ringEquivRealOfIsReal hw).injective).mpr h1

open scoped Classical in

theorem stdAddChar_lineAdele_half :
    NumberField.StandardAddChar.stdAddChar F
        (show (AdeleRing (𝓞 F) F) from (Pi.single w ((ringEquivRealOfIsReal hw).symm (1 / 2)), 0)) = -1 := by
  rw [NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal F w hw (1 / 2)]
  have : (2 * Real.pi * Complex.I * ((1 / 2 : ℝ) : ℂ)) = Real.pi * Complex.I := by
    push_cast
    ring
  rw [this, Complex.exp_pi_mul_I]

end RealPlace

section Whittaker

variable (F : Type) [Field F] [NumberField F]

theorem whittakerCoefficient_congr_slice (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (α : F) (g g' : AdelicGL2 (𝓞 F) F)
    (h : ∀ u : AdeleRing (𝓞 F) F, φ (unipotentGL2 u * g) = φ (unipotentGL2 u * g')) :
    whittakerCoefficient F pins ψ φ α g = whittakerCoefficient F pins ψ φ α g' := by
  simp only [whittakerCoefficient, h]

variable {F}

theorem whittakerCoefficient_archRealGLAt_unipotent_mul {w : InfinitePlace F} (hw : w.IsReal)
    (pins : CarrierPins F) (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      φ (g * archRealGLAt hw h) = φ g)
    (α : F) (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    whittakerCoefficient F pins ψ φ α (archRealGLAt hw (unipotentGL2 t) * g) =
      whittakerCoefficient F pins ψ φ α g := by
  refine whittakerCoefficient_congr_slice F pins ψ φ α _ _ fun u => ?_
  rw [archRealGLAt_mul hw, ← mul_assoc]
  refine hinv _ _ (det_conj_eq_one _ _ ?_)

  refine Units.ext ?_
  simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

theorem slice_periodic (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (g : AdelicGL2 (𝓞 F) F) (β : F) (u : AdeleRing (𝓞 F) F) :
    φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g) := by
  rw [unipotentGL2_add, mul_assoc]
  have : unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) = globalPoints (𝓞 F) F (unipotentGL2 β) := by
    rw [globalPoints, map_unipotentGL2]
  rw [this, hleft]

open scoped Classical in

theorem whittakerCoefficient_eq_zero_of_ne_zero
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hleft : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    {w : InfinitePlace F} (hw : w.IsReal)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      φ (g * archRealGLAt hw h) = φ g)
    {α : F} (hα : α ≠ 0) (g : AdelicGL2 (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) φ α g = 0 := by
  set r : ℝ := ringEquivRealOfIsReal hw ((algebraMap F (AdeleRing (𝓞 F) F) α).1 w) with hr
  have hr0 : r ≠ 0 := ringEquivRealOfIsReal_algebraMap_ne_zero hw hα
  set t : ℝ := 1 / (2 * r) with ht
  have hrt : r * t = 1 / 2 := by
    rw [ht]; field_simp
  set W := whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) φ α g with hW

  have hcov := AutomorphicForm.whittakerCoefficient_unipotentGL2_mul F D U gen
    (NumberField.StandardAddChar.stdAddChar F)
    (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F).principalInvariant φ g
    (slice_periodic φ hleft g) α
    (show (AdeleRing (𝓞 F) F) from (Pi.single w ((ringEquivRealOfIsReal hw).symm t), 0))
  have hinv' := whittakerCoefficient_archRealGLAt_unipotent_mul hw (productionPinsOf F D U gen (adelicBox F))
    (NumberField.StandardAddChar.stdAddChar F) φ hinv α g t
  rw [archRealGLAt_unipotentGL2 hw t, hcov, algebraMap_mul_lineAdele hw α t] at hinv'
  rw [← hr, hrt, stdAddChar_lineAdele_half hw] at hinv'

  have : (2 : ℂ) * W = 0 := by linear_combination -hinv'
  simpa using this

end Whittaker

theorem main
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hleft : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hcusp : @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 φ)
    (w : InfinitePlace F) (hw : w.IsReal)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      φ (g * archRealGLAt hw h) = φ g) :
    φ = 0 := by
  funext g

  have hW : (fun α : F => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F))
      (NumberField.StandardAddChar.stdAddChar F) φ α g) = fun _ => 0 := by
    funext α
    by_cases hα : α = 0
    · subst hα
      rw [whittakerCoefficient_zero_eq_constantTerm]
      exact hcusp g
    · exact whittakerCoefficient_eq_zero_of_ne_zero D U gen φ hleft hw hinv hα g
  have hcont : Continuous fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g) :=
    hφ.comp ((AutomorphicForm.continuous_unipotentGL2).mul continuous_const)
  have hsum := AutomorphicForm.hasSum_whittakerCoefficient F D U gen
    (NumberField.StandardAddChar.stdAddChar F) (NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F)
    φ g hcont (by rw [hW]; exact summable_zero)
  rw [hW] at hsum
  exact hsum.unique hasSum_zero

end AutomorphicForm.Ws46.FLAT

end

p2m_open "NumberField NumberField.InfinitePlace.NumberField NumberField.AdelicLevel NumberField.AdelicBox AutomorphicForm P2MW.S_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering NumberField.InfinitePlace NumberField.InfinitePlace.NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain"

theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (hleft : ∀ (γ : GL (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hcusp : @IsCuspidalFn _ (productionPinsOf F D U gen (adelicBox F)).nS _ _
      (productionPinsOf F D U gen (adelicBox F)).ν unipotentGL2 φ)
    (w : InfinitePlace F) (hw : w.IsReal)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      φ (g * archRealGLAt hw h) = φ g) :
    φ = 0 :=
  AutomorphicForm.Ws46.FLAT.main F D U gen φ hφ hleft hcusp w hw hinv

end S_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq
end P2MW
export P2MW.S_AutomorphicForm_eq_zero_of_isCuspidalFn_of_forall_apply_mul_archRealGLAt_eq (solution)
