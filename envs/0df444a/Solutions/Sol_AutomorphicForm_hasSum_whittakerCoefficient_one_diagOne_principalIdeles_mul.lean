-- Prove2me | solution 1 for AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8f951e32-c738-5782-b4ee-6f695252b3a8

import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_AutomorphicForm_hasSum_whittakerCoefficient
import Theorems.Thm_AutomorphicForm_whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
import Theorems.Thm_AutomorphicForm_whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec"
p2m_attr_erase "simp" "NumberField.StandardAddChar.AdelicTraceData.mk.injEq NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.AdelicBox NumberField.AdelicLevel AutomorphicForm

noncomputable section

namespace Ws1
namespace K4

open NumberField NumberField.AdelicLevel AutomorphicForm

theorem globalPoints_unipotentGL2 (F : Type) [Field F] [NumberField F] (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  simp only [globalPoints, Matrix.GeneralLinearGroup.map, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, unipotentGL2_coe]

theorem globalPoints_diagOne (F : Type) [Field F] [NumberField F] (u : Fˣ) :
    globalPoints (𝓞 F) F (diagOne u) =
      diagOne (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) u) := by
  apply Units.ext
  ext i j
  simp only [globalPoints, Matrix.GeneralLinearGroup.map, diagOne_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [RingHom.mapMatrix_apply, diagOne_coe_apply, Matrix.diagonal]

theorem principalIdeles_equiv (F : Type) [Field F] [NumberField F] :
    ∃ e : {α : F // α ≠ 0} ≃ ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
      ∀ a : {α : F // α ≠ 0}, ((e a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) =
        Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (Units.mk0 a.1 a.2) := by
  classical
  let fwd : {α : F // α ≠ 0} → ↥(M4aHerbrand.principalIdeles (𝓞 F) F) := fun a =>
    ⟨Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) (Units.mk0 a.1 a.2),
      ⟨Units.mk0 a.1 a.2, rfl⟩⟩
  have hinj : Function.Injective fwd := by
    intro a b hab
    have h1 : ((fwd a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ) = fwd b :=
      congrArg Subtype.val hab
    have h2 := congrArg (fun x : (AdeleRing (𝓞 F) F)ˣ => (x : AdeleRing (𝓞 F) F)) h1
    simp only [fwd, Units.coe_map, MonoidHom.coe_coe, Units.val_mk0] at h2
    exact Subtype.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F h2)
  have hsurj : Function.Surjective fwd := by
    rintro ⟨_, u, rfl⟩
    refine ⟨⟨(u : F), u.ne_zero⟩, Subtype.ext ?_⟩
    simp only [fwd, Units.mk0_val]
  exact ⟨Equiv.ofBijective fwd ⟨hinj, hsurj⟩, fun a => rfl⟩

end Ws1.K4

end

open scoped Classical in

theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsGlobalAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hcont : Continuous φ)
    (hleft : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      φ (globalPoints (𝓞 F) F γ * g) = φ g)
    (hsm : IsKfSmooth F φ)
    (harch : ∀ g : AdelicGL2 (𝓞 F) F,
      ContDiff ℝ (Module.finrank ℚ F + 1) (fun z : mixedEmbedding.mixedSpace F =>
        φ (unipotentGL2 (R := AdeleRing (𝓞 F) F)
          ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm z, 0) * g)))
    (hcusp : ∀ g : AdelicGL2 (𝓞 F) F,
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 0 g = 0)
    (g : AdelicGL2 (𝓞 F) F) :
    HasSum (fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (diagOne (γ : (AdeleRing (𝓞 F) F)ˣ) * g))
      (φ g) := by
  classical

  have hleftN : ∀ (β : F) (g : AdelicGL2 (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) * g) = φ g := by
    intro β g
    rw [← Ws1.K4.globalPoints_unipotentGL2 F β]
    exact hleft _ g

  obtain ⟨-, hsumm⟩ :=
    AutomorphicForm.whittakerCoefficientIntegrable_and_summable_of_isKfSmooth_of_contDiff_mixedSpace
      F D U gen ψ hψ φ hleftN hsm harch
  have hslice : Continuous (fun x : AdeleRing (𝓞 F) F => φ (unipotentGL2 x * g)) :=
    hcont.comp (AutomorphicForm.continuous_unipotentGL2.mul continuous_const)
  have hF : HasSum (fun α : F => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) (φ g) :=
    AutomorphicForm.hasSum_whittakerCoefficient F D U gen ψ hψ φ g hslice (hsumm g)

  have hsupp : Function.support
      (fun α : F => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) ⊆ {α : F | α ≠ 0} := by
    intro α hα
    simp only [Function.mem_support, ne_eq] at hα
    intro h0
    exact hα (h0 ▸ hcusp g)
  have hF' := (hasSum_subtype_iff_of_support_subset hsupp).mpr hF

  obtain ⟨e, he⟩ := Ws1.K4.principalIdeles_equiv F
  refine (e.hasSum_iff).mp ?_
  have key : ∀ a : {α : F // α ≠ 0},
      whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (diagOne (((e a : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) : (AdeleRing (𝓞 F) F)ˣ)) * g)
        = whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ (a : F) g := by
    intro a
    rw [he a, ← Ws1.K4.globalPoints_diagOne F,
      AutomorphicForm.whittakerCoefficient_eq_whittakerCoefficient_one_globalPoints_diagOne_mul F D U gen ψ hψ φ
        hleft (a : F) a.2 g]
  have hfun : ((fun γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F) =>
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ 1
          (diagOne (γ : (AdeleRing (𝓞 F) F)ˣ) * g)) ∘ ⇑e)
      = (fun α : F => whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g) ∘ Subtype.val := by
    funext a
    exact key a
  rw [hfun]
  exact hF'

end S_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul
end P2MW
export P2MW.S_AutomorphicForm_hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul (solution)
