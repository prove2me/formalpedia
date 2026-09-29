-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.inf_eq_bot_or_le_of_isCuspConstituent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/f7836568-c997-5c62-a57b-97929b633194

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self"
p2m_attr_erase "simp" "AdelicDock.coe_localEmbed"

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "AutomorphicForm P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open NumberField.SiegelVolume
p2m_open "AutomorphicForm.CuspidalConstituent P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent.AutomorphicForm.CuspidalConstituent"
open scoped BigOperators

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ ArchTypeFamily archCutSubmodule IsArchBiFinite CarrierPins productionPinsOf AdelicGL2 finiteAdelicGL2Subgroup rightConv rowIsometrySubgroup₀ IsFactorizableTestFn CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le"
namespace CuspidalConstituent
p2m_export "AutomorphicForm.CuspidalConstituent" "rightTranslate IsCuspSubrep IsCuspConstituent levelInvariantSubmodule iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le"
namespace C8F55
p2m_open "AutomorphicForm.CuspidalConstituent AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

theorem isCuspSubrep_iInf₂ {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {P : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) → Prop}
    (hP : ∀ W, P W → IsCuspSubrep F pins ξ W) {W₀ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hW₀ : P W₀) :
    IsCuspSubrep F pins ξ (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : P W), W) := by
  refine ⟨(iInf₂_le W₀ hW₀).trans (hP W₀ hW₀).le, fun g hg φ hφ => ?_, fun w k φ hφ => ?_, fun f tys hf hbf φ hφ => ?_⟩
  · simp only [Submodule.mem_iInf] at hφ ⊢
    exact fun W hW => (hP W hW).rightTranslate_fin_mem g hg φ (hφ W hW)
  · simp only [Submodule.mem_iInf] at hφ ⊢
    exact fun W hW => (hP W hW).rightTranslate_arch_mem w k φ (hφ W hW)
  · simp only [Submodule.mem_iInf] at hφ ⊢
    exact fun W hW => (hP W hW).rightConv_mem f tys hf hbf φ (hφ W hW)

end AutomorphicForm.CuspidalConstituent.C8F55

open AutomorphicForm.CuspidalConstituent.C8F55 in
theorem solution
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hV : IsCuspConstituent F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V)
    (M : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hMk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ M, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ M)
    (hMhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, ∃ u' ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = u * g * u') →
        ∃ i, ∃ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N → i = j) →
      ∀ φ ∈ M ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N,
        (fun x => ∑ i, φ (x * reps i)) ∈ M)
    (hMconv : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → IsArchBiFinite F tys f →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, f (u * x) = f x ∧ f (x * u) = f x) →
      ∀ φ ∈ M, rightConv F φ f ∈ M) :
    V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M = ⊥ ∨
      V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ M := by
  classical
  by_cases hY : V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M = ⊥
  · exact Or.inl hY
  right

  set Y := V ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ⊓ M with hYdef
  set W₀ := ⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W ∧ Y ≤ W), W with hW₀
  have hVin : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ V ∧ Y ≤ V :=
    ⟨hV.1, inf_le_left.trans (inf_le_left.trans inf_le_left)⟩
  have hW₀rep : IsCuspSubrep F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) ξ W₀ := isCuspSubrep_iInf₂ (fun W hW => hW.1) hVin
  have hW₀V : W₀ ≤ V := iInf₂_le V hVin
  have hYW₀ : Y ≤ W₀ := le_iInf₂ fun W hW => hW.2
  have hW₀ne : W₀ ≠ ⊥ := fun h => hY (le_bot_iff.mp (h ▸ hYW₀))

  have hW₀eq : W₀ = V := (hV.2.2 W₀ hW₀rep hW₀V).resolve_left hW₀ne

  have hcut := AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_levelInvariantSubmodule_inf_archCutSubmodule_le
    F D ξ N hN tys V hV.1 M hMk hMhecke hMconv

  have : W₀ ⊓ levelInvariantSubmodule F (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)) N ⊓ archCutSubmodule F tys ≤ M := hcut
  rw [hW₀eq] at this
  exact this

end S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_inf_eq_bot_or_le_of_isCuspConstituent (solution)
