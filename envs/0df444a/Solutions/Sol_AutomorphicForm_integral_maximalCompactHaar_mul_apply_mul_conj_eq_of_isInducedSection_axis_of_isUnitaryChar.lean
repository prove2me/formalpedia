-- Prove2me | solution 1 for AutomorphicForm.integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e88ae9ee-273d-5cfe-8cd1-53b679922aba

import Theorems.Thm_AutomorphicForm_integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_AdelicHaar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar
open IsDedekindDomain
open scoped ComplexConjugate NNReal

namespace P2mAxisUnitarity

open AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

local notation "G" => AdelicGL2 (𝓞 K) K

theorem mul_conj_eq_ofReal (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem mul_conj_borel_mul (αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
    {μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hμ : IsUnitaryChar (𝓞 K) K μ) (hν : IsUnitaryChar (𝓞 K) K ν)
    (t : ℝ) {φ ψ : G → ℂ}
    (hφ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) φ)
    (hψ : IsInducedSection (𝓞 K) K (etaFst μ αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν αm hαm ((t : ℂ) * Complex.I)) ψ)
    (b : G) (hb : b ∈ adelicBorel (𝓞 K) K) (g : G) :
    φ (b * g) * conj (ψ (b * g)) =
      ((((αm (borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) /
          ((αm (borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K))) : ℝˣ) : ℝ) : ℝ) : ℂ) *
        (φ g * conj (ψ g)) := by
  set s : ℂ := (t : ℂ) * Complex.I with hs
  have hsre : s.re = 0 := by simp [hs]
  set x₁ := borelDiagFst (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hx₁
  set x₂ := borelDiagSnd (⟨b, hb⟩ : ↥(adelicBorel (𝓞 K) K)) with hx₂
  have hA : 0 < ((αm x₁ : ℝˣ) : ℝ) := hαm x₁
  have hD : 0 < ((αm x₂ : ℝˣ) : ℝ) := hαm x₂
  set e₁ : ℂ := ((etaFst μ αm hαm s x₁ : ℂˣ) : ℂ) with he₁
  set e₂ : ℂ := ((etaSnd ν αm hαm s x₂ : ℂˣ) : ℂ) with he₂
  have h1 : ‖e₁‖ = ((αm x₁ : ℝˣ) : ℝ) ^ (1 / 2 : ℝ) := by
    rw [he₁, norm_etaFst_apply_of_unitary hμ, hsre, zero_add]
  have h2 : ‖e₂‖ = ((αm x₂ : ℝˣ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [he₂, etaSnd_apply, Units.val_mul, norm_mul, hν x₂, one_mul, norm_cpowChar_apply]
    congr 1
    simp [hs]
  have hsq1 : ‖e₁‖ ^ 2 = ((αm x₁ : ℝˣ) : ℝ) := by
    rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]; norm_num
  have hsq2 : ‖e₂‖ ^ 2 = ((αm x₂ : ℝˣ) : ℝ)⁻¹ := by
    rw [h2, ← Real.rpow_natCast, ← Real.rpow_mul hD.le, ← Real.rpow_neg_one]; norm_num
  have hφb : φ (b * g) = e₁ * e₂ * φ g := hφ b hb g
  have hψb : ψ (b * g) = e₁ * e₂ * ψ g := hψ b hb g
  have hee : (e₁ * e₂) * conj (e₁ * e₂) =
      ((((αm x₁ : ℝˣ) : ℝ) / ((αm x₂ : ℝˣ) : ℝ) : ℝ) : ℂ) := by
    rw [mul_conj_eq_ofReal, norm_mul, mul_pow, hsq1, hsq2, div_eq_mul_inv]
  rw [hφb, hψb, map_mul, ← hee]
  ring

end P2mAxisUnitarity

open P2mAxisUnitarity AutomorphicForm

theorem solution
    (K : Type) [Field K] [NumberField K] :
    let α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (t : ℝ) (φ ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hφ : IsInducedSection (𝓞 K) K (etaFst μ α hα ((t : ℂ) * Complex.I)) (etaSnd ν α hα ((t : ℂ) * Complex.I)) φ)
      (_hψ : IsInducedSection (𝓞 K) K (etaFst μ α hα ((t : ℂ) * Complex.I)) (etaSnd ν α hα ((t : ℂ) * Complex.I)) ψ)
      (_hφc : Continuous φ) (_hψc : Continuous ψ)
      (g : AdelicGL2 (𝓞 K) K),
    ∫ k, φ ((k : AdelicGL2 (𝓞 K) K) * g) * conj (ψ ((k : AdelicGL2 (𝓞 K) K) * g)) ∂(maximalCompactHaar K) =
      ∫ k, φ (k : AdelicGL2 (𝓞 K) K) * conj (ψ (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
  intro αm hαm μ ν hμ hν t φ ψ hφ hψ hφc hψc g
  exact AutomorphicForm.integral_maximalCompact_comp_mul_eq_integral_of_forall_borel_mul_eq_modulus_mul K
    (fun x => φ x * conj (ψ x)) (hφc.mul (Complex.continuous_conj.comp hψc))
    (fun b hb x => mul_conj_borel_mul K αm hαm hμ hν t hφ hψ b hb x) g

end S_AutomorphicForm_integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar
end P2MW
export P2MW.S_AutomorphicForm_integral_maximalCompactHaar_mul_apply_mul_conj_eq_of_isInducedSection_axis_of_isUnitaryChar (solution)
