-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/513f0c78-084c-5bdf-80c6-6b2b092537f0

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_isCuspLift_rightTranslate_and_norm_le
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false

set_option synthInstance.maxHeartbeats 320000

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace IsoRepU

section Dense

variable (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
  (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)

theorem exists_mem_norm_sub_lt (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
      ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ < ε := by
  have hv : (v : Carrier F Φ₀ σ) ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) : Set (Carrier F Φ₀ σ))) := by
    rw [← Submodule.topologicalClosure_coe]; exact v.2
  obtain ⟨a, haA, hav⟩ := Metric.mem_closure_iff.mp hv ε hε
  obtain ⟨φm, hφm, rfl⟩ := haA
  refine ⟨φm, hφm, ?_⟩
  rw [Submodule.coe_norm, Submodule.coe_sub, toCuspSubcarrier_apply_coe, ← dist_eq_norm]
  exact hav

variable {F hΦ₀ σ ξ}

theorem eq_of_isCuspLift {op : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ)}
    (hop : ∀ φ ∈ cuspMemberSubmodule F Φ₀ ξ, op φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    {S S' : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)}
    (hS : IsCuspLift F hΦ₀ σ ξ op S) (hS' : IsCuspLift F hΦ₀ σ ξ op S') : S = S' := by
  letI normedInst : NormedAddCommGroup (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  refine ContinuousLinearMap.ext fun v => ?_

  have key : ∀ ε : ℝ, 0 < ε → ‖S v - S' v‖ ≤ (‖S‖ + ‖S'‖) * ε := by
    intro ε hε
    obtain ⟨φ, hφ, hva⟩ := exists_mem_norm_sub_lt F hΦ₀ σ ξ v ε hε
    have hSa : S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) = S' (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) := by
      rw [hS ⟨φ, hφ⟩ (hop φ hφ), hS' ⟨φ, hφ⟩ (hop φ hφ)]
    have hdec : S v - S' v = S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) - S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) := by
      rw [map_sub, map_sub, hSa]; abel
    rw [hdec]
    calc ‖S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) - S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖
        ≤ ‖S (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ + ‖S' (v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)‖ := norm_sub_le _ _
      _ ≤ ‖S‖ * ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ + ‖S'‖ * ‖v - toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩‖ :=
          add_le_add (S.le_opNorm _) (S'.le_opNorm _)
      _ ≤ ‖S‖ * ε + ‖S'‖ * ε := add_le_add (mul_le_mul_of_nonneg_left hva.le (norm_nonneg S))
          (mul_le_mul_of_nonneg_left hva.le (norm_nonneg S'))
      _ = (‖S‖ + ‖S'‖) * ε := by ring
  have h0 : ‖S v - S' v‖ ≤ 0 := by
    by_contra hc
    push Not at hc
    have hpos : 0 < ‖S‖ + ‖S'‖ + 1 := by positivity
    have := key (‖S v - S' v‖ / (2 * (‖S‖ + ‖S'‖ + 1))) (by positivity)
    have hlt : (‖S‖ + ‖S'‖) * (‖S v - S' v‖ / (2 * (‖S‖ + ‖S'‖ + 1))) < ‖S v - S' v‖ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg S, norm_nonneg S']
    exact absurd (this.trans_lt hlt) (lt_irrefl _)
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)

end Dense

end IsoRepU

open IsoRepU in
theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F))) :
    ∃ π : U →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ u : U, IsCuspLift F hΦ₀ σ ξ (rightTranslate F (u : AdelicGL2 (𝓞 F) F)) (π u)) ∧
      (∀ (u : U) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π u v‖ = ‖v‖) ∧
      (∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun u : U => π u v) := by
  classical

  let y : ↥U →* AdelicGL2 (𝓞 F) F := U.subtype
  have hy : ∀ u : ↥U, y u = (u : AdelicGL2 (𝓞 F) F) := fun _ => rfl
  have hyc : Continuous y := continuous_subtype_val
  have hN : ∀ u : ↥U, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det (y u)) = 1 :=
    fun u => NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem F U hU (u : AdelicGL2 (𝓞 F) F) u.2
  have hmem : ∀ (u : ↥U) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ cuspMemberSubmodule F Φ₀ ξ →
      rightTranslate F (y u) φ ∈ cuspMemberSubmodule F Φ₀ ξ := fun u φ hφ =>
    AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (y u) φ hφ

  choose π₀ hπ₀ using fun u : ↥U =>
    AutomorphicForm.CuspidalSpectrum.exists_isCuspLift_rightTranslate_and_norm_le F hΦ₀ σ ξ hσ (y u)
  letI normedInst : NormedAddCommGroup (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
  have hnorm : ∀ u, ‖π₀ u‖ ≤ 1 := fun u => by
    have h := (hπ₀ u).2
    rwa [hN u, Real.one_rpow] at h

  have hone : π₀ 1 = 1 := by
    refine eq_of_isCuspLift (hmem 1) (hπ₀ 1).1 fun φ h => ?_
    have hR : rightTranslate F (y 1) φ = φ := by
      funext x; rw [map_one, rightTranslate_apply, mul_one]
    rw [ContinuousLinearMap.one_apply]
    congr 1
    exact Subtype.ext hR.symm
  have hmul : ∀ a b, π₀ (a * b) = π₀ a * π₀ b := by
    intro a b
    refine eq_of_isCuspLift (hmem (a * b)) (hπ₀ (a * b)).1 fun φ h => ?_
    have hb : rightTranslate F (y b) φ ∈ cuspMemberSubmodule F Φ₀ ξ := hmem b φ φ.2
    have hab : rightTranslate F (y a) (rightTranslate F (y b) φ) ∈ cuspMemberSubmodule F Φ₀ ξ := hmem a _ hb
    rw [ContinuousLinearMap.mul_apply, (hπ₀ b).1 φ hb, (hπ₀ a).1 ⟨_, hb⟩ hab]
    congr 1
    apply Subtype.ext
    show rightTranslate F (y a) (rightTranslate F (y b) φ) = rightTranslate F (y (a * b)) φ
    rw [rightTranslate_rightTranslate, map_mul]
  let π : ↥U →* (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) :=
    { toFun := π₀, map_one' := hone, map_mul' := hmul }
  have hπ : ∀ u, π u = π₀ u := fun _ => rfl

  have hiso : ∀ (u) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)), ‖π u v‖ = ‖v‖ := by
    intro u v
    apply le_antisymm
    · exact (ContinuousLinearMap.le_opNorm _ _).trans (by rw [hπ]; nlinarith [hnorm u, norm_nonneg v])
    · have hinv : π u⁻¹ (π u v) = v := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, inv_mul_cancel, map_one, ContinuousLinearMap.one_apply]
      calc ‖v‖ = ‖π u⁻¹ (π u v)‖ := by rw [hinv]
        _ ≤ ‖π u⁻¹‖ * ‖π u v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖π u v‖ := mul_le_mul_of_nonneg_right (hnorm u⁻¹) (norm_nonneg _)
        _ = ‖π u v‖ := one_mul _
  refine ⟨π, fun u => (hπ₀ u).1, hiso, fun v => ?_⟩

  refine continuous_iff_continuousAt.mpr fun u₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨φ, hφ, hva⟩ := exists_mem_norm_sub_lt F hΦ₀ σ ξ v (ε / 3) hε3
  set a : ↥(cuspSubcarrier F hΦ₀ σ ξ) := toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ with ha
  obtain ⟨V, hV, hVlt⟩ := AutomorphicForm.CuspidalSpectrum.exists_nhds_forall_norm_toCarrier_rightTranslate_sub_lt
    F hΦ₀ σ ξ hσ φ ⟨hφ.1.1.1, hφ.2⟩ (ε / 3) hε3
  have hf : Continuous fun u : ↥U => y (u₀⁻¹ * u) := hyc.comp (continuous_const.mul continuous_id)
  have hpre : (fun u : ↥U => y (u₀⁻¹ * u)) ⁻¹' V ∈ 𝓝 u₀ :=
    hf.continuousAt.preimage_mem_nhds (by rw [inv_mul_cancel, map_one]; exact hV)
  refine Filter.eventually_of_mem hpre fun u hu => ?_
  obtain ⟨hy', hlt⟩ := hVlt _ hu
  have hmid : ‖π u a - π u₀ a‖ < ε / 3 := by
    have hκeq : π u = π u₀ * π (u₀⁻¹ * u) := by rw [← map_mul, mul_inv_cancel_left]
    have h1 : π u a - π u₀ a = π u₀ (π (u₀⁻¹ * u) a - a) := by
      rw [map_sub, hκeq, ContinuousLinearMap.mul_apply]
    rw [h1, hiso]
    have hlift : π (u₀⁻¹ * u) a = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F (y (u₀⁻¹ * u)) φ, hmem _ φ hφ⟩ :=
      (hπ₀ (u₀⁻¹ * u)).1 ⟨φ, hφ⟩ (hmem _ φ hφ)
    rw [hlift, ha, Submodule.coe_norm, Submodule.coe_sub, toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
    exact hlt
  rw [dist_eq_norm]
  have hsplit : π u v - π u₀ v = π u (v - a) + (π u a - π u₀ a) + π u₀ (a - v) := by
    simp only [map_sub]; abel
  calc ‖π u v - π u₀ v‖ = ‖π u (v - a) + (π u a - π u₀ a) + π u₀ (a - v)‖ := by rw [hsplit]
    _ ≤ ‖π u (v - a)‖ + ‖π u a - π u₀ a‖ + ‖π u₀ (a - v)‖ := norm_add₃_le
    _ = ‖v - a‖ + ‖π u a - π u₀ a‖ + ‖a - v‖ := by rw [hiso, hiso]
    _ < ε / 3 + ε / 3 + ε / 3 := by
        have h2 : ‖a - v‖ < ε / 3 := by rw [norm_sub_rev]; exact hva
        linarith
    _ = ε := by ring

end S_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_monoidHom_isCuspLift_rightTranslate_coe_and_norm_eq_and_continuous_of_isCompact (solution)
