-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_isLift_rightConv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/824358f5-e749-560f-834e-e0a0c079567e

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_norm_toCarrier_rightConv_le
import Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport
import Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

theorem solution
    (F : Type) [Field F] [NumberField F] (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 F) F))
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    ∃ T T' : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ,
      IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ g) T ∧
      IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ (flat F σ g)) T' ∧
      ContinuousLinearMap.adjoint T = T' := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

  have hw_cont : Continuous fun y : AdelicGL2 (𝓞 F) F => NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hrpow : ∀ p : ℝ, Continuous fun y : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ p :=
    fun p => hw_cont.rpow_const fun y => Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hflat_cont : Continuous (flat F σ g) := by
    unfold flat
    exact (Complex.continuous_conj.comp (hg.comp continuous_inv)).mul (Complex.continuous_ofReal.comp (hrpow (-σ)))
  have hflat_supp : HasCompactSupport (flat F σ g) := by
    refine HasCompactSupport.intro hgc.isCompact.inv ?_
    intro y hy
    have hy' : y⁻¹ ∉ tsupport g := fun h => hy (Set.mem_inv.mpr h)
    have : g y⁻¹ = 0 := image_eq_zero_of_notMem_tsupport hy'
    simp only [flat, this, map_zero, zero_mul]

  have conv_add : ∀ (h : AdelicGL2 (𝓞 F) F → ℂ), Continuous h → HasCompactSupport h →
      ∀ (φ ψ : AdelicGL2 (𝓞 F) F → ℂ), Continuous φ → Continuous ψ →
        rightConv F (φ + ψ) h = rightConv F φ h + rightConv F ψ h := by
    intro h hh hhc φ ψ hφc hψc
    funext x
    have hint : ∀ θ : AdelicGL2 (𝓞 F) F → ℂ, Continuous θ →
        Integrable (fun y => θ (x * y) * h y) (adelicGLHaar (Fin 2) (𝓞 F) F) := fun θ hθ =>
      ((hθ.comp (continuous_const.mul continuous_id)).mul hh).integrable_of_hasCompactSupport hhc.mul_left
    simp only [rightConv_apply, Pi.add_apply]
    rw [← integral_add (hint φ hφc) (hint ψ hψc)]
    congr 1
    funext y
    ring
  have conv_smul : ∀ (h : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ), rightConv F (c • φ) h = c • rightConv F φ h := by
    intro h c φ
    funext x
    simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring

  let Nc : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := contMemberSubmodule F Φ₀ ξ
  let ι : ↥Nc →ₗ[ℂ] ↥(memberSubmodule F Φ₀ ξ) := Submodule.inclusion (fun _ h => h.1)
  let L0 : ↥Nc →ₗ[ℂ] Carrier F Φ₀ σ := (toCarrier F hΦ₀ σ ξ).comp ι
  have hL0 : ∀ ψ : ↥Nc, L0 ψ = toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩ := fun ψ => rfl
  obtain ⟨Mbar, hMbar⟩ : ∃ Mbar : Submodule ℂ (Carrier F Φ₀ σ), (LinearMap.range L0).topologicalClosure = Mbar := ⟨_, rfl⟩
  have hMbar_closed : IsClosed (Mbar : Set (Carrier F Φ₀ σ)) := by
    rw [← hMbar]; exact Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace ↥Mbar := hMbar_closed.completeSpace_coe
  have hL0mem : ∀ ψ : ↥Nc, L0 ψ ∈ Mbar := fun ψ => by
    rw [← hMbar]; exact Submodule.le_topologicalClosure _ (LinearMap.mem_range_self L0 ψ)
  let e : ↥Nc →ₗ[ℂ] ↥Mbar := L0.codRestrict Mbar hL0mem
  have he_coe : ∀ ψ : ↥Nc, ((e ψ : ↥Mbar) : Carrier F Φ₀ σ) = L0 ψ := fun ψ => rfl
  have hdense : DenseRange e := by
    rw [DenseRange, Subtype.dense_iff]
    intro v hv
    have hv' : v ∈ closure ((LinearMap.range L0 : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      rw [← Submodule.topologicalClosure_coe, hMbar]; exact hv
    refine closure_mono ?_ hv'
    rintro _ ⟨ψ, rfl⟩
    exact ⟨e ψ, ⟨ψ, rfl⟩, rfl⟩
  let P : Carrier F Φ₀ σ →L[ℂ] ↥Mbar := Mbar.orthogonalProjection

  have hw_nonneg : ∀ x : AdelicGL2 (𝓞 F) F, 0 ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
    fun x => Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
  have inner_toCarrier : ∀ (a b : AdelicGL2 (𝓞 F) F → ℂ) (ha : a ∈ memberSubmodule F Φ₀ ξ) (hb : b ∈ memberSubmodule F Φ₀ ξ),
      ⟪toCarrier F hΦ₀ σ ξ ⟨a, ha⟩, toCarrier F hΦ₀ σ ξ ⟨b, hb⟩⟫_ℂ =
        ∫ x in Φ₀, b x * conj (a x) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro a b ha hb
    rw [MeasureTheory.L2.inner_def]
    have hae_a : (toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] a :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ ha)
    have hae_b : (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩ : AdelicGL2 (𝓞 F) F → ℂ) =ᵐ[weightedMeasure F Φ₀ σ] b :=
      MemLp.coeFn_toLp (memLp_weightedMeasure_of_mem F hΦ₀ σ hb)
    have h1 : ∫ x, ⟪(toCarrier F hΦ₀ σ ξ ⟨a, ha⟩ : AdelicGL2 (𝓞 F) F → ℂ) x, (toCarrier F hΦ₀ σ ξ ⟨b, hb⟩ : AdelicGL2 (𝓞 F) F → ℂ) x⟫_ℂ
          ∂(weightedMeasure F Φ₀ σ) = ∫ x, b x * conj (a x) ∂(weightedMeasure F Φ₀ σ) := by
      apply integral_congr_ae
      filter_upwards [hae_a, hae_b] with x hxa hxb
      rw [hxa, hxb, RCLike.inner_apply]
    rw [h1]
    unfold weightedMeasure
    rw [integral_withDensity_eq_integral_toReal_smul]
    · refine integral_congr_ae (ae_of_all _ fun x => ?_)
      show (ENNReal.ofReal (weight F σ x)).toReal • (b x * conj (a x)) = b x * conj (a x) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
      rw [weight_def, ENNReal.toReal_ofReal (hw_nonneg x), Complex.real_smul]
      ring
    · exact ((hrpow (-σ)).measurable).ennreal_ofReal
    · exact ae_of_all _ fun x => ENNReal.ofReal_lt_top

  have build : ∀ (h : AdelicGL2 (𝓞 F) F → ℂ), Continuous h → HasCompactSupport h →
      ∃ (Sh : ↥Mbar →L[ℂ] Carrier F Φ₀ σ) (hmaps : ∀ φ, φ ∈ contMemberSubmodule F Φ₀ ξ → rightConv F φ h ∈ contMemberSubmodule F Φ₀ ξ),
        (∀ v, Sh v ∈ Mbar) ∧
        (∀ ψ : ↥Nc, Sh (e ψ) = L0 ⟨rightConv F ψ h, hmaps ψ ψ.2⟩) ∧
        IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ h) (Sh.comp P) := by
    intro h hh hhc
    obtain ⟨C, hC0, hBh⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_norm_toCarrier_rightConv_le F hΦ₀ σ ξ hσ h hh hhc
    have hmaps : ∀ φ, φ ∈ contMemberSubmodule F Φ₀ ξ → rightConv F φ h ∈ contMemberSubmodule F Φ₀ ξ :=
      fun φ hφ => ⟨(hBh φ hφ).fst, AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport F φ hφ.2 h hh hhc⟩
    let fh : ↥Nc →ₗ[ℂ] Carrier F Φ₀ σ :=
      { toFun := fun ψ => L0 ⟨rightConv F ψ h, hmaps ψ ψ.2⟩
        map_add' := fun ψ θ => by
          rw [← map_add]
          congr 1
          apply Subtype.ext
          simp only [Submodule.coe_add]
          exact conv_add h hh hhc ψ θ ψ.2.2 θ.2.2
        map_smul' := fun c ψ => by
          rw [RingHom.id_apply, ← map_smul]
          congr 1
          apply Subtype.ext
          simp only [Submodule.coe_smul]
          exact conv_smul h c ψ }
    have hfh : ∀ ψ : ↥Nc, fh ψ = L0 ⟨rightConv F ψ h, hmaps ψ ψ.2⟩ := fun ψ => rfl
    have hbound : ∀ ψ : ↥Nc, ‖fh ψ‖ ≤ C * ‖e ψ‖ := by
      intro ψ
      rw [hfh, hL0]
      exact (hBh ψ ψ.2).snd
    let Sh : ↥Mbar →L[ℂ] Carrier F Φ₀ σ := fh.extendOfNorm e
    have hSh_e : ∀ ψ : ↥Nc, Sh (e ψ) = L0 ⟨rightConv F ψ h, hmaps ψ ψ.2⟩ := fun ψ =>
      LinearMap.extendOfNorm_eq hdense ⟨C, hbound⟩ ψ
    have hSh_mem : ∀ v, Sh v ∈ Mbar := by
      intro v
      refine hdense.induction_on v (p := fun v => Sh v ∈ Mbar) ?_ ?_
      · exact hMbar_closed.preimage Sh.continuous
      · intro ψ
        rw [hSh_e]
        exact hL0mem _
    refine ⟨Sh, hmaps, hSh_mem, hSh_e, ⟨hmaps, ?_⟩⟩
    intro φ hφ
    have hPe : P (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩) = e ⟨φ, hφ⟩ := by
      have : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩ = ((e ⟨φ, hφ⟩ : ↥Mbar) : Carrier F Φ₀ σ) := rfl
      rw [this]
      exact Submodule.orthogonalProjection_mem_subspace_eq_self _
    rw [ContinuousLinearMap.comp_apply, hPe, hSh_e]
    rfl

  obtain ⟨Sg, hmg, hSg_mem, hSg_e, hliftg⟩ := build g hg hgc
  obtain ⟨Sf, hmf, hSf_mem, hSf_e, hliftf⟩ := build (flat F σ g) hflat_cont hflat_supp
  refine ⟨Sg.comp P, Sf.comp P, hliftg, hliftf, ?_⟩

  have hcore_e : ∀ ψ θ : ↥Nc, ⟪Sf (e ψ), ((e θ : ↥Mbar) : Carrier F Φ₀ σ)⟫_ℂ = ⟪((e ψ : ↥Mbar) : Carrier F Φ₀ σ), Sg (e θ)⟫_ℂ := by
    intro ψ θ
    rw [hSf_e, hSg_e, he_coe, he_coe, hL0, hL0, hL0, hL0, inner_toCarrier, inner_toCarrier]
    have hψ' := (mem_memberSubmodule_iff' F Φ₀ ξ (ψ : AdelicGL2 (𝓞 F) F → ℂ)).mp ψ.2.1
    have hθ' := (mem_memberSubmodule_iff' F Φ₀ ξ (θ : AdelicGL2 (𝓞 F) F → ℂ)).mp θ.2.1
    exact (AutomorphicForm.adjoint_rightConv_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀ hΦ₀.subset
      hΦ₀.isFundamentalDomain ξ σ hσ (θ : AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) hθ'.1 hψ'.1 θ.2.2 ψ.2.2 hθ'.2 hψ'.2 g hg hgc).2.2.symm
  have hcore : ∀ a b : ↥Mbar, ⟪Sf a, (b : Carrier F Φ₀ σ)⟫_ℂ = ⟪(a : Carrier F Φ₀ σ), Sg b⟫_ℂ := by
    intro a b
    refine hdense.induction_on₂ (p := fun a b => ⟪Sf a, (b : Carrier F Φ₀ σ)⟫_ℂ = ⟪(a : Carrier F Φ₀ σ), Sg b⟫_ℂ) ?_ hcore_e a b
    exact isClosed_eq ((Sf.continuous.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd))
      ((continuous_subtype_val.comp continuous_fst).inner (Sg.continuous.comp continuous_snd))
  refine ((ContinuousLinearMap.eq_adjoint_iff (Sf.comp P) (Sg.comp P)).mpr ?_).symm
  intro x y
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have h1 : ⟪Sf (P x), y⟫_ℂ = ⟪Sf (P x), ((P y : ↥Mbar) : Carrier F Φ₀ σ)⟫_ℂ := by
    have hsub : y - ((P y : ↥Mbar) : Carrier F Φ₀ σ) ∈ Mbarᗮ := Submodule.sub_starProjection_mem_orthogonal y
    have := Submodule.inner_right_of_mem_orthogonal (hSf_mem (P x)) hsub
    rw [inner_sub_right, sub_eq_zero] at this
    exact this
  have h2 : ⟪x, Sg (P y)⟫_ℂ = ⟪((P x : ↥Mbar) : Carrier F Φ₀ σ), Sg (P y)⟫_ℂ := by
    have hsub : x - ((P x : ↥Mbar) : Carrier F Φ₀ σ) ∈ Mbarᗮ := Submodule.sub_starProjection_mem_orthogonal x
    have := Submodule.inner_left_of_mem_orthogonal (hSg_mem (P y)) hsub
    rw [inner_sub_left, sub_eq_zero] at this
    exact this
  rw [h1, h2]
  exact hcore (P x) (P y)

end S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightConv (solution)
