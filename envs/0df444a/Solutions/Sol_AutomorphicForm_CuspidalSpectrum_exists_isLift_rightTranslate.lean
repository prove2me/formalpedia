-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/de102fcf-abe2-56d2-826b-47adbdb3ed24

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

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
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (y : AdelicGL2 (𝓞 F) F) :
    ∃ T T' : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ,
      IsLift F hΦ₀ σ ξ (rightTranslate F y) T ∧
      IsLift F hΦ₀ σ ξ (rightTranslate F y⁻¹) T' ∧
      ContinuousLinearMap.adjoint T =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) • T' ∧
      ‖T‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ (σ / 2) := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hw_cont : Continuous fun x : AdelicGL2 (𝓞 F) F => NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hrpow : ∀ p : ℝ, Continuous fun x : AdelicGL2 (𝓞 F) F =>
      NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ p :=
    fun p => hw_cont.rpow_const fun x => Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hcpos : ∀ w : AdelicGL2 (𝓞 F) F, 0 < NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) := fun w => NumberField.TateGlobal.ideleNorm_pos _

  have hmaps : ∀ (w : AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ), φ ∈ contMemberSubmodule F Φ₀ ξ →
      rightTranslate F w φ ∈ contMemberSubmodule F Φ₀ ξ := by
    intro w φ hφ
    obtain ⟨hlx, h2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ φ).mp hφ.1
    have hT := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀ hΦ₀.subset
      hΦ₀.isFundamentalDomain ξ σ hσ φ φ hlx hlx hφ.2 hφ.2 h2 h2 w
    refine ⟨(mem_memberSubmodule_iff' F Φ₀ ξ _).mpr ⟨⟨fun γ x => ?_, fun z x => ?_⟩, hT.1⟩,
      hφ.2.comp (continuous_id.mul continuous_const)⟩
    · show φ (globalPoints (𝓞 F) F γ * x * w) = φ (x * w)
      rw [mul_assoc]; exact hlx.left_invariant γ (x * w)
    · show φ (centralScalar (𝓞 F) F ((z : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F)ˣ) * x * w) =
        ((ξ z : ℂˣ) : ℂ) * φ (x * w)
      rw [mul_assoc]; exact hlx.central_transform z (x * w)

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

  have hpair : ∀ (w : AdelicGL2 (𝓞 F) F) (ψ θ : ↥Nc),
      ⟪toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩, toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w θ, (hmaps w θ θ.2).1⟩⟫_ℂ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ : ℝ) : ℂ) *
          ⟪toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w⁻¹ ψ, (hmaps w⁻¹ ψ ψ.2).1⟩, toCarrier F hΦ₀ σ ξ ⟨(θ : AdelicGL2 (𝓞 F) F → ℂ), θ.2.1⟩⟫_ℂ := by
    intro w ψ θ
    obtain ⟨hψlx, hψ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ (ψ : AdelicGL2 (𝓞 F) F → ℂ)).mp ψ.2.1
    obtain ⟨hθlx, hθ2⟩ := (mem_memberSubmodule_iff' F Φ₀ ξ (θ : AdelicGL2 (𝓞 F) F → ℂ)).mp θ.2.1
    have hT := AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction F α β hΦ₀.pos Φ₀ hΦ₀.subset
      hΦ₀.isFundamentalDomain ξ σ hσ (θ : AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ) hθlx hψlx θ.2.2 ψ.2.2 hθ2 hψ2 w
    rw [inner_toCarrier, inner_toCarrier]
    exact hT.2.2
  have hnormsq : ∀ (w : AdelicGL2 (𝓞 F) F) (ψ : ↥Nc),
      ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩‖ ^ 2 =
        NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ * ‖toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩‖ ^ 2 := by
    intro w ψ

    have h := hpair w ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩ ψ
    have hback : rightTranslate F w⁻¹ (rightTranslate F w (ψ : AdelicGL2 (𝓞 F) F → ℂ)) = ψ := by
      funext x; simp only [rightTranslate_apply, inv_mul_cancel_right]
    have h' : ⟪toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩,
        toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩⟫_ℂ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ : ℝ) : ℂ) *
          ⟪toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩, toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩⟫_ℂ := by
      rw [h]
      have hsub : (⟨rightTranslate F w⁻¹ (rightTranslate F w (ψ : AdelicGL2 (𝓞 F) F → ℂ)),
          (hmaps w⁻¹ _ (hmaps w ψ ψ.2)).1⟩ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2.1⟩ :=
        Subtype.ext hback
      rw [hsub]
    rw [← @inner_self_eq_norm_sq ℂ, ← @inner_self_eq_norm_sq ℂ, h', RCLike.re_to_complex, RCLike.re_to_complex,
      Complex.re_ofReal_mul]

  have build : ∀ w : AdelicGL2 (𝓞 F) F,
      ∃ (Sw : ↥Mbar →L[ℂ] Carrier F Φ₀ σ),
        (∀ v, Sw v ∈ Mbar) ∧
        (∀ ψ : ↥Nc, Sw (e ψ) = L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩) ∧
        (∀ v, ‖Sw v‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) * ‖v‖) ∧
        IsLift F hΦ₀ σ ξ (rightTranslate F w) (Sw.comp P) := by
    intro w
    let fw : ↥Nc →ₗ[ℂ] Carrier F Φ₀ σ :=
      { toFun := fun ψ => L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩
        map_add' := fun ψ θ => by
          rw [← map_add]; congr 1
        map_smul' := fun c ψ => by
          rw [RingHom.id_apply, ← map_smul]; congr 1 }
    have hfw : ∀ ψ : ↥Nc, fw ψ = L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩ := fun ψ => rfl
    have hbound : ∀ ψ : ↥Nc, ‖fw ψ‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) * ‖e ψ‖ := by
      intro ψ
      rw [hfw, hL0]
      have hsq := hnormsq w ψ
      have h0 : 0 ≤ ‖toCarrier F hΦ₀ σ ξ ⟨rightTranslate F w ψ, (hmaps w ψ ψ.2).1⟩‖ := norm_nonneg _
      have h1 : 0 ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) * ‖e ψ‖ := mul_nonneg (Real.rpow_nonneg (hcpos w).le _) (norm_nonneg _)
      refine (pow_le_pow_iff_left₀ h0 h1 two_ne_zero).mp (le_of_eq ?_)
      have hc2 : (NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2)) ^ (2 : ℕ) =
          NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ σ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hcpos w).le]
        norm_num
      rw [hsq, mul_pow, hc2]
      rfl
    let Sw : ↥Mbar →L[ℂ] Carrier F Φ₀ σ := fw.extendOfNorm e
    have hSw_e : ∀ ψ : ↥Nc, Sw (e ψ) = L0 ⟨rightTranslate F w ψ, hmaps w ψ ψ.2⟩ := fun ψ =>
      LinearMap.extendOfNorm_eq hdense ⟨_, hbound⟩ ψ
    have hSw_norm : ∀ v, ‖Sw v‖ ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det w) ^ (σ / 2) * ‖v‖ := fun v =>
      LinearMap.norm_extendOfNorm_apply_le hdense _ hbound v
    have hSw_mem : ∀ v, Sw v ∈ Mbar := by
      intro v
      refine hdense.induction_on v (p := fun v => Sw v ∈ Mbar) ?_ ?_
      · exact hMbar_closed.preimage Sw.continuous
      · intro ψ
        rw [hSw_e]
        exact hL0mem _
    refine ⟨Sw, hSw_mem, hSw_e, hSw_norm, ⟨hmaps w, ?_⟩⟩
    intro φ hφ
    have hPe : P (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩) = e ⟨φ, hφ⟩ := by
      have : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1⟩ = ((e ⟨φ, hφ⟩ : ↥Mbar) : Carrier F Φ₀ σ) := rfl
      rw [this]
      exact Submodule.orthogonalProjection_mem_subspace_eq_self _
    rw [ContinuousLinearMap.comp_apply, hPe, hSw_e]
    rfl

  obtain ⟨Sy, hSy_mem, hSy_e, hSy_norm, hlift⟩ := build y
  obtain ⟨Si, hSi_mem, hSi_e, hSi_norm, hlift'⟩ := build y⁻¹
  refine ⟨Sy.comp P, Si.comp P, hlift, hlift', ?_, ?_⟩
  ·
    have hcore_e : ∀ ψ θ : ↥Nc, ⟪((e ψ : ↥Mbar) : Carrier F Φ₀ σ), Sy (e θ)⟫_ℂ =
        ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) * ⟪Si (e ψ), ((e θ : ↥Mbar) : Carrier F Φ₀ σ)⟫_ℂ := by
      intro ψ θ
      rw [hSy_e, hSi_e, he_coe, he_coe, hL0, hL0, hL0, hL0]
      exact hpair y ψ θ
    have hcore : ∀ a b : ↥Mbar, ⟪(a : Carrier F Φ₀ σ), Sy b⟫_ℂ = ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) * ⟪Si a, (b : Carrier F Φ₀ σ)⟫_ℂ := by
      intro a b
      refine hdense.induction_on₂ (p := fun (a b : ↥Mbar) => ⟪(a : Carrier F Φ₀ σ), Sy b⟫_ℂ = ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) * ⟪Si a, (b : Carrier F Φ₀ σ)⟫_ℂ)
        ?_ hcore_e a b
      exact isClosed_eq ((continuous_subtype_val.comp continuous_fst).inner (Sy.continuous.comp continuous_snd))
        (continuous_const.mul ((Si.continuous.comp continuous_fst).inner (continuous_subtype_val.comp continuous_snd)))
    refine ((ContinuousLinearMap.eq_adjoint_iff (((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) • Si.comp P) (Sy.comp P)).mpr ?_).symm
    intro x v
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inner_smul_left,
      Complex.conj_ofReal]
    have h1 : ⟪Si (P x), v⟫_ℂ = ⟪Si (P x), ((P v : ↥Mbar) : Carrier F Φ₀ σ)⟫_ℂ := by
      have hsub : v - ((P v : ↥Mbar) : Carrier F Φ₀ σ) ∈ Mbarᗮ := Submodule.sub_starProjection_mem_orthogonal v
      have := Submodule.inner_right_of_mem_orthogonal (hSi_mem (P x)) hsub
      rw [inner_sub_right, sub_eq_zero] at this
      exact this
    have h2 : ⟪x, Sy (P v)⟫_ℂ = ⟪((P x : ↥Mbar) : Carrier F Φ₀ σ), Sy (P v)⟫_ℂ := by
      have hsub : x - ((P x : ↥Mbar) : Carrier F Φ₀ σ) ∈ Mbarᗮ := Submodule.sub_starProjection_mem_orthogonal x
      have := Submodule.inner_left_of_mem_orthogonal (hSy_mem (P v)) hsub
      rw [inner_sub_left, sub_eq_zero] at this
      exact this
    rw [h1, h2]
    exact (hcore (P x) (P v)).symm
  ·
    refine ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (hcpos y).le _) fun v => ?_
    rw [ContinuousLinearMap.comp_apply]
    refine (hSy_norm (P v)).trans (mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (hcpos y).le _))
    exact Submodule.norm_orthogonalProjection_apply_le Mbar v

end S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_isLift_rightTranslate (solution)
