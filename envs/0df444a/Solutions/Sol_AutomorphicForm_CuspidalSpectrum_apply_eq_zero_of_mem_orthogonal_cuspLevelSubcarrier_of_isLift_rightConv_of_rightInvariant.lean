-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e706e96c-01af-5541-b66e-478837eda469

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AdelicDock_LocalEmbedding
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Theorems.Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant
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
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (N : Ideal (𝓞 F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f)
    (hfU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (fdPins F Φ₀).U N, f (x * u) = f x)
    (T : Carrier F Φ₀ σ →L[ℂ] Carrier F Φ₀ σ) (hT : IsLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) T)
    (v : Carrier F Φ₀ σ) (hv : v ∈ cuspSubcarrier F hΦ₀ σ ξ)
    (hperp : v ∈ (cuspLevelSubcarrier F hΦ₀ σ ξ N)ᗮ) :
    T v = 0 := by
  classical
  haveI hBorel : BorelSpace (AdelicGL2 (𝓞 F) F) := borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI hHaar := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI hRinv : (adelicGLHaar (Fin 2) (𝓞 F) F).IsMulRightInvariant :=
    NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ

  have hU_Kf : ∀ u ∈ (fdPins F Φ₀).U N, u ∈ finiteAdelicGL2Subgroup F := fun u hu => (Subgroup.mem_inf.mp hu).2
  have hU_lvl : ∀ u ∈ (fdPins F Φ₀).U N, glFin (𝓞 F) F u ∈ finiteLevelOne (𝓞 F) F N := fun u hu => (Subgroup.mem_inf.mp hu).1
  have hdet1 : ∀ u ∈ (fdPins F Φ₀).U N, NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by
    intro u hu
    rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult F u
      (mem_finiteIntegralGL2_iff.mpr ⟨(hU_lvl u hu).1.integral, (hU_lvl u hu).2.integral⟩)]
    refine Finset.prod_eq_one fun w _ => ?_
    have h1 : NumberField.AdelicVolume.archDetNorm w u = 1 := by
      unfold NumberField.AdelicVolume.archDetNorm
      rw [(mem_finiteAdelicGL2Subgroup_iff F u).mp (hU_Kf u hu), map_one, Units.val_one, Matrix.det_one, norm_one]
    rw [h1, one_pow]

  set K : Set ↥(finiteAdelicGL2Subgroup F) := {k | (k : AdelicGL2 (𝓞 F) F) ∈ (fdPins F Φ₀).U N} with hK
  have hcontFE : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
    refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
    · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => AdelicDock.finMat (𝓞 F) F g i j
      exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
    · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
        AdelicDock.finMat (𝓞 F) F ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _) i j
      exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)
  let emb : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ↥(finiteAdelicGL2Subgroup F) := fun g =>
    ⟨AdelicDock.finEmbed (𝓞 F) F g, (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F g)⟩
  have hemb : Continuous emb := hcontFE.subtype_mk _
  have hKimg : K = emb '' (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
    ext k
    simp only [hK, Set.mem_setOf_eq, Set.mem_image, SetLike.mem_coe]
    constructor
    · intro hk
      refine ⟨glFin (𝓞 F) F k, hU_lvl _ hk, Subtype.ext ?_⟩

      refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
      · have h1 := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
          ((AdelicDock.glArch_finEmbed (𝓞 F) F (glFin (𝓞 F) F k)).trans ((mem_finiteAdelicGL2Subgroup_iff F _).mp k.2).symm)
        simpa only [glArch_apply] using h1
      · have h2 := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)
          (AdelicDock.glFin_finEmbed (𝓞 F) F (glFin (𝓞 F) F k))
        simpa only [glFin_apply] using h2
    · rintro ⟨g, hg, rfl⟩
      show AdelicDock.finEmbed (𝓞 F) F g ∈ (fdPins F Φ₀).U N
      exact Subgroup.mem_inf.mpr ⟨(AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F g).mpr hg,
        (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F g)⟩
  have hKcpt : IsCompact K := by
    rw [hKimg]; exact (isCompact_finiteLevelOne (𝓞 F) F N).image hemb
  have hK_one : (1 : ↥(finiteAdelicGL2Subgroup F)) ∈ K := by
    show ((1 : ↥(finiteAdelicGL2Subgroup F)) : AdelicGL2 (𝓞 F) F) ∈ (fdPins F Φ₀).U N; exact one_mem _
  have hK_mul : ∀ a b : ↥(finiteAdelicGL2Subgroup F), a ∈ K → b ∈ K → a * b ∈ K := fun a b ha hb => by
    show ((a * b : ↥(finiteAdelicGL2Subgroup F)) : AdelicGL2 (𝓞 F) F) ∈ (fdPins F Φ₀).U N; exact mul_mem ha hb
  have hK_inv : ∀ a : ↥(finiteAdelicGL2Subgroup F), a ∈ K → a⁻¹ ∈ K := fun a ha => by
    show ((a⁻¹ : ↥(finiteAdelicGL2Subgroup F)) : AdelicGL2 (𝓞 F) F) ∈ (fdPins F Φ₀).U N; exact inv_mem ha

  have hconv_eq : ∀ u ∈ (fdPins F Φ₀).U N, ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, rightConv F (rightTranslate F u φ) f = rightConv F φ f := by
    intro u hu φ
    funext x
    simp only [rightConv_apply, rightTranslate_apply]
    have h := integral_mul_right_eq_self (μ := μ) (fun y => φ (x * y) * f y) u
    rw [← hμ, ← h]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show φ (x * y * u) * f y = φ (x * (y * u)) * f (y * u)
    rw [mul_assoc, hfU y u hu]

  have hw_nonneg : ∀ x : AdelicGL2 (𝓞 F) F, 0 ≤ NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
    fun x => Real.rpow_nonneg (NumberField.TateGlobal.ideleNorm_pos _).le _
  have hwmeas : Measurable fun x : AdelicGL2 (𝓞 F) F => ENNReal.ofReal (weight F σ x) :=
    (((NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun x =>
      Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne').measurable).ennreal_ofReal
  have inner_toCarrier : ∀ (a b : AdelicGL2 (𝓞 F) F → ℂ) (ha : a ∈ memberSubmodule F Φ₀ ξ) (hb : b ∈ memberSubmodule F Φ₀ ξ),
      ⟪toCarrier F hΦ₀ σ ξ ⟨a, ha⟩, toCarrier F hΦ₀ σ ξ ⟨b, hb⟩⟫_ℂ = pairing F Φ₀ σ b a := by
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
    unfold weightedMeasure pairing
    rw [integral_withDensity_eq_integral_toReal_smul hwmeas (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show (ENNReal.ofReal (weight F σ x)).toReal • (b x * conj (a x)) = b x * conj (a x) * ((NumberField.TateGlobal.ideleNorm F (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
    rw [weight_def, ENNReal.toReal_ofReal (hw_nonneg x), Complex.real_smul]
    ring
  set L : Submodule ℂ (Carrier F Φ₀ σ) := cuspLevelSubcarrier F hΦ₀ σ ξ N with hLdef
  have hLclosed : IsClosed (L : Set (Carrier F Φ₀ σ)) := by
    rw [hLdef]; unfold cuspLevelSubcarrier; exact Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace ↥L := hLclosed.completeSpace_coe
  let PL := L.orthogonalProjection

  have key : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
      T (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) = T ((PL (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) : Carrier F Φ₀ σ)) := by
    intro φ hφ

    have hOfin := AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact (F := F) (φ := φ) hφ.1.2 hKcpt
    set O : Finset (FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) := hOfin.toFinset with hO
    have hmemO : ∀ θ, θ ∈ O ↔ ∃ k ∈ K, k • (FLT.SmoothVectors.RightTranslationFn.mk φ :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) = θ := by
      intro θ; rw [hO, Set.Finite.mem_toFinset, Set.mem_image]
    have hO_ne : O.Nonempty := ⟨_, (hmemO _).mpr ⟨1, hK_one, rfl⟩⟩
    have hcard : (O.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hO_ne).ne'

    have hθ_tr : ∀ θ ∈ O, ∃ u ∈ (fdPins F Φ₀).U N, (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ) = rightTranslate F u φ := by
      intro θ hθ
      obtain ⟨k, hk, rfl⟩ := (hmemO θ).mp hθ
      refine ⟨(k : AdelicGL2 (𝓞 F) F), hk, funext fun x => ?_⟩
      rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul, FLT.SmoothVectors.RightTranslationFn.toFun_mk,
        rightTranslate_apply]
    have hθ_mem : ∀ θ ∈ O, (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspMemberSubmodule F Φ₀ ξ := by
      intro θ hθ
      obtain ⟨u, -, hu⟩ := hθ_tr θ hθ
      rw [hu]
      exact AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ u φ hφ

    set eφ : AdelicGL2 (𝓞 F) F → ℂ := (O.card : ℂ)⁻¹ • ∑ θ ∈ O, (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ) with heφ
    have he_mem : eφ ∈ cuspMemberSubmodule F Φ₀ ξ :=
      Submodule.smul_mem _ _ (Submodule.sum_mem _ fun θ hθ => hθ_mem θ hθ)

    have he_lvl : eφ ∈ levelInvariantSubmodule F (fdPins F Φ₀) N := by
      intro x u hu
      have hu' : (⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F)) ∈ K := hu
      simp only [heφ, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      congr 1
      refine Finset.sum_bij' (fun θ _ => (⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F)) • θ)
        (fun θ _ => (⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F))⁻¹ • θ) ?_ ?_ ?_ ?_ ?_
      · intro θ hθ
        obtain ⟨k, hk, rfl⟩ := (hmemO θ).mp hθ
        exact (hmemO _).mpr ⟨_, hK_mul _ _ hu' hk, (mul_smul _ _ _)⟩
      · intro θ hθ
        obtain ⟨k, hk, rfl⟩ := (hmemO θ).mp hθ
        exact (hmemO _).mpr ⟨_, hK_mul _ _ (hK_inv _ hu') hk, (mul_smul _ _ _)⟩
      · intro θ _; exact inv_smul_smul _ _
      · intro θ _; exact smul_inv_smul _ _
      · intro θ _
        show θ.toFun (x * u) = (((⟨u, hU_Kf u hu⟩ : ↥(finiteAdelicGL2Subgroup F)) • θ).toFun x)
        rw [Subgroup.smul_def, FLT.SmoothVectors.RightTranslationFn.toFun_smul]

    have he_coe : (⟨eφ, he_mem.1.1.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) =
        (O.card : ℂ)⁻¹ • ∑ θ ∈ O.attach, (⟨(θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ), (hθ_mem θ.1 θ.2).1.1.1⟩ : ↥(memberSubmodule F Φ₀ ξ)) := by
      apply Subtype.ext
      simp only [heφ, Submodule.coe_smul, Submodule.coe_sum]
      congr 1
      exact (Finset.sum_attach O (fun θ => (θ.toFun : AdelicGL2 (𝓞 F) F → ℂ))).symm

    have hT_orbit : ∀ θ : ↥O, T (toCarrier F hΦ₀ σ ξ ⟨(θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ), (hθ_mem θ.1 θ.2).1.1.1⟩) =
        T (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) := by
      intro θ
      obtain ⟨u, hu, hθu⟩ := hθ_tr θ.1 θ.2
      have hcθ : (θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ) ∈ contMemberSubmodule F Φ₀ ξ := ⟨(hθ_mem θ.1 θ.2).1.1.1, (hθ_mem θ.1 θ.2).2⟩
      have hcφ : φ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hφ.1.1.1, hφ.2⟩
      rw [hT.comm _ hcθ, hT.comm _ hcφ]
      congr 1
      apply Subtype.ext
      show rightConv F θ.1.toFun f = rightConv F φ f
      rw [hθu, hconv_eq u hu φ]
    have hTe : T (toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩) = T (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩) := by
      rw [he_coe, map_smul, map_sum, map_smul, map_sum]
      simp only [hT_orbit, Finset.sum_const, Finset.card_attach]
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

    have he_L : toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩ ∈ L := by
      rw [hLdef]; unfold cuspLevelSubcarrier
      exact Submodule.le_topologicalClosure _ ⟨⟨eφ, he_mem.1.1.1⟩, Submodule.mem_inf.mpr ⟨he_mem, he_lvl⟩, rfl⟩
    have hpair_orbit : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ ∈ cuspMemberSubmodule F Φ₀ ξ →
        ψ ∈ levelInvariantSubmodule F (fdPins F Φ₀) N → ∀ θ ∈ O, pairing F Φ₀ σ θ.toFun ψ = pairing F Φ₀ σ φ ψ := by
      intro ψ hψ hψU θ hθ
      obtain ⟨u, hu, hθu⟩ := hθ_tr θ hθ
      have hcφ : φ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hφ.1.1.1, hφ.2⟩
      have hcψ : ψ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hψ.1.1.1, hψ.2⟩
      have hU1 := AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_and_pairing_rightTranslate_eq_of_ideleNorm_det_eq_one
        F hΦ₀ σ ξ φ ψ hcφ hcψ u (hdet1 u hu)
      have hψinv : rightTranslate F u⁻¹ ψ = ψ := funext fun x => hψU x u⁻¹ (inv_mem hu)
      rw [hθu, hU1.2.2, hψinv]
    have he_perp : toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩ - toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩ ∈ Lᗮ := by

      have hgen : ∀ w ∈ (Submodule.map (toCarrier F hΦ₀ σ ξ)
          (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
            (cuspMemberSubmodule F Φ₀ ξ ⊓ levelInvariantSubmodule F (fdPins F Φ₀) N))),
          ⟪w, toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩ - toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩⟫_ℂ = 0 := by
        rintro _ ⟨ψ, hψ, rfl⟩
        obtain ⟨hψc, hψU⟩ := Submodule.mem_inf.mp hψ
        have hψ' : (ψ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2⟩ := rfl
        rw [inner_sub_right, hψ', he_coe, map_smul, map_sum, inner_smul_right, inner_sum, inner_toCarrier]
        have hθψ : ∀ θ ∈ O.attach, ⟪toCarrier F hΦ₀ σ ξ ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), ψ.2⟩,
            toCarrier F hΦ₀ σ ξ ⟨(θ.1.toFun : AdelicGL2 (𝓞 F) F → ℂ), (hθ_mem θ.1 θ.2).1.1.1⟩⟫_ℂ = pairing F Φ₀ σ φ ψ := by
          intro θ _
          rw [inner_toCarrier]
          exact hpair_orbit ψ hψc hψU θ.1 θ.2
        rw [Finset.sum_congr rfl hθψ, Finset.sum_const, Finset.card_attach, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hcard, one_mul, sub_self]
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hw' : w ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
          (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype
            (cuspMemberSubmodule F Φ₀ ξ ⊓ levelInvariantSubmodule F (fdPins F Φ₀) N)) : Set (Carrier F Φ₀ σ))) := by
        rw [← Submodule.topologicalClosure_coe]; rw [hLdef] at hw; exact hw
      exact closure_minimal (s := _) (t := {w : Carrier F Φ₀ σ | ⟪w, toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩ - toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩⟫_ℂ = 0})
        hgen (isClosed_eq (continuous_id.inner continuous_const) continuous_const) hw'

    have hP : ((PL (toCarrier F hΦ₀ σ ξ ⟨φ, hφ.1.1.1⟩)) : Carrier F Φ₀ σ) = toCarrier F hΦ₀ σ ξ ⟨eφ, he_mem.1.1.1⟩ :=
      Submodule.eq_starProjection_of_mem_orthogonal he_L he_perp
    rw [hP, hTe]

  have hC : IsClosed {w : Carrier F Φ₀ σ | T w = T ((PL w : ↥L) : Carrier F Φ₀ σ)} :=
    isClosed_eq T.continuous (T.continuous.comp (continuous_subtype_val.comp PL.continuous))
  have hv' : v ∈ closure ((Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ))) : Set (Carrier F Φ₀ σ)) := by
    rw [← Submodule.topologicalClosure_coe]; exact hv
  have hvC : T v = T ((PL v : ↥L) : Carrier F Φ₀ σ) := by
    refine closure_minimal ?_ hC hv'
    rintro _ ⟨ψ, hψ, rfl⟩
    have hψ' : (ψ : ↥(memberSubmodule F Φ₀ ξ)) = ⟨(ψ : AdelicGL2 (𝓞 F) F → ℂ), hψ.1.1.1⟩ := rfl
    show T (toCarrier F hΦ₀ σ ξ ψ) = T ((PL (toCarrier F hΦ₀ σ ξ ψ) : ↥L) : Carrier F Φ₀ σ)
    rw [hψ']
    exact key ψ hψ
  have hPv : PL v = 0 := Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero hperp
  rw [hvC, hPv, Submodule.coe_zero, map_zero]

end S_AutomorphicForm_CuspidalSpectrum_apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant (solution)
