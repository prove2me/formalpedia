-- Prove2me | solution 1 for AutomorphicForm.rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ed217df3-49e1-5ced-89b0-a0113d0337e8

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_FnTwist
import Definitions.Def_AutomorphicForm_SiegelCovering
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_AutomorphicForm_ideleNorm_det_globalPoints
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace WeightedPairingTranslate

open AutomorphicForm NumberField.TateGlobal NumberField.AdelicVolume

variable (K : Type) [Field K] [NumberField K]

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

private abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

private abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range

variable {K}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K

private scoped instance instRightInvμ : (μ K).IsMulRightInvariant := isMulRightInvariant_adelicGLHaar K

private theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

private theorem ideleNorm_one' : ideleNorm K (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := by
  have h := ideleNorm_mul (F := K) 1 1
  rw [mul_one] at h
  exact (mul_right_cancel₀ (ideleNorm_pos (F := K) 1).ne' (h.symm.trans (one_mul _).symm))

private theorem ideleNorm_inv' (c : (AdeleRing (𝓞 K) K)ˣ) : ideleNorm K c⁻¹ = (ideleNorm K c)⁻¹ := by
  have h := ideleNorm_mul (F := K) c c⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem normDet_central (c : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (centralScalar (𝓞 K) K c * x)) =
      ideleNorm K c ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, det_centralScalar, pow_two, ideleNorm_mul, pow_two]

private theorem normDet_global (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (globalPoints (𝓞 K) K γ * x)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) := by
  rw [normDet_mul, ideleNorm_det_globalPoints, one_mul]

omit [NumberField K] in

private theorem exists_completion_norm_eq (w : InfinitePlace K) (s : ℝ) (hs : 0 ≤ s) :
    ∃ a : w.Completion, ‖a‖ = s := by
  have hiso := InfinitePlace.Completion.isometry_extensionEmbedding w
  rcases w.isReal_or_isComplex with hw | hw
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw s
    refine ⟨a, ?_⟩
    have h1 : (InfinitePlace.Completion.extensionEmbedding w a : ℂ) = (s : ℂ) := by
      rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw, ha]
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  · obtain ⟨a, ha⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw (s : ℂ)
    refine ⟨a, ?_⟩
    rw [← hiso.norm_map_of_map_zero (map_zero _) a, ha, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]

private theorem exists_ideleNorm_eq (t : ℝ) (ht : 0 < t) : ∃ c : (AdeleRing (𝓞 K) K)ˣ, ideleNorm K c = t := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance

  obtain ⟨a, ha⟩ := exists_completion_norm_eq w (t ^ ((w.mult : ℝ)⁻¹)) (Real.rpow_nonneg ht.le _)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, norm_zero] at ha
    exact (Real.rpow_pos_of_pos ht _).ne ha
  refine ⟨archCentralUnit K w (Units.mk0 a ha0), ?_⟩
  unfold ideleNorm
  rw [AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one K _ (archCentralUnit_snd w _),
    Finset.prod_eq_single w (fun v _ hv => by rw [archCentralUnit_fst_of_ne w _ hv, norm_one, one_pow])
      (fun h => (h (Finset.mem_univ w)).elim),
    archCentralUnit_fst_self]
  show ‖a‖ ^ w.mult = t
  rw [ha, Real.rpow_inv_natCast_pow ht.le InfinitePlace.mult_ne_zero]

private theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem Γ_smul (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) : γ • x = (γ : AdelicGL2 (𝓞 K) K) * x := rfl

private theorem Γ_smul_eq (γ : Γ K) :
    ∃ γ₀ : Matrix.GeneralLinearGroup (Fin 2) K, (γ : AdelicGL2 (𝓞 K) K) = globalPoints (𝓞 K) K γ₀ := by
  obtain ⟨γ₀, h⟩ := γ.2
  exact ⟨γ₀, h.symm⟩

private theorem slab_Γ_stable (α β : ℝ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    γ • x ∈ slab K α β ↔ x ∈ slab K α β := by
  obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
  show ideleNorm K (Matrix.GeneralLinearGroup.det (_ * x)) ∈ Set.Icc α β ↔ x ∈ slab K α β
  rw [hγ₀, normDet_global]
  exact Iff.rfl

private scoped instance instMeasurableConstSMulΓ : MeasurableConstSMul (Γ K) (AdelicGL2 (𝓞 K) K) :=
  ⟨fun γ => measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)⟩

private theorem smulInvariant_restrict (S : Set (AdelicGL2 (𝓞 K) K))
    (hS : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), γ • x ∈ S ↔ x ∈ S) :
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict S) := by
  refine ⟨fun γ s hs => ?_⟩
  have hmeas : MeasurableSet ((fun x => γ • x) ⁻¹' s) := (measurable_const_mul (γ : AdelicGL2 (𝓞 K) K)) hs
  rw [Measure.restrict_apply hmeas, Measure.restrict_apply hs]
  have hset : (fun x => γ • x) ⁻¹' s ∩ S = (fun x => (γ : AdelicGL2 (𝓞 K) K) * x) ⁻¹' (s ∩ S) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [← Γ_smul γ x, hS γ x]
  rw [hset, measure_preimage_mul]

private theorem countable_K : Countable K :=
  (Module.finBasis ℚ K).equivFun.injective.countable

private theorem countable_Γ : Countable (Γ K) := by
  haveI := countable_K (K := K)
  haveI : Countable (Matrix (Fin 2) (Fin 2) K) := inferInstanceAs (Countable (Fin 2 → Fin 2 → K))
  haveI : Countable (Matrix.GeneralLinearGroup (Fin 2) K) :=
    Function.Injective.countable fun _ _ h => Units.ext h
  have h : ((Γ K : Subgroup (AdelicGL2 (𝓞 K) K)) : Set (AdelicGL2 (𝓞 K) K)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact h.to_subtype

private theorem fd_preimage (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    (f : AdelicGL2 (𝓞 K) K → AdelicGL2 (𝓞 K) K) (hf : MeasurePreserving f (μ K) (μ K))
    (hcomm : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), f (γ • x) = γ • f x) :
    IsFundamentalDomain (Γ K) (f ⁻¹' Φ₀) ((μ K).restrict (f ⁻¹' slab K α β)) :=
  hFD.preimage_of_equiv (hf.restrict_preimage (slab_measurable α β)).quasiMeasurePreserving
    (e := id) Function.bijective_id (fun γ x => hcomm γ x)

private theorem mp_mul_right (z : AdelicGL2 (𝓞 K) K) : MeasurePreserving (· * z) (μ K) (μ K) :=
  measurePreserving_mul_right (μ K) z

private theorem mp_mul_left (z : AdelicGL2 (𝓞 K) K) : MeasurePreserving (z * ·) (μ K) (μ K) :=
  measurePreserving_mul_left (μ K) z

private theorem preimage_slab_eq (α β : ℝ) (y : AdelicGL2 (𝓞 K) K) (c : (AdeleRing (𝓞 K) K)ˣ)
    (hc : ideleNorm K c ^ 2 = ideleNorm K (Matrix.GeneralLinearGroup.det y)) :
    ((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' slab K α β = (· * y⁻¹) ⁻¹' slab K α β := by
  have hy := ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det y)
  ext x
  show ideleNorm K (Matrix.GeneralLinearGroup.det ((centralScalar (𝓞 K) K c)⁻¹ * x)) ∈ Set.Icc α β ↔
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * y⁻¹)) ∈ Set.Icc α β
  rw [← map_inv, normDet_central, ideleNorm_inv', normDet_mul, map_inv, ideleNorm_inv', ← hc, inv_pow, mul_comm]

private theorem central_comm (c : (AdeleRing (𝓞 K) K)ˣ) (X : AdelicGL2 (𝓞 K) K) :
    X * (centralScalar (𝓞 K) K c)⁻¹ = (centralScalar (𝓞 K) K c)⁻¹ * X :=
  (Commute.inv_right (AutomorphicForm.SiegelCovering.mul_centralScalar_comm c X :
    Commute X (centralScalar (𝓞 K) K c))).eq

private theorem comm_right (y : AdelicGL2 (𝓞 K) K) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    (γ • x) * y⁻¹ = γ • (x * y⁻¹) := by
  simp only [Γ_smul, mul_assoc]

private theorem comm_left (c : (AdeleRing (𝓞 K) K)ˣ) (γ : Γ K) (x : AdelicGL2 (𝓞 K) K) :
    (centralScalar (𝓞 K) K c)⁻¹ * (γ • x) = γ • ((centralScalar (𝓞 K) K c)⁻¹ * x) := by
  simp only [Γ_smul]
  rw [← mul_assoc, ← central_comm, mul_assoc]

private theorem preimage_right_eq (y : AdelicGL2 (𝓞 K) K) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) :
    (fun x => x * y) ⁻¹' ((· * y⁻¹) ⁻¹' Φ₀) = Φ₀ := by
  ext x
  simp [mul_inv_cancel_right]

private theorem preimage_left_eq (z : AdelicGL2 (𝓞 K) K) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) :
    (fun x => z * x) ⁻¹' ((z⁻¹ * ·) ⁻¹' Φ₀) = Φ₀ := by
  ext x
  simp [inv_mul_cancel_left]

private theorem emb_right (y : AdelicGL2 (𝓞 K) K) : MeasurableEmbedding (fun x : AdelicGL2 (𝓞 K) K => x * y) :=
  (MeasurableEquiv.mulRight y).measurableEmbedding

private theorem emb_left (z : AdelicGL2 (𝓞 K) K) : MeasurableEmbedding (fun x : AdelicGL2 (𝓞 K) K => z * x) :=
  (MeasurableEquiv.mulLeft z).measurableEmbedding

private theorem fd_pair (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) (y : AdelicGL2 (𝓞 K) K)
    (c : (AdeleRing (𝓞 K) K)ˣ) (hc : ideleNorm K c ^ 2 = ideleNorm K (Matrix.GeneralLinearGroup.det y)) :
    IsFundamentalDomain (Γ K) ((· * y⁻¹) ⁻¹' Φ₀) ((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) ∧
    IsFundamentalDomain (Γ K) (((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀)
      ((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) ∧
    (· * y⁻¹) ⁻¹' Φ₀ ⊆ (· * y⁻¹) ⁻¹' slab K α β ∧
    ((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀ ⊆ (· * y⁻¹) ⁻¹' slab K α β ∧
    SMulInvariantMeasure (Γ K) (AdelicGL2 (𝓞 K) K) ((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) := by
  have hS' := preimage_slab_eq α β y c hc
  refine ⟨fd_preimage α β Φ₀ hFD _ (mp_mul_right y⁻¹) (comm_right y), ?_, Set.preimage_mono hΦ₀, ?_, ?_⟩
  · have h := fd_preimage α β Φ₀ hFD _ (mp_mul_left (centralScalar (𝓞 K) K c)⁻¹) (comm_left c)
    rwa [hS'] at h
  · rw [← hS']
    exact Set.preimage_mono hΦ₀
  · refine smulInvariant_restrict _ fun γ x => ?_
    show (γ • x) * y⁻¹ ∈ slab K α β ↔ x * y⁻¹ ∈ slab K α β
    rw [comm_right y γ x]
    exact slab_Γ_stable α β γ (x * y⁻¹)

private theorem setIntegral_translate (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) (y : AdelicGL2 (𝓞 K) K)
    (c : (AdeleRing (𝓞 K) K)ˣ) (hc : ideleNorm K c ^ 2 = ideleNorm K (Matrix.GeneralLinearGroup.det y))
    (H : AdelicGL2 (𝓞 K) K → ℂ)
    (hΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K), H (globalPoints (𝓞 K) K γ * x) = H x)
    (k : ℂ) (hk : ∀ x : AdelicGL2 (𝓞 K) K, H (centralScalar (𝓞 K) K c * x) = k * H x) :
    ∫ x in Φ₀, H (x * y) ∂(μ K) = k * ∫ x in Φ₀, H x ∂(μ K) := by
  obtain ⟨hFD₁, hFD₂, hsub₁, hsub₂, hinv⟩ := fd_pair α β Φ₀ hΦ₀ hFD y c hc
  haveI := hinv
  haveI := countable_Γ (K := K)
  have hHΓ : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), H (γ • x) = H x := fun γ x => by
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hΓ]
  have hr₁ : ∫ x in (· * y⁻¹) ⁻¹' Φ₀, H x ∂((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) =
      ∫ x in (· * y⁻¹) ⁻¹' Φ₀, H x ∂(μ K) := by
    rw [Measure.restrict_restrict₀ hFD₁.nullMeasurableSet, Set.inter_eq_left.mpr hsub₁]
  have hr₂ : ∫ x in ((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀, H x ∂((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) =
      ∫ x in ((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀, H x ∂(μ K) := by
    rw [Measure.restrict_restrict₀ hFD₂.nullMeasurableSet, Set.inter_eq_left.mpr hsub₂]
  calc ∫ x in Φ₀, H (x * y) ∂(μ K)
      = ∫ x in (· * y⁻¹) ⁻¹' Φ₀, H x ∂(μ K) := by
        conv_lhs => rw [← preimage_right_eq y Φ₀]
        exact (mp_mul_right y).setIntegral_preimage_emb (emb_right y) H _
    _ = ∫ x in (· * y⁻¹) ⁻¹' Φ₀, H x ∂((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) := hr₁.symm
    _ = ∫ x in ((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀, H x ∂((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) :=
        hFD₁.setIntegral_eq hFD₂ hHΓ
    _ = ∫ x in ((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀, H x ∂(μ K) := hr₂
    _ = ∫ x in Φ₀, H (centralScalar (𝓞 K) K c * x) ∂(μ K) := by
        conv_rhs => rw [← preimage_left_eq (centralScalar (𝓞 K) K c) Φ₀]
        exact ((mp_mul_left (centralScalar (𝓞 K) K c)).setIntegral_preimage_emb
          (emb_left (centralScalar (𝓞 K) K c)) H _).symm
    _ = k * ∫ x in Φ₀, H x ∂(μ K) := by
        simp only [hk]
        exact integral_const_mul k H

private theorem integrableOn_sq_central (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hF : IntegrableOn (fun x => ‖u x‖ ^ 2) Φ₀ (μ K))
    (c : (AdeleRing (𝓞 K) K)ˣ) :
    IntegrableOn (fun x => ‖u x‖ ^ 2) (((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀) (μ K) := by
  obtain ⟨z, hz⟩ : ∃ z : AdelicGL2 (𝓞 K) K, centralScalar (𝓞 K) K c = z := ⟨_, rfl⟩
  have hcen : ∀ x : AdelicGL2 (𝓞 K) K, u (z * x) = ((ξ ⟨c, Subgroup.mem_top c⟩ : ℂˣ) : ℂ) * u x := fun x => by
    have h : u (centralScalar (𝓞 K) K c * x) = ((ξ ⟨c, Subgroup.mem_top c⟩ : ℂˣ) : ℂ) * u x :=
      hu.central_transform ⟨c, Subgroup.mem_top c⟩ x
    rwa [hz] at h
  rw [hz]
  have hmp := (mp_mul_left z).restrict_preimage_emb (emb_left z) ((z⁻¹ * ·) ⁻¹' Φ₀)
  rw [preimage_left_eq z Φ₀] at hmp
  refine (hmp.integrable_comp_emb (emb_left z)).mp ?_
  refine (hF.const_mul (‖((ξ ⟨c, Subgroup.mem_top c⟩ : ℂˣ) : ℂ)‖ ^ 2)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show ‖((ξ ⟨c, Subgroup.mem_top c⟩ : ℂˣ) : ℂ)‖ ^ 2 * ‖u x‖ ^ 2 = ‖u (z * x)‖ ^ 2
  rw [hcen x, norm_mul, mul_pow]

private theorem memLp_translate (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β)
    (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (huc : Continuous u)
    (hu₂ : MemLp u 2 ((μ K).restrict Φ₀)) (y : AdelicGL2 (𝓞 K) K) :
    MemLp (fun x => u (x * y)) 2 ((μ K).restrict Φ₀) := by
  obtain ⟨c, hc⟩ := exists_ideleNorm_eq (K := K) (Real.sqrt (ideleNorm K (Matrix.GeneralLinearGroup.det y)))
    (Real.sqrt_pos.mpr (ideleNorm_pos _))
  have hc2 : ideleNorm K c ^ 2 = ideleNorm K (Matrix.GeneralLinearGroup.det y) := by
    rw [hc, Real.sq_sqrt (ideleNorm_pos _).le]
  obtain ⟨hFD₁, hFD₂, hsub₁, hsub₂, hinv⟩ := fd_pair α β Φ₀ hΦ₀ hFD y c hc2
  haveI := hinv
  haveI := countable_Γ (K := K)
  have hF : IntegrableOn (fun x => ‖u x‖ ^ 2) Φ₀ (μ K) :=
    (memLp_two_iff_integrable_sq_norm huc.aestronglyMeasurable).mp hu₂
  have hA := integrableOn_sq_central Φ₀ ξ u hu hF c
  have hinvu : ∀ (γ : Γ K) (x : AdelicGL2 (𝓞 K) K), ‖u (γ • x)‖ ^ 2 = ‖u x‖ ^ 2 := fun γ x => by
    obtain ⟨γ₀, hγ₀⟩ := Γ_smul_eq γ
    rw [Γ_smul, hγ₀, hu.left_invariant]
  have h2 : IntegrableOn (fun x => ‖u x‖ ^ 2) (((centralScalar (𝓞 K) K c)⁻¹ * ·) ⁻¹' Φ₀)
      ((μ K).restrict ((· * y⁻¹) ⁻¹' slab K α β)) := by
    unfold IntegrableOn
    rw [Measure.restrict_restrict₀ hFD₂.nullMeasurableSet, Set.inter_eq_left.mpr hsub₂]
    exact hA
  have h3 := (hFD₁.integrableOn_iff hFD₂ hinvu).mpr h2
  have hB : IntegrableOn (fun x => ‖u x‖ ^ 2) ((· * y⁻¹) ⁻¹' Φ₀) (μ K) := by
    unfold IntegrableOn at h3 ⊢
    rwa [Measure.restrict_restrict₀ hFD₁.nullMeasurableSet, Set.inter_eq_left.mpr hsub₁] at h3
  have hC : MemLp u 2 ((μ K).restrict ((· * y⁻¹) ⁻¹' Φ₀)) :=
    (memLp_two_iff_integrable_sq_norm huc.aestronglyMeasurable).mpr hB
  have hmp := (mp_mul_right y).restrict_preimage_emb (emb_right y) ((· * y⁻¹) ⁻¹' Φ₀)
  rw [preimage_right_eq y Φ₀] at hmp
  exact hC.comp_measurePreserving hmp

private theorem integrand_Γ (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (u v : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (y : AdelicGL2 (𝓞 K) K) (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AdelicGL2 (𝓞 K) K) :
    u (globalPoints (𝓞 K) K γ * x) * conj (v (globalPoints (𝓞 K) K γ * x * y⁻¹)) *
        wt K σ (globalPoints (𝓞 K) K γ * x) =
      u x * conj (v (x * y⁻¹)) * wt K σ x := by
  rw [hu.left_invariant, show globalPoints (𝓞 K) K γ * x * y⁻¹ = globalPoints (𝓞 K) K γ * (x * y⁻¹) from
    mul_assoc _ _ _, hv.left_invariant]
  unfold wt
  rw [normDet_global]

private theorem integrand_central (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u v : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (y : AdelicGL2 (𝓞 K) K) (c : (AdeleRing (𝓞 K) K)ˣ) (x : AdelicGL2 (𝓞 K) K) :
    u (centralScalar (𝓞 K) K c * x) * conj (v (centralScalar (𝓞 K) K c * x * y⁻¹)) *
        wt K σ (centralScalar (𝓞 K) K c * x) =
      1 * (u x * conj (v (x * y⁻¹)) * wt K σ x) := by
  set z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) := ⟨c, Subgroup.mem_top c⟩ with hz
  have h1 : u (centralScalar (𝓞 K) K c * x) = ((ξ z : ℂˣ) : ℂ) * u x := hu.central_transform z x
  have h2 : v (centralScalar (𝓞 K) K c * x * y⁻¹) = ((ξ z : ℂˣ) : ℂ) * v (x * y⁻¹) := by
    rw [mul_assoc]
    exact hv.central_transform z (x * y⁻¹)
  have hn := ideleNorm_pos (F := K) c
  have hd := ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det x)
  set m : ℝ := ideleNorm K c ^ σ with hm
  have hm0 : 0 < m := Real.rpow_pos_of_pos hn σ
  have hξ : ‖((ξ z : ℂˣ) : ℂ)‖ = m := hσ z
  have hmul : ((ξ z : ℂˣ) : ℂ) * conj ((ξ z : ℂˣ) : ℂ) = ((m : ℂ) * m) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hξ]
    push_cast
    ring
  have hwt : wt K σ (centralScalar (𝓞 K) K c * x) = (((m * m)⁻¹ : ℝ) : ℂ) * wt K σ x := by
    unfold wt
    rw [normDet_central, Real.mul_rpow (by positivity) hd.le, Real.rpow_neg (by positivity), pow_two,
      Real.mul_rpow hn.le hn.le]
    push_cast
    ring
  rw [h1, h2, hwt, map_mul]
  have hmne : ((m : ℂ) * m) ≠ 0 := by exact_mod_cast (mul_pos hm0 hm0).ne'
  set ζ : ℂ := ((ξ z : ℂˣ) : ℂ) with hζ
  set R : ℂ := u x * conj (v (x * y⁻¹)) * wt K σ x with hR
  calc ζ * u x * (conj ζ * conj (v (x * y⁻¹))) * ((((m * m)⁻¹ : ℝ) : ℂ) * wt K σ x)
      = (ζ * conj ζ) * (((m * m : ℝ) : ℂ))⁻¹ * R := by
        push_cast
        ring
    _ = 1 * R := by
        rw [hmul]
        push_cast
        rw [mul_inv_cancel₀ hmne]

private theorem integrand_shift (σ : ℝ) (u v : AdelicGL2 (𝓞 K) K → ℂ) (y x : AdelicGL2 (𝓞 K) K) :
    u (x * y) * conj (v x) * wt K σ x =
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
        (u (x * y) * conj (v (x * y * y⁻¹)) * wt K σ (x * y)) := by
  have ht := ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det y)
  have hd := ideleNorm_pos (F := K) (Matrix.GeneralLinearGroup.det x)
  have hne : ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos ht σ).ne'
  unfold wt
  rw [mul_inv_cancel_right, normDet_mul, Real.mul_rpow hd.le ht.le, Real.rpow_neg ht.le]
  push_cast
  field_simp

end WeightedPairingTranslate
p2m_reactivate "P2MW.S_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction.WeightedPairingTranslate"

open WeightedPairingTranslate NumberField.TateGlobal in
theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α)
    (Φ₀ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ₀ : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hFD : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u v : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hu : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ u) (hv : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ v)
    (huc : Continuous u) (hvc : Continuous v)
    (hu₂ : MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hv₂ : MemLp v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (y : AutomorphicForm.AdelicGL2 (𝓞 K) K) :
    MemLp (fun x => u (x * y)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (fun x => v (x * y⁻¹)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, u (x * y) * conj (v x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) *
        ∫ x in Φ₀, u x * conj (v (x * y⁻¹)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
  have _ := hα
  have hΦ₀' : Φ₀ ⊆ slab K α β := hΦ₀
  have hFD' : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)) := hFD
  refine ⟨memLp_translate α β Φ₀ hΦ₀' hFD' ξ u hu huc hu₂ y,
    memLp_translate α β Φ₀ hΦ₀' hFD' ξ v hv hvc hv₂ y⁻¹, ?_⟩

  obtain ⟨c, hc⟩ := exists_ideleNorm_eq (K := K) (Real.sqrt (ideleNorm K (Matrix.GeneralLinearGroup.det y)))
    (Real.sqrt_pos.mpr (ideleNorm_pos _))
  have hc2 : ideleNorm K c ^ 2 = ideleNorm K (Matrix.GeneralLinearGroup.det y) := by
    rw [hc, Real.sq_sqrt (ideleNorm_pos _).le]

  set H : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ := fun x => u x * conj (v (x * y⁻¹)) * wt K σ x with hHdef
  have hHΓ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) K) (x : AutomorphicForm.AdelicGL2 (𝓞 K) K),
      H (AutomorphicForm.globalPoints (𝓞 K) K γ * x) = H x :=
    fun γ x => integrand_Γ ξ σ u v hu hv y γ x
  have hHcen : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K, H (AutomorphicForm.centralScalar (𝓞 K) K c * x) = 1 * H x :=
    fun x => integrand_central ξ σ hσ u v hu hv y c x
  have key := setIntegral_translate α β Φ₀ hΦ₀' hFD' y c hc2 H hHΓ 1 hHcen
  rw [one_mul] at key

  have hL : ∀ x : AutomorphicForm.AdelicGL2 (𝓞 K) K,
      u (x * y) * conj (v x) * wt K σ x =
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) * H (x * y) :=
    fun x => integrand_shift σ u v y x
  change ∫ x in Φ₀, u (x * y) * conj (v x) * wt K σ x ∂(μ K) =
    ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ σ : ℝ) : ℂ) * ∫ x in Φ₀, H x ∂(μ K)
  simp_rw [hL]
  rw [integral_const_mul, key]

end
p2m_reactivate "P2MW.S_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction.WeightedPairingTranslate"

end S_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
end P2MW
export P2MW.S_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction (solution)
