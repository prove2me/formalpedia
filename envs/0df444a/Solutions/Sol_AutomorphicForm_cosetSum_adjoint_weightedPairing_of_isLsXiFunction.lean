-- Prove2me | solution 1 for AutomorphicForm.cosetSum_adjoint_weightedPairing_of_isLsXiFunction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/8d44515a-1936-5e06-a88c-977286cbfee2

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_SiegelCovering
import Theorems.Thm_AutomorphicForm_rightTranslate_adjoint_weightedPairing_of_isLsXiFunction
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff"

set_option autoImplicit false

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace WeightedPairingCosetSum

open AutomorphicForm NumberField.TateGlobal

variable (K : Type) [Field K] [NumberField K]

private abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K

private def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)

variable {K}

private def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}

private scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K

private theorem slab_measurableSet (α β : ℝ) : MeasurableSet (slab (K := K) α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β

private theorem ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), x ∈ slab (K := K) α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurableSet α β))

private theorem wt_continuous (σ : ℝ) : Continuous (wt K σ) :=
  Complex.continuous_ofReal.comp
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne')

private theorem wt_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _

private theorem wt_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)
  · exact (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)

private theorem wt_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => by
    simp only [wt, Complex.norm_real, Real.norm_of_nonneg (wt_pos σ x).le]
    exact wt_bounds α β σ hα x hx

private theorem wt_conj (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : conj (wt K σ x) = wt K σ x := Complex.conj_ofReal _

private theorem normDet_mul (x z : AdelicGL2 (𝓞 K) K) :
    ideleNorm K (Matrix.GeneralLinearGroup.det (x * z)) =
      ideleNorm K (Matrix.GeneralLinearGroup.det x) * ideleNorm K (Matrix.GeneralLinearGroup.det z) := by
  rw [map_mul, ideleNorm_mul]

private theorem integrable_mul_of_memLp_two {ρ : Measure (AdelicGL2 (𝓞 K) K)} (a b : AdelicGL2 (𝓞 K) K → ℂ)
    (ha : AEStronglyMeasurable a ρ) (hb : AEStronglyMeasurable b ρ) (ha₂ : MemLp a 2 ρ) (hb₂ : MemLp b 2 ρ) :
    Integrable (fun x => a x * b x) ρ := by
  have ha' := (memLp_two_iff_integrable_sq_norm ha).1 ha₂
  have hb' := (memLp_two_iff_integrable_sq_norm hb).1 hb₂
  have hpt : ∀ x, ‖a x * b x‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  exact Integrable.mono' ((ha'.add hb').div_const 2) (ha.mul hb) (Filter.Eventually.of_forall fun x => hpt x)

private theorem integrable_pairing (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
    (a b : AdelicGL2 (𝓞 K) K → ℂ) (hac : Continuous a) (hbc : Continuous b)
    (ha₂ : MemLp a 2 ((μ K).restrict Φ₀)) (hb₂ : MemLp b 2 ((μ K).restrict Φ₀)) :
    Integrable (fun x => a x * conj (b x) * wt K σ x) ((μ K).restrict Φ₀) := by
  have hb₂' : MemLp (fun x => conj (b x)) 2 ((μ K).restrict Φ₀) := by
    have hm : AEStronglyMeasurable (fun x => conj (b x)) ((μ K).restrict Φ₀) :=
      (Complex.continuous_conj.comp hbc).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    simpa only [Complex.norm_conj] using (memLp_two_iff_integrable_sq_norm hbc.aestronglyMeasurable).1 hb₂
  have hab := integrable_mul_of_memLp_two a (fun x => conj (b x)) hac.aestronglyMeasurable
    (Complex.continuous_conj.comp hbc).aestronglyMeasurable ha₂ hb₂'
  have h := hab.bdd_mul (wt_continuous σ).aestronglyMeasurable (wt_ae_bound α β σ hα Φ₀ hΦ₀)
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  ring

private theorem isLsXi_translate (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (u : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (y : AdelicGL2 (𝓞 K) K) :
    IsLsXiFunction (𝓞 K) K ⊤ ξ (fun x => u (x * y)) where
  left_invariant γ x := by simp only [mul_assoc, hu.left_invariant]
  central_transform z x := by simp only [mul_assoc, hu.central_transform]

private theorem memLp_translate (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
    (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((μ K).restrict (slab α β)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
    (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
    (u : AdelicGL2 (𝓞 K) K → ℂ) (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) (huc : Continuous u)
    (hu₂ : MemLp u 2 ((μ K).restrict Φ₀)) (y : AdelicGL2 (𝓞 K) K) :
    MemLp (fun x => u (x * y)) 2 ((μ K).restrict Φ₀) :=
  (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ u u hu hu huc huc
    hu₂ hu₂ y).1

section Main

variable (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((μ K).restrict (slab α β)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
  (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : ∀ u ∈ U, ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1)
  (φ ψ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hψ : IsLsXiFunction (𝓞 K) K ⊤ ξ ψ)
  (hφc : Continuous φ) (hψc : Continuous ψ)
  (hφ₂ : MemLp φ 2 ((μ K).restrict Φ₀)) (hψ₂ : MemLp ψ 2 ((μ K).restrict Φ₀))
  (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) (hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, ψ (g * u) = ψ g)
  (gv : AdelicGL2 (𝓞 K) K)

include hα hΦ₀ hFD hσ hφ hψ hφc hψc hφ₂ hψ₂ hU hφU hψU

omit hψU in

private theorem pairing_left_U (w : AdelicGL2 (𝓞 K) K) (hw : w ∈ U) :
    ∫ x in Φ₀, φ x * conj (ψ (x * (w * gv))) * wt K σ x ∂(μ K) =
      ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * wt K σ x ∂(μ K) := by
  have hψ' : IsLsXiFunction (𝓞 K) K ⊤ ξ (fun x => ψ (x * gv)) := isLsXi_translate ξ ψ hψ gv
  have hψ'c : Continuous fun x => ψ (x * gv) := hψc.comp (continuous_id.mul continuous_const)
  have hψ'₂ := memLp_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ ψ hψ hψc hψ₂ gv
  have h := (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ
    (fun x => ψ (x * gv)) φ hψ' hφ hψ'c hφc hψ'₂ hφ₂ w).2.2
  simp only [hU w hw, Complex.ofReal_one, one_mul] at h

  have h' : ∫ x in Φ₀, ψ (x * w * gv) * conj (φ x) * wt K σ x ∂(μ K) =
      ∫ x in Φ₀, ψ (x * gv) * conj (φ x) * wt K σ x ∂(μ K) := by
    refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
    simp only [hφU x w⁻¹ (U.inv_mem hw), wt]
  have hc := congrArg (starRingEnd ℂ) h'
  rw [← integral_conj, ← integral_conj] at hc
  simp only [map_mul, Complex.conj_conj, wt_conj] at hc
  calc ∫ x in Φ₀, φ x * conj (ψ (x * (w * gv))) * wt K σ x ∂(μ K)
      = ∫ x in Φ₀, conj (ψ (x * w * gv)) * φ x * wt K σ x ∂(μ K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [mul_assoc]
        ring
    _ = ∫ x in Φ₀, conj (ψ (x * gv)) * φ x * wt K σ x ∂(μ K) := hc
    _ = ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * wt K σ x ∂(μ K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        ring

private theorem pairing_doubleCoset (u : AdelicGL2 (𝓞 K) K) (hu : u ∈ U) (u' : AdelicGL2 (𝓞 K) K) (hu' : u' ∈ U) :
    ∫ x in Φ₀, φ x * conj (ψ (x * (u * gv * u'))) * wt K σ x ∂(μ K) =
      ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * wt K σ x ∂(μ K) := by
  rw [← pairing_left_U α β hα Φ₀ hΦ₀ hFD ξ σ hσ U hU φ ψ hφ hψ hφc hψc hφ₂ hψ₂ hφU gv u hu]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [← mul_assoc, hψU (x * u * gv) u' hu']

end Main

section Reps

variable (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab α β)
  (hFD : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀ ((μ K).restrict (slab α β)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ), ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)
  (U : Subgroup (AdelicGL2 (𝓞 K) K)) (hU : ∀ u ∈ U, ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1)
  (φ ψ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hψ : IsLsXiFunction (𝓞 K) K ⊤ ξ ψ)
  (hφc : Continuous φ) (hψc : Continuous ψ)
  (hφ₂ : MemLp φ 2 ((μ K).restrict Φ₀)) (hψ₂ : MemLp ψ 2 ((μ K).restrict Φ₀))
  (hφU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g) (hψU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ U, ψ (g * u) = ψ g)
  (gv : AdelicGL2 (𝓞 K) K) (c : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))
  (hc : ∃ u ∈ U, ∃ u' ∈ U, gv⁻¹ = centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u * gv * u'))
  (r : AdelicGL2 (𝓞 K) K) (hr : ∃ u ∈ U, ∃ u' ∈ U, r = u * gv * u')

include hU hr

private theorem normDet_rep :
    ideleNorm K (Matrix.GeneralLinearGroup.det r) ^ σ = ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hr
  rw [normDet_mul, normDet_mul, Real.mul_rpow (mul_pos (ideleNorm_pos _) (ideleNorm_pos _)).le (ideleNorm_pos _).le,
    Real.mul_rpow (ideleNorm_pos _).le (ideleNorm_pos _).le, hU u hu, hU u' hu', one_mul, mul_one]

include hc

omit hU in

private theorem inv_rep :
    ∃ w ∈ U, ∃ w' ∈ U, r⁻¹ = centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (w * gv * w') := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hr
  obtain ⟨u₀, hu₀, u₀', hu₀', hgv⟩ := hc
  refine ⟨u'⁻¹ * u₀, U.mul_mem (U.inv_mem hu') hu₀, u₀' * u⁻¹, U.mul_mem hu₀' (U.inv_mem hu), ?_⟩
  have hcomm := SiegelCovering.mul_centralScalar_comm (c : (AdeleRing (𝓞 K) K)ˣ) u'⁻¹
  calc (u * gv * u')⁻¹ = u'⁻¹ * gv⁻¹ * u⁻¹ := by simp only [mul_inv_rev, mul_assoc]
    _ = u'⁻¹ * centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u₀ * gv * u₀' * u⁻¹) := by
        rw [hgv]; simp only [mul_assoc]
    _ = centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u'⁻¹ * u₀ * gv * (u₀' * u⁻¹)) := by
        rw [hcomm]; simp only [mul_assoc]

include hα hΦ₀ hFD hσ hφ hψ hφc hψc hφ₂ hψ₂ hφU hψU

private theorem term_lhs :
    ∫ x in Φ₀, φ (x * r) * conj (ψ x) * wt K σ x ∂(μ K) =
      ((ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) * conj ((ξ c : ℂˣ) : ℂ) *
        ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * wt K σ x ∂(μ K) := by
  have h := (rightTranslate_adjoint_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ φ ψ hφ hψ hφc hψc
    hφ₂ hψ₂ r).2.2
  obtain ⟨w, hw, w', hw', hr'⟩ := inv_rep U gv c hc r hr
  have hP := pairing_doubleCoset α β hα Φ₀ hΦ₀ hFD ξ σ hσ U hU φ ψ hφ hψ hφc hψc hφ₂ hψ₂ hφU hψU gv w hw w' hw'
  have hdet := normDet_rep σ U hU gv r hr

  have hin : ∀ x, φ x * conj (ψ (x * r⁻¹)) * wt K σ x =
      conj ((ξ c : ℂˣ) : ℂ) * (φ x * conj (ψ (x * (w * gv * w'))) * wt K σ x) := by
    intro x
    have e : x * (centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (w * gv * w')) =
        centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (x * (w * gv * w')) := by
      rw [← mul_assoc, SiegelCovering.mul_centralScalar_comm, mul_assoc]
    rw [hr', e, hψ.central_transform c, map_mul]
    ring
  have h' : ∫ x in Φ₀, φ (x * r) * conj (ψ x) * wt K σ x ∂(μ K) =
      ((ideleNorm K (Matrix.GeneralLinearGroup.det r) ^ σ : ℝ) : ℂ) *
        ∫ x in Φ₀, φ x * conj (ψ (x * r⁻¹)) * wt K σ x ∂(μ K) := h
  rw [h', hdet]
  rw [show (∫ x in Φ₀, φ x * conj (ψ (x * r⁻¹)) * wt K σ x ∂(μ K)) =
      conj ((ξ c : ℂˣ) : ℂ) * ∫ x in Φ₀, φ x * conj (ψ (x * (w * gv * w'))) * wt K σ x ∂(μ K) by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => hin x), hP]
  ring

omit hc in

private theorem term_rhs :
    ∫ x in Φ₀, φ x * conj (ψ (x * r)) * wt K σ x ∂(μ K) =
      ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * wt K σ x ∂(μ K) := by
  obtain ⟨u, hu, u', hu', rfl⟩ := hr
  exact pairing_doubleCoset α β hα Φ₀ hΦ₀ hFD ξ σ hσ U hU φ ψ hφ hψ hφc hψc hφ₂ hψ₂ hφU hψU gv u hu u' hu'

end Reps

end WeightedPairingCosetSum
p2m_reactivate "P2MW.S_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction.WeightedPairingCosetSum"

open WeightedPairingCosetSum NumberField.TateGlobal AutomorphicForm in
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
    (U : Subgroup (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hU : ∀ u ∈ U, NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det u) ^ σ = 1)
    (φ ψ : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ φ) (hψ : AutomorphicForm.IsLsXiFunction (𝓞 K) K ⊤ ξ ψ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ₂ : MemLp φ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hψ₂ : MemLp ψ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀))
    (hφU : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, ∀ u ∈ U, φ (g * u) = φ g)
    (hψU : ∀ g : AutomorphicForm.AdelicGL2 (𝓞 K) K, ∀ u ∈ U, ψ (g * u) = ψ g)
    (gv : AutomorphicForm.AdelicGL2 (𝓞 K) K) (n : ℕ) (reps : Fin n → AutomorphicForm.AdelicGL2 (𝓞 K) K)
    (hreps : ∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * gv * u')
    (c : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ))
    (hc : ∃ u ∈ U, ∃ u' ∈ U,
      gv⁻¹ = AutomorphicForm.centralScalar (𝓞 K) K (c : (AdeleRing (𝓞 K) K)ˣ) * (u * gv * u')) :
    MemLp (fun x => ∑ i, φ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    MemLp (fun x => ∑ i, ψ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) ∧
    ∫ x in Φ₀, (∑ i, φ (x * reps i)) * conj (ψ x) *
        ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
        ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) *
        conj ((ξ c : ℂˣ) : ℂ) *
        ∫ x in Φ₀, φ x * conj (∑ i, ψ (x * reps i)) *
          ((NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by

  have hφr : ∀ i, MemLp (fun x => φ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) := fun i =>
    WeightedPairingCosetSum.memLp_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ φ hφ hφc hφ₂ (reps i)
  have hψr : ∀ i, MemLp (fun x => ψ (x * reps i)) 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) := fun i =>
    WeightedPairingCosetSum.memLp_translate α β hα Φ₀ hΦ₀ hFD ξ σ hσ ψ hψ hψc hψ₂ (reps i)
  refine ⟨memLp_finsetSum _ fun i _ => hφr i, memLp_finsetSum _ fun i _ => hψr i, ?_⟩

  have hintL : ∀ i, Integrable (fun x => φ (x * reps i) * conj (ψ x) * WeightedPairingCosetSum.wt K σ x)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) := fun i =>
    WeightedPairingCosetSum.integrable_pairing α β σ hα Φ₀ hΦ₀ _ ψ (hφc.comp (continuous_id.mul continuous_const))
      hψc (hφr i) hψ₂
  have hintR : ∀ i, Integrable (fun x => φ x * conj (ψ (x * reps i)) * WeightedPairingCosetSum.wt K σ x)
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) := fun i =>
    WeightedPairingCosetSum.integrable_pairing α β σ hα Φ₀ hΦ₀ φ _ hφc (hψc.comp (continuous_id.mul continuous_const))
      hφ₂ (hψr i)
  have hL : ∀ i, ∫ x in Φ₀, φ (x * reps i) * conj (ψ x) * WeightedPairingCosetSum.wt K σ x
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ((ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) * conj ((ξ c : ℂˣ) : ℂ) *
        ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * WeightedPairingCosetSum.wt K σ x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    fun i => WeightedPairingCosetSum.term_lhs α β hα Φ₀ hΦ₀ hFD ξ σ hσ U hU φ ψ hφ hψ hφc hψc hφ₂ hψ₂ hφU hψU gv c hc
      (reps i) (hreps i)
  have hR : ∀ i, ∫ x in Φ₀, φ x * conj (ψ (x * reps i)) * WeightedPairingCosetSum.wt K σ x
      ∂(adelicGLHaar (Fin 2) (𝓞 K) K) =
      ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * WeightedPairingCosetSum.wt K σ x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
    fun i => WeightedPairingCosetSum.term_rhs α β hα Φ₀ hΦ₀ hFD ξ σ hσ U hU φ ψ hφ hψ hφc hψc hφ₂ hψ₂ hφU hψU gv
      (reps i) (hreps i)

  calc ∫ x in Φ₀, (∑ i, φ (x * reps i)) * conj (ψ x) *
          ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)
      = ∫ x in Φ₀, ∑ i, φ (x * reps i) * conj (ψ x) * WeightedPairingCosetSum.wt K σ x
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [Finset.sum_mul, WeightedPairingCosetSum.wt]
    _ = ∑ i, ∫ x in Φ₀, φ (x * reps i) * conj (ψ x) * WeightedPairingCosetSum.wt K σ x
          ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := integral_finsetSum _ fun i _ => hintL i
    _ = ∑ _i : Fin n, ((ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) * conj ((ξ c : ℂˣ) : ℂ) *
          ∫ x in Φ₀, φ x * conj (ψ (x * gv)) * WeightedPairingCosetSum.wt K σ x ∂(adelicGLHaar (Fin 2) (𝓞 K) K) :=
        Finset.sum_congr rfl fun i _ => hL i
    _ = ((ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) * conj ((ξ c : ℂˣ) : ℂ) *
          ∑ i, ∫ x in Φ₀, φ x * conj (ψ (x * reps i)) * WeightedPairingCosetSum.wt K σ x
            ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hR i]
    _ = ((ideleNorm K (Matrix.GeneralLinearGroup.det gv) ^ σ : ℝ) : ℂ) * conj ((ξ c : ℂˣ) : ℂ) *
          ∫ x in Φ₀, φ x * conj (∑ i, ψ (x * reps i)) *
            ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) := by
        congr 1
        rw [← integral_finsetSum _ fun i _ => hintR i]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [map_sum, Finset.mul_sum, Finset.sum_mul, WeightedPairingCosetSum.wt]

end
p2m_reactivate "P2MW.S_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction.WeightedPairingCosetSum"

end S_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction
end P2MW
export P2MW.S_AutomorphicForm_cosetSum_adjoint_weightedPairing_of_isLsXiFunction (solution)
