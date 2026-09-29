-- Prove2me | solution 1 for AutomorphicForm.integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e7c3767a-2d07-5f4e-b31f-ec96edd8d5f9

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_AutomorphicForm_setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 160000

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox NumberField.InfinitePlace
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

namespace Ws47
namespace INV

open NumberField.TateGlobal

variable {K : Type} [Field K] [NumberField K]

abbrev Kc (K : Type) [Field K] [NumberField K] : Type := ↥(maximalCompactAt K ∅)
noncomputable abbrev μK (K : Type) [Field K] [NumberField K] : Measure (Kc K) := maximalCompactAtHaar K ∅

theorem eq_of_glArch_eq_of_glFin_eq {a b : AdelicGL2 (𝓞 K) K}
    (hA : glArch (𝓞 K) K a = glArch (𝓞 K) K b) (hF : glFin (𝓞 K) K a = glFin (𝓞 K) K b) : a = b := by
  apply Units.ext
  ext i j
  refine Prod.ext ?_ ?_
  · have := congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing K) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing K)) i j) hA
    simpa only [glArch_apply] using this
  · have := congrArg (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) => (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j) hF
    simpa only [glFin_apply] using this

theorem glFin_eq_one_of_mem {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ maximalCompactAt K ∅) : glFin (𝓞 K) K k = 1 := by
  have h := (mem_maximalCompactAt_iff.1 hk).2
  apply Units.ext
  ext i j v
  have hv := congrArg (fun m : GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) =>
    (m : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion K v)) i j) (h v (Finset.notMem_empty v))
  simp only [finComponent_apply] at hv
  rw [hv, Units.val_one, Units.val_one, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem mul_comm_of_glArch_eq_one {u : AdelicGL2 (𝓞 K) K} (hu : glArch (𝓞 K) K u = 1) (k : Kc K) :
    u * (k : AdelicGL2 (𝓞 K) K) = (k : AdelicGL2 (𝓞 K) K) * u := by
  refine eq_of_glArch_eq_of_glFin_eq ?_ ?_
  · rw [map_mul, map_mul, hu, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_eq_one_of_mem k.2, one_mul, mul_one]

noncomputable def avg (κ : Kc K → ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(μK K)

theorem continuous_integrand {κ : Kc K → ℝ} (hκc : Continuous κ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) :
    Continuous fun p : AdelicGL2 (𝓞 K) K × Kc K => (κ p.2 : ℂ) * f (p.1 * (p.2 : AdelicGL2 (𝓞 K) K)) :=
  (Complex.continuous_ofReal.comp (hκc.comp continuous_snd)).mul
    (hf.comp (continuous_fst.mul (continuous_subtype_val.comp continuous_snd)))

theorem integrable_integrand {κ : Kc K → ℝ} (hκc : Continuous κ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (x : AdelicGL2 (𝓞 K) K) : Integrable (fun k : Kc K => (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K))) (μK K) := by
  have hc : Continuous fun k : Kc K => (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) :=
    (continuous_integrand hκc hf).comp (Continuous.prodMk_right x)
  exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)

theorem continuous_avg {κ : Kc K → ℝ} (hκc : Continuous κ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) :
    Continuous (avg κ f) := by
  set G : AdelicGL2 (𝓞 K) K → Kc K → ℂ := fun x k => (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) with hG
  have hGc : Continuous (Function.uncurry G) := continuous_integrand hκc hf
  haveI : IsProbabilityMeasure (μK K) := inferInstance
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε

  have hev : ∀ᶠ x in nhds x₀, ∀ k ∈ (Set.univ : Set (Kc K)), dist (G x k) (G x₀ k) < ε / 2 := by
    refine isCompact_univ.eventually_forall_of_forall_eventually fun k _ => ?_
    have hc : ContinuousAt (Function.uncurry G) (x₀, k) := hGc.continuousAt
    have hc' : ContinuousAt (fun z : AdelicGL2 (𝓞 K) K × Kc K => G x₀ z.2) (x₀, k) :=
      (hGc.comp (continuous_const.prodMk continuous_snd)).continuousAt
    have h1 := Metric.tendsto_nhds.1 hc (ε / 4) (by positivity)
    have h2 := Metric.tendsto_nhds.1 hc' (ε / 4) (by positivity)
    filter_upwards [h1, h2] with z hz1 hz2
    have hz1' : dist (G z.1 z.2) (G x₀ k) < ε / 4 := by simpa [Function.uncurry] using hz1
    have hz2' : dist (G x₀ z.2) (G x₀ k) < ε / 4 := by simpa using hz2
    calc dist (G z.1 z.2) (G x₀ z.2) ≤ dist (G z.1 z.2) (G x₀ k) + dist (G x₀ z.2) (G x₀ k) := dist_triangle_right _ _ _
      _ < ε / 4 + ε / 4 := add_lt_add hz1' hz2'
      _ = ε / 2 := by ring
  filter_upwards [hev] with x hx
  show dist (∫ k, G x k ∂(μK K)) (∫ k, G x₀ k ∂(μK K)) < ε
  rw [dist_eq_norm, ← integral_sub (integrable_integrand hκc hf x) (integrable_integrand hκc hf x₀)]
  have hb : ‖∫ k, (G x k - G x₀ k) ∂(μK K)‖ ≤ ε / 2 * (μK K).real Set.univ :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun k =>
      le_of_lt (by rw [← dist_eq_norm]; exact hx k (Set.mem_univ _)))
  rw [probReal_univ, mul_one] at hb
  exact lt_of_le_of_lt hb (half_lt_self hε)

theorem avg_congr {κ : Kc K → ℝ} {f g : AdelicGL2 (𝓞 K) K → ℂ} {x y : AdelicGL2 (𝓞 K) K}
    (h : ∀ k : Kc K, f (x * (k : AdelicGL2 (𝓞 K) K)) = g (y * (k : AdelicGL2 (𝓞 K) K))) : avg κ f x = avg κ g y := by
  unfold avg
  exact integral_congr_ae (Filter.Eventually.of_forall fun k => by
    show (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) = (κ k : ℂ) * g (y * (k : AdelicGL2 (𝓞 K) K))
    rw [h k])

theorem avg_const_mul (κ : Kc K → ℝ) (c : ℂ) (f : AdelicGL2 (𝓞 K) K → ℂ) (x : AdelicGL2 (𝓞 K) K) :
    avg κ (fun y => c * f y) x = c * avg κ f x := by
  unfold avg
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)

theorem avg_mul_of_glArch_eq_one (κ : Kc K → ℝ) (f : AdelicGL2 (𝓞 K) K → ℂ) {u : AdelicGL2 (𝓞 K) K}
    (hu : glArch (𝓞 K) K u = 1) (x : AdelicGL2 (𝓞 K) K) :
    avg κ f (x * u) = avg κ (fun y => f (y * u)) x :=
  avg_congr fun k => by rw [mul_assoc, mul_comm_of_glArch_eq_one hu k, ← mul_assoc]

theorem sum_avg_mul {ι : Type} (s : Finset ι) (r : ι → AdelicGL2 (𝓞 K) K) (hr : ∀ i ∈ s, glArch (𝓞 K) K (r i) = 1)
    {κ : Kc K → ℝ} (hκc : Continuous κ) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (x : AdelicGL2 (𝓞 K) K) :
    ∑ i ∈ s, avg κ f (x * r i) = avg κ (fun y => ∑ i ∈ s, f (y * r i)) x := by
  unfold avg
  rw [← integral_finsetSum]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_assoc x (r i), mul_comm_of_glArch_eq_one (hr i hi) k, ← mul_assoc]
  · intro i _
    exact integrable_integrand hκc hf (x * r i)

theorem glArch_heckeGen (v : HeightOneSpectrum (𝓞 K)) : glArch (𝓞 K) K (heckeGen (𝓞 K) K v) = 1 := by
  apply Units.ext
  ext i j
  rw [glArch_apply]
  exact heckeGenAt_fst _ i j

theorem glArch_eq_one_of_mem_U {N : Ideal (𝓞 K)} {u : AdelicGL2 (𝓞 K) K}
    (hu : u ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) : glArch (𝓞 K) K u = 1 :=
  (mem_finiteAdelicGL2Subgroup_iff K u).mp hu.2

theorem glArch_eq_one_of_mem_doubleCoset {N : Ideal (𝓞 K)} (v : HeightOneSpectrum (𝓞 K)) {x : AdelicGL2 (𝓞 K) K}
    (hx : x ∈ HeckePair.doubleCoset (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (heckeGen (𝓞 K) K v)) :
    glArch (𝓞 K) K x = 1 := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  rw [map_mul, map_mul, glArch_eq_one_of_mem_U hu, glArch_eq_one_of_mem_U hu', glArch_heckeGen, one_mul, one_mul]

theorem isIsotypicCuspFormAt_avg (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (ξ : (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (κ : Kc K → ℝ) (hκc : Continuous κ) (hκ0 : ∀ k, 0 ≤ κ k) (hκ1 : ∫ k, κ k ∂(μK K) = 1)
    {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (hφ : IsIsotypicCuspFormAt K (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ φ) :
    IsIsotypicCuspFormAt K (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ (avg κ φ) := by
  classical
  obtain ⟨⟨hauto, hcusp⟩, hKf⟩ := hφ.smoothCusp
  obtain ⟨hinv, hL2⟩ := (lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ φ).mp hauto
  have hφc : Continuous φ := hφ.continuous
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, continuous_avg hκc hφc, ?_, ?_, ?_⟩
  ·
    refine (lsXiMemberAt_iff (𝓞 K) K _ _ ξ _ _).mpr ⟨⟨fun γ x => ?_, fun z x => ?_⟩, ?_⟩
    · exact avg_congr fun k => by rw [mul_assoc]; exact hinv.left_invariant γ _
    · rw [← avg_const_mul]
      exact avg_congr fun k => by rw [mul_assoc]; exact hinv.central_transform z _
    ·
      haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
      refine ⟨(continuous_avg hκc hφc).aestronglyMeasurable, ?_⟩
      have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
      have h2' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
      rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top h2 h2']
      have hE : ∫⁻ g, ‖φ g‖ₑ ^ (2 : ℝ) ∂((adelicGLHaar (Fin 2) (𝓞 K) K).restrict Φ₀) < ⊤ := by
        have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top h2 h2' hL2.2
        simp at this ⊢
        exact this
      have hJ := AutomorphicForm.setLIntegral_nnnorm_integral_maximalCompactAtHaar_mul_sq_le_of_isFundamentalDomain
        K α β Φ₀ hΦ₀ hΦ₀s κ hκc hκ0 hκ1 φ hφc (fun γ x => hinv.left_invariant γ x)
      simp only [ENNReal.toReal_ofNat]
      refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hJ ?_)
      · refine le_of_eq (lintegral_congr fun x => ?_)
        rw [ENNReal.rpow_two, enorm_eq_nnnorm]
        rfl
      · refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) hE
        rw [ENNReal.rpow_two, enorm_eq_nnnorm]
  ·
    haveI : IsProbabilityMeasure (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) :=
      isProbabilityMeasure_cond_adelicBox K
    obtain ⟨B, hB, hsub⟩ := exists_isCompact_adelicBox_subset K
    have hνB : (ProbabilityTheory.cond (adelicAddHaar (𝓞 K) K) (adelicBox K)) Bᶜ = 0 := by
      rw [ProbabilityTheory.cond_apply (measurableSet_adelicBox K)]
      have : adelicBox K ∩ Bᶜ = ∅ := Set.eq_empty_of_forall_notMem fun x hx => hx.2 (hsub hx.1)
      rw [this, measure_empty, mul_zero]
    exact AutomorphicForm.isCuspidalFn_integral_maximalCompactAtHaar_mul_of_isCuspidalFn K _ (measure_ne_top _ _)
      B hB hνB κ hκc φ hφc hcusp
  ·
    rw [isKfSmooth_iff, FLT.SmoothVectors.isSmoothVector_iff_exists_isOpen_subgroup] at hKf ⊢
    obtain ⟨U, hUo, hU⟩ := hKf
    refine ⟨U, hUo, fun u hu => ?_⟩
    have hφu : (fun y => φ (y * (u : AdelicGL2 (𝓞 K) K))) = φ := by
      funext y
      have := congrArg (fun f => FLT.SmoothVectors.RightTranslationFn.toFun f y) (hU u hu)
      simp at this
      exact this
    refine FLT.SmoothVectors.RightTranslationFn.ext fun x => ?_
    show avg κ φ (x * (u : AdelicGL2 (𝓞 K) K)) = avg κ φ x
    rw [avg_mul_of_glArch_eq_one κ φ ((mem_finiteAdelicGL2Subgroup_iff K _).mp u.2), hφu]
  ·
    intro g u hu
    rw [avg_mul_of_glArch_eq_one κ φ (glArch_eq_one_of_mem_U hu)]
    exact avg_congr fun k => hφ.level_invariant _ u hu
  ·
    intro v hv
    obtain ⟨reps, hsys, heq⟩ := hφ.hecke_eigen v hv
    refine ⟨reps, hsys, fun g => ?_⟩
    show ∑ i, avg κ φ (g * reps i) = Ψ.a v * avg κ φ g
    rw [sum_avg_mul Finset.univ reps (fun i _ => glArch_eq_one_of_mem_doubleCoset v (hsys.mem_doubleCoset i)) hκc hφc,
      ← avg_const_mul]
    exact avg_congr fun k => heq _
  ·
    intro v hv g
    rw [← avg_const_mul]
    exact avg_congr fun k => by rw [mul_assoc]; exact hφ.central_eigen v hv _

end Ws47.INV

open Ws47.INV in

theorem solution
    (K : Type) [Field K] [NumberField K] (α β : ℝ)
    (Φ₀ : Set (AdelicGL2 (𝓞 K) K))
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 K) K).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (ξ : (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ)
    (κ : ↥(maximalCompactAt K ∅) → ℝ) (hκc : Continuous κ) (hκ0 : ∀ k, 0 ≤ κ k) (hκ1 : ∫ k, κ k ∂(maximalCompactAtHaar K ∅) = 1)
    (f : AdelicGL2 (𝓞 K) K → ℂ)
    (hf : f ∈ isotypicCuspSubmodule K
      (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ) :
    (fun x => ∫ k, (κ k : ℂ) * f (x * (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactAtHaar K ∅)) ∈ isotypicCuspSubmodule K
        (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ := by

  have key : ∀ g : AdelicGL2 (𝓞 K) K → ℂ, g ∈ isotypicCuspSubmodule K (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ →
      Continuous g ∧ Ws47.INV.avg κ g ∈ isotypicCuspSubmodule K (productionPinsOf K Φ₀
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ N S Ψ := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      exact ⟨hx.continuous, (isIsotypicCuspFormAt_avg α β Φ₀ hΦ₀ hΦ₀s ξ N S Ψ κ hκc hκ0 hκ1 hx).mem_isotypicCuspSubmodule⟩
    | zero =>
      refine ⟨continuous_const, ?_⟩
      have : Ws47.INV.avg κ (0 : AdelicGL2 (𝓞 K) K → ℂ) = 0 := by
        funext x; simp [Ws47.INV.avg]
      rw [this]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      refine ⟨hx.1.add hy.1, ?_⟩
      have : Ws47.INV.avg κ (x + y) = Ws47.INV.avg κ x + Ws47.INV.avg κ y := by
        funext g
        simp only [Ws47.INV.avg, Pi.add_apply, mul_add]
        exact integral_add (integrable_integrand hκc hx.1 g) (integrable_integrand hκc hy.1 g)
      rw [this]
      exact Submodule.add_mem _ hx.2 hy.2
    | smul c x _ hx =>
      refine ⟨continuous_const.mul hx.1, ?_⟩
      have : Ws47.INV.avg κ (c • x) = c • Ws47.INV.avg κ x := by
        funext g
        simp only [Ws47.INV.avg, Pi.smul_apply, smul_eq_mul]
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun k => by ring)
      rw [this]
      exact Submodule.smul_mem _ c hx.2
  exact (key f hf).2

end S_AutomorphicForm_integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule
end P2MW
export P2MW.S_AutomorphicForm_integral_maximalCompactAtHaar_mul_mem_isotypicCuspSubmodule (solution)
