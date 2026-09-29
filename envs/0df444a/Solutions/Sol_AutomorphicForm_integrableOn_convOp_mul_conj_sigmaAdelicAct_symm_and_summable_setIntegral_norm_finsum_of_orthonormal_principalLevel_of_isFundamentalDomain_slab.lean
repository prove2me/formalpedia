-- Prove2me | solution 1 for AutomorphicForm.integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/ea52888d-e55b-5c66-865b-e277f0ed15c8

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_FormalBaseChange
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_TwistedNormClasses
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_TwistedAdelicKernel
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_exists_forall_sum_setIntegral_norm_sq_rightConv_le_of_orthogonal_of_isCuspidalFn_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
import Theorems.Thm_AutomorphicForm_adjoint_rightConv_weightedPairing_of_isLsXiFunction
import Theorems.Thm_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous
import Theorems.Thm_NumberField_TateGlobal_exists_norm_apply_eq_ideleNorm_rpow
import Theorems.Thm_NumberField_TateGlobal_measurableSet_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det
import Theorems.Thm_AutomorphicForm_rightConv_rightConv_inv_eq_rightConv_rightConv
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain
import Theorems.Thm_AutomorphicForm_isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Theorems.Thm_MeasureTheory_integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
import Theorems.Thm_AutomorphicForm_integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicVolume
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
p2m_attr_erase "instance" "RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply HeckePair.IsGelfandInvolution.reindex_mk HeckePair.IsGelfandInvolution.reindexInv_mk FLT.HaarFiniteOrderGates.negContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.doublingContinuousAddEquiv_apply FLT.HaarFiniteOrderGates.invContinuousMulEquiv_apply"

set_option autoImplicit false

noncomputable section

namespace R4TCDiagSigma

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate
open MeasureTheory.Measure
open scoped ENNReal Pointwise
attribute [local instance] NumberField.AdelicHaar.glBorel

namespace Mixed

theorem integrable_mul_conj {X : Type*} [MeasurableSpace X] {ρ : Measure X} (a b : X → ℂ)
    (ha : MemLp a 2 ρ) (hb : MemLp b 2 ρ) : Integrable (fun x => a x * conj (b x)) ρ := by
  have ha' := (memLp_two_iff_integrable_sq_norm ha.1).1 ha
  have hb' := (memLp_two_iff_integrable_sq_norm hb.1).1 hb
  have hpt : ∀ x, ‖a x * conj (b x)‖ ≤ (‖a x‖ ^ 2 + ‖b x‖ ^ 2) / 2 := fun x => by
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have hm : AEStronglyMeasurable (fun x => a x * conj (b x)) ρ :=
    ha.1.mul (Complex.continuous_conj.comp_aestronglyMeasurable hb.1)
  exact Integrable.mono' ((ha'.add hb').div_const 2) hm (Filter.Eventually.of_forall hpt)

end Mixed

namespace Venue

open AutomorphicForm NumberField.TateGlobal NumberField.AdelicVolume
variable (K : Type) [Field K] [NumberField K]
def slab (α β : ℝ) : Set (AdelicGL2 (𝓞 K) K) :=
  {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}
def wt (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) : ℂ :=
  ((ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) : ℝ) : ℂ)
abbrev μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K
abbrev Γ : Subgroup (AdelicGL2 (𝓞 K) K) := (globalPoints (𝓞 K) K).range
variable {K}
scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
theorem wt_continuous (σ : ℝ) : Continuous (wt K σ) :=
  Complex.continuous_ofReal.comp
    ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne')
theorem wt_pos (σ : ℝ) (x : AdelicGL2 (𝓞 K) K) :
    0 < ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) :=
  Real.rpow_pos_of_pos (ideleNorm_pos _) _
theorem wt_bounds (α β σ : ℝ) (hα : 0 < α) (x : AdelicGL2 (𝓞 K) K)
    (hx : ideleNorm K (Matrix.GeneralLinearGroup.det x) ∈ Set.Icc α β) :
    min (α ^ (-σ)) (β ^ (-σ)) ≤ ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∧
      ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ≤ max (α ^ (-σ)) (β ^ (-σ)) := by
  obtain ⟨h1, h2⟩ := hx
  rcases le_or_gt 0 (-σ) with hs | hs
  · exact ⟨(min_le_left _ _).trans (Real.rpow_le_rpow hα.le h1 hs),
      (Real.rpow_le_rpow (ideleNorm_pos _).le h2 hs).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (Real.rpow_le_rpow_of_nonpos (ideleNorm_pos _) h2 hs.le),
      (Real.rpow_le_rpow_of_nonpos hα h1 hs.le).trans (le_max_left _ _)⟩

theorem slab_measurable (α β : ℝ) : MeasurableSet (slab K α β) :=
  measurableSet_setOf_ideleNorm_det_mem_Icc K α β
theorem ae_mem_slab (α β : ℝ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), x ∈ slab K α β :=
  ae_mono (Measure.restrict_mono hΦ₀ le_rfl) (ae_restrict_mem (slab_measurable α β))
theorem wt_ae_bound (α β σ : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hΦ₀ : Φ₀ ⊆ slab K α β) :
    ∀ᵐ x ∂((μ K).restrict Φ₀), ‖wt K σ x‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
  (ae_mem_slab α β Φ₀ hΦ₀).mono fun x hx => by
    simp only [wt, Complex.norm_real, Real.norm_of_nonneg (wt_pos σ x).le]
    exact (wt_bounds α β σ hα x hx).2

def ven (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) where
  carrier := {φ | Continuous φ ∧ IsLsXiFunction (𝓞 K) K ⊤ ξ φ ∧ MemLp φ 2 ((μ K).restrict Φ₀)}
  zero_mem' := ⟨continuous_zero, ⟨fun _ _ => rfl, fun _ _ => by simp⟩, MemLp.zero'⟩
  add_mem' := by
    rintro φ ψ ⟨hφc, hφ, hφ₂⟩ ⟨hψc, hψ, hψ₂⟩
    exact ⟨hφc.add hψc,
      ⟨fun γ g => by simp only [Pi.add_apply, hφ.left_invariant, hψ.left_invariant],
        fun z g => by simp only [Pi.add_apply, hφ.central_transform, hψ.central_transform, mul_add]⟩,
      hφ₂.add hψ₂⟩
  smul_mem' := by
    rintro c φ ⟨hφc, hφ, hφ₂⟩
    exact ⟨hφc.const_smul c,
      ⟨fun γ g => by simp only [Pi.smul_apply, hφ.left_invariant],
        fun z g => by simp only [Pi.smul_apply, smul_eq_mul, hφ.central_transform]; ring⟩,
      hφ₂.const_smul c⟩

section Venue
variable (α β : ℝ) (hα : 0 < α) (Φ₀ : Set (AdelicGL2 (𝓞 K) K)) (hαβ : α < β) (hΦ₀ : Φ₀ ⊆ slab K α β)
  (hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (σ : ℝ)
  (hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ)

def Ven (_hα : 0 < α) (_hαβ : α < β) (_hΦ₀ : Φ₀ ⊆ slab K α β)
    (_hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))) (σ : ℝ)
    (_hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ) : Type :=
  ↥(ven ξ Φ₀)
scoped instance : AddCommGroup (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  inferInstanceAs (AddCommGroup ↥(ven ξ Φ₀))
scoped instance : Module ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  inferInstanceAs (Module ℂ ↥(ven ξ Φ₀))
variable {α β hα hαβ Φ₀ hΦ₀ hFD ξ σ hσ}

def fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : AdelicGL2 (𝓞 K) K → ℂ := (φ : ↥(ven ξ Φ₀)).1
theorem fn_add (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (φ + ψ) = fn φ + fn ψ := rfl
theorem fn_smul (c : ℂ) (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (c • φ) = c • fn φ := rfl
theorem fn_zero : fn (0 : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) = 0 := rfl
theorem fn_sum {J : Type*} (s : Finset J) (φ : J → Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    fn (∑ j ∈ s, φ j) = ∑ j ∈ s, fn (φ j) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, fn_add, ih]
theorem continuous_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : Continuous (fn φ) :=
  (φ : ↥(ven ξ Φ₀)).2.1
theorem isLsXiFunction_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : IsLsXiFunction (𝓞 K) K ⊤ ξ (fn φ) :=
  (φ : ↥(ven ξ Φ₀)).2.2.1
theorem memLp_fn (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : MemLp (fn φ) 2 ((μ K).restrict Φ₀) :=
  (φ : ↥(ven ξ Φ₀)).2.2.2
theorem fn_injective : Function.Injective (fn : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ → _) :=
  fun _ _ h => Subtype.ext h

def pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : ℂ :=
  ∫ x in Φ₀, fn ψ x * conj (fn φ x) * wt K σ x ∂(μ K)
theorem integrable_pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    Integrable (fun x => fn ψ x * conj (fn φ x) * wt K σ x) ((μ K).restrict Φ₀) := by
  simpa only [mul_comm] using (Mixed.integrable_mul_conj (fn ψ) (fn φ) (memLp_fn ψ) (memLp_fn φ)).bdd_mul
    (wt_continuous σ).aestronglyMeasurable (wt_ae_bound α β σ hα Φ₀ hΦ₀)
theorem pair_add_left (φ φ' ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair (φ + φ') ψ = pair φ ψ + pair φ' ψ := by
  simp only [pair, fn_add, Pi.add_apply, map_add, mul_add, add_mul]
  exact integral_add (integrable_pair φ ψ) (integrable_pair φ' ψ)
theorem pair_smul_left (c : ℂ) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair (c • φ) ψ = conj c * pair φ ψ := by
  simp only [pair, fn_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
theorem conj_pair (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : conj (pair ψ φ) = pair φ ψ := by
  simp only [pair, ← integral_conj, map_mul, Complex.conj_conj, wt, Complex.conj_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
theorem pair_self_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    pair φ φ = ((∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) : ℝ) : ℂ) := by
  rw [pair, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [wt, Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.ofReal_pow]
theorem re_pair_self_nonneg (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : 0 ≤ RCLike.re (pair φ φ) := by
  rw [pair_self_eq, RCLike.re_to_complex, Complex.ofReal_re]
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (wt_pos σ x).le

theorem eq_zero_of_pair_self_eq_zero (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) (h : pair φ φ = 0) :
    φ = 0 := by
  by_contra hne
  have hfn : fn φ ≠ 0 := fun h0 => hne (fn_injective (h0.trans fn_zero.symm))
  exact setIntegral_mul_conj_mul_ideleNorm_det_rpow_ne_zero_of_isLsXiFunction_of_isFundamentalDomain K α β hα
    hαβ Φ₀ hΦ₀ hFD ξ σ (fn φ) (isLsXiFunction_fn φ) (continuous_fn φ) (memLp_fn φ) hfn h

@[reducible] def venCore : InnerProductSpace.Core ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) where
  inner := pair
  conj_inner_symm φ ψ := conj_pair φ ψ
  re_inner_nonneg φ := re_pair_self_nonneg φ
  add_left φ φ' ψ := pair_add_left φ φ' ψ
  smul_left φ ψ c := pair_smul_left c φ ψ
  definite φ h := eq_zero_of_pair_self_eq_zero φ h
scoped instance : NormedAddCommGroup (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ _ _ _ _ venCore
scoped instance : InnerProductSpace ℂ (Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :=
  InnerProductSpace.ofCore _
theorem norm_sq_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    ‖φ‖ ^ 2 = ∫ x in Φ₀, ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ) ∂(μ K) := by
  rw [@norm_sq_eq_re_inner ℂ]
  change RCLike.re (pair φ φ) = _
  rw [pair_self_eq, RCLike.re_to_complex, Complex.ofReal_re]

def uw (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : ℂ :=
  ∫ x in Φ₀, fn ψ x * conj (fn φ x) ∂(μ K)
theorem integrable_uw (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    Integrable (fun x => fn ψ x * conj (fn φ x)) ((μ K).restrict Φ₀) :=
  Mixed.integrable_mul_conj (fn ψ) (fn φ) (memLp_fn ψ) (memLp_fn φ)
theorem uw_add_left (φ φ' ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw (φ + φ') ψ = uw φ ψ + uw φ' ψ := by
  simp only [uw, fn_add, Pi.add_apply, map_add, mul_add]
  exact integral_add (integrable_uw φ ψ) (integrable_uw φ' ψ)
theorem uw_add_right (φ ψ ψ' : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw φ (ψ + ψ') = uw φ ψ + uw φ ψ' := by
  simp only [uw, fn_add, Pi.add_apply, add_mul]
  exact integral_add (integrable_uw φ ψ) (integrable_uw φ ψ')
theorem uw_smul_left (c : ℂ) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw (c • φ) ψ = conj c * uw φ ψ := by
  simp only [uw, fn_smul, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
theorem uw_smul_right (c : ℂ) (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw φ (c • ψ) = c * uw φ ψ := by
  simp only [uw, fn_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _
theorem uw_zero_left (ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw 0 ψ = 0 := by
  simp only [uw, fn_zero, Pi.zero_apply, map_zero, mul_zero, integral_zero]
theorem uw_zero_right (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : uw φ 0 = 0 := by
  simp only [uw, fn_zero, Pi.zero_apply, zero_mul, integral_zero]
theorem conj_uw (φ ψ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : conj (uw ψ φ) = uw φ ψ := by
  simp only [uw, ← integral_conj, map_mul, Complex.conj_conj]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
theorem uw_self_eq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    uw φ φ = ((∫ x in Φ₀, ‖fn φ x‖ ^ 2 ∂(μ K) : ℝ) : ℂ) := by
  rw [uw, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [Complex.ofReal_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem norm_sq_le_mul_uw (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    ‖φ‖ ^ 2 ≤ max (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖fn φ x‖ ^ 2 ∂(μ K) := by
  have hsq : Integrable (fun x => ‖fn φ x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm (continuous_fn φ).aestronglyMeasurable).1 (memLp_fn φ)
  rw [norm_sq_eq, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) (hsq.const_mul _) ?_
  · exact mul_nonneg (sq_nonneg _) (wt_pos σ x).le
  filter_upwards [ae_mem_slab α β Φ₀ hΦ₀] with x hx
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (wt_bounds α β σ hα x hx).2 (sq_nonneg _)

theorem mul_uw_le_norm_sq (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    min (α ^ (-σ)) (β ^ (-σ)) * ∫ x in Φ₀, ‖fn φ x‖ ^ 2 ∂(μ K) ≤ ‖φ‖ ^ 2 := by
  have hsq : Integrable (fun x => ‖fn φ x‖ ^ 2) ((μ K).restrict Φ₀) :=
    (memLp_two_iff_integrable_sq_norm (continuous_fn φ).aestronglyMeasurable).1 (memLp_fn φ)
  have hint : Integrable (fun x => ‖fn φ x‖ ^ 2 * ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ))
      ((μ K).restrict Φ₀) := by
    have hb : ∀ᵐ x ∂((μ K).restrict Φ₀),
        ‖ideleNorm K (Matrix.GeneralLinearGroup.det x) ^ (-σ)‖ ≤ max (α ^ (-σ)) (β ^ (-σ)) :=
      (wt_ae_bound α β σ hα Φ₀ hΦ₀).mono fun x hx => by simpa only [wt, Complex.norm_real] using hx
    simpa only [mul_comm] using hsq.bdd_mul
      ((continuous_ideleNorm_det K).rpow_const fun _ => Or.inl (ideleNorm_pos _).ne').aestronglyMeasurable hb
  rw [norm_sq_eq, ← integral_const_mul]
  refine integral_mono_ae (hsq.const_mul _) hint ?_
  filter_upwards [ae_mem_slab α β Φ₀ hΦ₀] with x hx
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_left (wt_bounds α β σ hα x hx).1 (sq_nonneg _)

end Venue

scoped instance secondCountable_gl : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
  NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K

section Convolution
theorem continuous_rightConv_of_hasCompactSupport (u g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u)
    (hg : Continuous g) (hgc : HasCompactSupport g) : Continuous (rightConv K u g) := by
  have hconv : rightConv K u g = fun x => ∫ y, u (x * y) * g y ∂(μ K) := funext fun x => rightConv_apply K u g x
  rw [hconv, continuous_iff_continuousAt]
  intro x₀
  obtain ⟨N, hNc, hN⟩ := exists_compact_mem_nhds x₀
  obtain ⟨M, hM⟩ := (hNc.mul (hgc : IsCompact (tsupport g))).exists_bound_of_continuousOn huc.continuousOn
  refine continuousAt_of_dominated (bound := fun y => M * ‖g y‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((huc.comp (continuous_const.mul continuous_id)).mul hg).aestronglyMeasurable
  · refine Filter.eventually_of_mem hN fun x hx => Filter.Eventually.of_forall fun y => ?_
    by_cases hy : y ∈ tsupport g
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM _ (Set.mul_mem_mul hx hy)) (norm_nonneg _)
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · exact (hg.norm.integrable_of_hasCompactSupport hgc.norm).const_mul M
  · exact Filter.Eventually.of_forall fun y =>
      ((huc.comp (continuous_id.mul continuous_const)).mul continuous_const).continuousAt
theorem isLsXiFunction_rightConv (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ) (u g : AdelicGL2 (𝓞 K) K → ℂ)
    (hu : IsLsXiFunction (𝓞 K) K ⊤ ξ u) : IsLsXiFunction (𝓞 K) K ⊤ ξ (rightConv K u g) where
  left_invariant γ x := by simp only [rightConv, mul_assoc, hu.left_invariant]
  central_transform z x := by simp only [rightConv, mul_assoc, hu.central_transform, integral_const_mul]
theorem rightConv_add_left (u v g : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) (hvc : Continuous v)
    (hg : Continuous g) (hgc : HasCompactSupport g) : rightConv K (u + v) g = rightConv K u g + rightConv K v g := by
  funext x
  simp only [rightConv, Pi.add_apply, add_mul]
  exact integral_add
    (((huc.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left)
    (((hvc.comp (continuous_const.mul continuous_id)).mul hg).integrable_of_hasCompactSupport hgc.mul_left)
theorem rightConv_smul_left (c : ℂ) (u g : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K (c • u) g = c • rightConv K u g := by
  funext x
  simp only [rightConv, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
theorem flat_continuous (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) :
    Continuous (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) :=
  (Complex.continuous_conj.comp (hg.comp continuous_inv)).mul (wt_continuous σ)
theorem flat_hasCompactSupport (σ : ℝ) (g : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g) :
    HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) *
      ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ)) := by
  have h1 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => g y⁻¹) :=
    hgc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  have h2 : HasCompactSupport (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹)) :=
    h1.comp_left (map_zero (starRingEnd ℂ))
  exact h2.mul_right

end Convolution

section Operators
variable {α β : ℝ} {hα : 0 < α} {Φ₀ : Set (AdelicGL2 (𝓞 K) K)} {hαβ : α < β} {hΦ₀ : Φ₀ ⊆ slab K α β}
  {hFD : IsFundamentalDomain (Γ K) Φ₀ ((μ K).restrict (slab K α β))}
  {ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ} {σ : ℝ}
  {hσ : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ),
    ‖((ξ z : ℂˣ) : ℂ)‖ = ideleNorm K (z : (AdeleRing (𝓞 K) K)ˣ) ^ σ}

def convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ where
  toFun φ := show ↥(ven ξ Φ₀) from
    ⟨rightConv K (fn φ) g,
      continuous_rightConv_of_hasCompactSupport (fn φ) g (continuous_fn φ) hg hgc,
      isLsXiFunction_rightConv ξ (fn φ) g (isLsXiFunction_fn φ),
      (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn φ) (fn φ)
        (isLsXiFunction_fn φ) (isLsXiFunction_fn φ) (continuous_fn φ) (continuous_fn φ) (memLp_fn φ) (memLp_fn φ)
        g hg hgc).1⟩
  map_add' φ ψ := fn_injective (by
    change rightConv K (fn φ + fn ψ) g = rightConv K (fn φ) g + rightConv K (fn ψ) g
    exact rightConv_add_left (fn φ) (fn ψ) g (continuous_fn φ) (continuous_fn ψ) hg hgc)
  map_smul' c φ := fn_injective (by
    change rightConv K (c • fn φ) g = c • rightConv K (fn φ) g
    exact rightConv_smul_left c (fn φ) g)
theorem fn_convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (φ : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) : fn (convOp g hg hgc φ) = rightConv K (fn φ) g := rfl

def convOpFlat (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ →ₗ[ℂ] Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ :=
  convOp (fun y : AdelicGL2 (𝓞 K) K => conj (g y⁻¹) * ((ideleNorm K (Matrix.GeneralLinearGroup.det y) ^ (-σ) : ℝ) : ℂ))
    (flat_continuous σ g hg) (flat_hasCompactSupport σ g hgc)

theorem inner_convOp (g : AdelicGL2 (𝓞 K) K → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g)
    (w v : Ven α β Φ₀ ξ hα hαβ hΦ₀ hFD σ hσ) :
    @inner ℂ _ _ (convOp g hg hgc w) v = @inner ℂ _ _ w (convOpFlat g hg hgc v) := by
  have h : pair v (convOp g hg hgc w) = pair (convOpFlat g hg hgc v) w :=
    (adjoint_rightConv_weightedPairing_of_isLsXiFunction K α β hα Φ₀ hΦ₀ hFD ξ σ hσ (fn w) (fn v)
      (isLsXiFunction_fn w) (isLsXiFunction_fn v) (continuous_fn w) (continuous_fn v) (memLp_fn w) (memLp_fn v)
      g hg hgc).2.2
  change pair (convOp g hg hgc w) v = pair w (convOpFlat g hg hgc v)
  rw [← conj_pair, h, conj_pair]

end Operators

end Venue
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue"

section

open MeasureTheory NumberField
open NumberField.AdelicHaar
open scoped ComplexConjugate
open MeasureTheory.Measure
open scoped ENNReal
open scoped Pointwise
attribute [local instance] NumberField.AdelicHaar.glBorel

namespace ConvolutionAssociativity

open AutomorphicForm
variable (K : Type) [Field K] [NumberField K]
private abbrev _root_.R4TCDiagSigma.ConvolutionAssociativity.μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K
p2m_export "R4TCDiagSigma.ConvolutionAssociativity" "μ"
variable {K}
scoped instance instBorelGL : BorelSpace (AdelicGL2 (𝓞 K) K) := borelSpace_glBorel (Fin 2) (𝓞 K) K
scoped instance instHaarμ : (μ K).IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
theorem hasCompactSupport_rightConv_inv (g h : AdelicGL2 (𝓞 K) K → ℂ) (hgc : HasCompactSupport g)
    (hhc : HasCompactSupport h) : HasCompactSupport (rightConv K g fun y => h y⁻¹) := by
  refine HasCompactSupport.intro ((hgc : IsCompact (tsupport g)).mul (hhc : IsCompact (tsupport h))) fun x hx => ?_
  rw [rightConv_apply]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : h y⁻¹ = 0
  · simp [hy]
  have hgx : g (x * y) = 0 := by
    by_contra hgx
    apply hx
    have : x = x * y * y⁻¹ := by group
    rw [this]
    exact Set.mul_mem_mul (subset_tsupport g hgx) (subset_tsupport h hy)
  simp [hgx]
theorem rightConv_sum_right (u : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (F : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hF : ∀ k, Continuous (F k)) (hFc : ∀ k, HasCompactSupport (F k)) :
    rightConv K u (∑ k, F k) = ∑ k, rightConv K u (F k) := by
  funext x
  simp only [rightConv, Finset.sum_apply, Finset.mul_sum]
  exact integral_finsetSum _ fun k _ =>
    ((huc.comp (continuous_const.mul continuous_id)).mul (hF k)).integrable_of_hasCompactSupport (hFc k).mul_left

theorem rightConv_eq_sum_of_forall_eq_sum (u f : AdelicGL2 (𝓞 K) K → ℂ) (huc : Continuous u) {n : ℕ}
    (g h : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (hg : ∀ k, Continuous (g k)) (hgc : ∀ k, HasCompactSupport (g k))
    (hh : ∀ k, Continuous (h k)) (hhc : ∀ k, HasCompactSupport (h k))
    (hf : ∀ x, f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x) :
    rightConv K u f = ∑ k, rightConv K (rightConv K u (h k)) (g k) := by
  have hf' : f = ∑ k, rightConv K (g k) fun y => h k y⁻¹ := by
    funext x
    rw [hf x, Finset.sum_apply]
  have hinvc : ∀ k, Continuous fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k => (hh k).comp continuous_inv
  have hinvcs : ∀ k, HasCompactSupport fun y : AdelicGL2 (𝓞 K) K => h k y⁻¹ := fun k =>
    (hhc k).comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))
  rw [hf', rightConv_sum_right u huc _
    (fun k => Venue.continuous_rightConv_of_hasCompactSupport (g k) _ (hg k) (hinvc k) (hinvcs k))
    (fun k => hasCompactSupport_rightConv_inv (g k) (h k) (hgc k) (hhc k))]
  exact Finset.sum_congr rfl fun k _ =>
    rightConv_rightConv_inv_eq_rightConv_rightConv K u (g k) (h k) huc (hg k) (hgc k) (hh k) (hhc k)

end ConvolutionAssociativity
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.ConvolutionAssociativity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.ConvolutionAssociativity"

section

open scoped InnerProductSpace ComplexConjugate

namespace Abstract
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem exists_orthonormalBasis_diag {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] (s : V → V → ℂ)
    (hadd : ∀ φ φ' ψ, s (φ + φ') ψ = s φ ψ + s φ' ψ) (hsmul : ∀ (c : ℂ) φ ψ, s (c • φ) ψ = conj c * s φ ψ)
    (hconj : ∀ φ ψ, conj (s ψ φ) = s φ ψ) :
    ∃ d : OrthonormalBasis (Fin (Module.finrank ℂ V)) ℂ V,
      (∀ p q, p ≠ q → s (d p) (d q) = 0) ∧ ∀ p, s (d p) (d p) = ((RCLike.re (s (d p) (d p)) : ℝ) : ℂ) := by
  classical

  have hadd' : ∀ φ ψ ψ', s φ (ψ + ψ') = s φ ψ + s φ ψ' := fun φ ψ ψ' => by
    rw [← hconj, hadd, map_add, hconj, hconj]
  have hsmul' : ∀ (c : ℂ) φ ψ, s φ (c • ψ) = c * s φ ψ := fun c φ ψ => by
    rw [← hconj, hsmul, map_mul, Complex.conj_conj, hconj]

  let b₀ := stdOrthonormalBasis ℂ V
  let G : V →ₗ[ℂ] V :=
    { toFun := fun v => ∑ q, s (b₀ q) v • b₀ q
      map_add' := fun v w => by
        simp only [hadd', add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by
        simp only [hsmul', RingHom.id_apply, Finset.smul_sum, smul_smul] }
  have hG : ∀ w v : V, ⟪w, G v⟫_ℂ = s w v := by
    intro w v
    show ⟪w, ∑ q, s (b₀ q) v • b₀ q⟫_ℂ = s w v
    rw [inner_sum]
    conv_rhs => rw [← b₀.sum_repr' w]
    have hexp : s (∑ q, ⟪b₀ q, w⟫_ℂ • b₀ q) v = ∑ q, conj ⟪b₀ q, w⟫_ℂ * s (b₀ q) v := by
      have hzero : ∀ ψ, s 0 ψ = 0 := fun ψ => by
        have := hsmul 0 (0 : V) ψ
        rwa [zero_smul, map_zero, zero_mul] at this
      induction (Finset.univ : Finset (Fin (Module.finrank ℂ V))) using Finset.induction_on with
      | empty => simp [hzero]
      | insert q t hq ih => rw [Finset.sum_insert hq, Finset.sum_insert hq, hadd, hsmul, ih]
    rw [hexp]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [inner_smul_right, inner_conj_symm, mul_comm]
  have hGsym : G.IsSymmetric := by
    intro v w
    rw [hG, ← inner_conj_symm, hG, hconj]
  refine ⟨hGsym.eigenvectorBasis rfl, fun p q hpq => ?_, fun p => ?_⟩
  · rw [← hG, hGsym.apply_eigenvectorBasis, inner_smul_right,
      orthonormal_iff_ite.1 (hGsym.eigenvectorBasis rfl).orthonormal p q, if_neg hpq, mul_zero]
  · have hval : s (hGsym.eigenvectorBasis rfl p) (hGsym.eigenvectorBasis rfl p) =
        ((hGsym.eigenvalues rfl p : ℝ) : ℂ) := by
      rw [← hG, hGsym.apply_eigenvectorBasis, inner_smul_right,
        orthonormal_iff_ite.1 (hGsym.eigenvectorBasis rfl).orthonormal p p, if_pos rfl, mul_one]
      try rfl
    rw [hval, RCLike.re_to_complex, Complex.ofReal_re]

end Abstract
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.ConvolutionAssociativity"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.ConvolutionAssociativity"

end R4TCDiagSigma
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.ConvolutionAssociativity P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma"

end
p2m_reactivate "P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.Venue P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma.ConvolutionAssociativity P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab.R4TCDiagSigma"

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain
open scoped ComplexConjugate InnerProductSpace ProbabilityTheory
open AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 6400000 in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (Φ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (SL : Finset (HeightOneSpectrum (𝓞 L)))
    (hSL : ∀ w w' : HeightOneSpectrum (𝓞 L),
      HeightOneSpectrum.under (𝓞 K) w = HeightOneSpectrum.under (𝓞 K) w' → (w ∈ SL ↔ w' ∈ SL))
    (N : Ideal (𝓞 L)) (hN : ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ N → w ∈ SL)
    (tysL : ArchTypeFamily L)
    (Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ι : Type) (b : ι → AdelicGL2 (𝓞 L) L → ℂ) (cls : ι → HeckeEigensystem L ℂ)
    (hb : ∀ i, cls i ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL ∧
      b i ∈ isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL (cls i) ⊓ archCutSubmodule L tysL)
    (hb₁ : ∀ i, ∫ g in Φ, b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 1)
    (hb₀ : ∀ i j, i ≠ j → ∫ g in Φ, b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 L) L) = 0)
    (hbs : ∀ π ∈ cuspClasses L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL,
      {i | cls i = π}.Finite ∧
      Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule L
        (productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun v => heckeGen (𝓞 L) L v) (adelicBox L)) ξ N SL π ⊓ archCutSubmodule L tysL)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hff : IsFactorizableTestFn L f)
    (hfU : IsBiInvariantUnder L (principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L) f)
    (hft : IsArchBiFinite L tysL f) :
    (∀ i, IntegrableOn
        (fun x => convOp L f (b i) x * conj (b i (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)))
        Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    Summable (fun Ψ : HeckeEigensystem L ℂ =>
      ∫ x in Φ₀, ‖∑ᶠ i : {i // cls i = Ψ},
          convOp L f (b i) x * conj (b i (AutomorphicForm.sigmaAdelicAct K L D σ.symm x))‖
        ∂(adelicGLHaar (Fin 2) (𝓞 L) L)) := by
  classical

  set P := productionPinsOf L Φ (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
    (fun v => heckeGen (𝓞 L) L v) (adelicBox L) with hP
  set μ : Measure (AdelicGL2 (𝓞 L) L) := adelicGLHaar (Fin 2) (𝓞 L) L with hμ
  set τ : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L := ⇑(AutomorphicForm.sigmaAdelicAct K L D σ.symm) with hτ
  have hτc : Continuous τ := AutomorphicForm.continuous_sigmaAdelicAct K L D σ.symm
  let W : HeckeEigensystem L ℂ → Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := fun Ψ =>
    isotypicCuspSubmodule L P ξ N SL Ψ ⊓ archCutSubmodule L tysL

  have hWf : ∀ Ψ, ∀ u ∈ W Ψ, Continuous u ∧ IsLsXiFunction (𝓞 L) L ⊤ ξ u ∧ MemLp u 2 (μ.restrict Φ) ∧
      IsCuspidalFn ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) unipotentGL2 u := by
    intro Ψ u hu
    have hu1 : u ∈ isotypicCuspSubmodule L P ξ N SL Ψ := (Submodule.mem_inf.1 hu).1
    by_cases hu0 : u = 0
    · subst hu0
      exact ⟨continuous_const, isLsXiFunction_zero (𝓞 L) L ⊤ ξ, MemLp.zero, fun g => constantTerm_zero _ _ g⟩
    · have hiso := AutomorphicForm.isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule L Φ
        (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L) (fun v => heckeGen (𝓞 L) L v)
        ξ N SL Ψ u hu1 hu0
      have hcusp : IsCuspAutomorphicFnAt L P ξ u := hiso.smoothCusp.1
      obtain ⟨hl, h2⟩ := (lsXiMemberAt_iff (𝓞 L) L (adelicGLHaar (Fin 2) (𝓞 L) L) ⊤ ξ Φ u).1 hcusp.1
      exact ⟨hiso.continuous, hl, h2, hcusp.2⟩

  have hRW : ∀ Ψ, ∀ u ∈ W Ψ, convOp L f u ∈ W Ψ := fun Ψ u hu =>
    AutomorphicForm.convOp_mem_isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_of_isBiInvariantUnder_of_isFundamentalDomain_slab
      L α β hα hαβ Φ hΦs hΦ ξ SL N hN tysL Ψ f hf hfc hfU hft u hu

  have hT : ∀ g : AdelicGL2 (𝓞 L) L → ℝ,
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L),
        g (globalPoints (𝓞 L) L γ * x) = g x) →
      (IntegrableOn g Φ₀ μ ↔ IntegrableOn g Φ μ) ∧ (∫ x in Φ₀, g x ∂μ = ∫ x in Φ, g x ∂μ) ∧
      (IntegrableOn (fun x => g (τ x)) Φ₀ μ ↔ IntegrableOn g Φ μ) ∧
      (∫ x in Φ₀, g (τ x) ∂μ = ∫ x in Φ, g x ∂μ) := by
    intro g hg
    obtain ⟨h1, h2, -, h4, h5⟩ :=
      AutomorphicForm.integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
        K L D σ α β Φ Φ₀ hΦs hΦ hΦ₀s hΦ₀ ℝ g hg (fun _ y => g y) (fun _ _ _ => rfl) (fun γ _ y => hg γ y)
    exact ⟨h1, h2, h4, h5⟩

  have hK2 : ∀ i, IntegrableOn (fun x => convOp L f (b i) x * conj (b i (τ x))) Φ₀ μ := by
    intro i
    obtain ⟨hc1, hl1, h21, -⟩ := hWf _ _ (hRW _ _ (hb i).2)
    obtain ⟨hc2, hl2, h22, -⟩ := hWf _ _ (hb i).2
    have hsq1 : IntegrableOn (fun x => ‖convOp L f (b i) x‖ ^ 2) Φ μ :=
      (memLp_two_iff_integrable_sq_norm h21.1).1 h21
    have hsq2 : IntegrableOn (fun x => ‖b i x‖ ^ 2) Φ μ := (memLp_two_iff_integrable_sq_norm h22.1).1 h22
    have hsq1' : IntegrableOn (fun x => ‖convOp L f (b i) x‖ ^ 2) Φ₀ μ :=
      (hT (fun x => ‖convOp L f (b i) x‖ ^ 2) (fun γ x => by simp only [hl1.left_invariant])).1.2 hsq1
    have hsq2' : IntegrableOn (fun x => ‖b i (τ x)‖ ^ 2) Φ₀ μ :=
      (hT (fun x => ‖b i x‖ ^ 2) (fun γ x => by simp only [hl2.left_invariant])).2.2.1.2 hsq2
    have hm : AEStronglyMeasurable (fun x => convOp L f (b i) x * conj (b i (τ x))) (μ.restrict Φ₀) :=
      (hc1.mul (Complex.continuous_conj.comp (hc2.comp hτc))).aestronglyMeasurable
    have hbd : Integrable (fun x => (‖convOp L f (b i) x‖ ^ 2 + ‖b i (τ x)‖ ^ 2) / 2) (μ.restrict Φ₀) :=
      (hsq1'.add hsq2').div_const 2
    refine Integrable.mono' hbd hm (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, RCLike.norm_conj]
    nlinarith [sq_nonneg (‖convOp L f (b i) x‖ - ‖b i (τ x)‖)]
  refine ⟨hK2, ?_⟩

  have hfin : ∀ Ψ, {i | cls i = Ψ}.Finite := by
    intro Ψ
    by_cases hΨ : Ψ ∈ cuspClasses L P ξ N SL
    · exact (hbs Ψ hΨ).1
    · have he : {i | cls i = Ψ} = ∅ := Set.eq_empty_of_forall_notMem fun i hi => hΨ (hi ▸ (hb i).1)
      rw [he]
      exact Set.finite_empty
  letI instF : ∀ Ψ, Fintype {i // cls i = Ψ} := fun Ψ => (hfin Ψ).fintype

  have hfs : ∀ Ψ x, (∑ᶠ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i (τ x))) =
      ∑ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i (τ x)) := fun Ψ x => finsum_eq_sum_of_fintype _
  simp_rw [hfs]

  by_cases hι : IsEmpty ι
  · have hz : (fun Ψ : HeckeEigensystem L ℂ =>
        ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i (τ x))‖ ∂μ) = 0 := by
      funext Ψ
      haveI : IsEmpty {i // cls i = Ψ} := ⟨fun i => hι.elim i.1⟩
      simp
    rw [hz]
    exact summable_zero

  obtain ⟨i₀⟩ := not_isEmpty_iff.1 hι
  have hb₀ne : ∃ g, b i₀ g ≠ 0 := by
    by_contra h
    have h' : ∀ g, b i₀ g = 0 := fun g => by_contra fun hg => h ⟨g, hg⟩
    have h0 : (fun g => b i₀ g * conj (b i₀ g)) = fun _ => 0 := funext fun g => by rw [h' g, zero_mul]
    have := hb₁ i₀
    rw [h0, integral_zero] at this
    exact zero_ne_one this
  obtain ⟨hprin, hcontχ⟩ :=
    AutomorphicForm.isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous L ξ (b i₀)
      (hWf _ _ (hb i₀).2).2.1 (hWf _ _ (hb i₀).2).1 hb₀ne
  let μξ : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ := ξ.comp Subgroup.topEquiv.symm.toMonoidHom
  obtain ⟨s, hs'⟩ := NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow L μξ (fun u => hprin u) hcontχ
  have hs : ∀ z : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ),
      ‖((ξ z : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm L (z : (AdeleRing (𝓞 L) L)ˣ) ^ s := fun z => hs' z

  have hΦ' : Φ ⊆ R4TCDiagSigma.Venue.slab L α β := hΦs
  have hFD' : IsFundamentalDomain (R4TCDiagSigma.Venue.Γ L) Φ
      ((R4TCDiagSigma.Venue.μ L).restrict (R4TCDiagSigma.Venue.slab L α β)) := hΦ
  let E : Type := R4TCDiagSigma.Venue.Ven α β Φ ξ hα hαβ hΦ' hFD' s hs
  have hWv : ∀ Ψ, W Ψ ≤ R4TCDiagSigma.Venue.ven ξ Φ :=
    fun Ψ u hu => ⟨(hWf Ψ u hu).1, (hWf Ψ u hu).2.1, (hWf Ψ u hu).2.2.1⟩

  let Bv : ι → E := fun i => show ↥(R4TCDiagSigma.Venue.ven ξ Φ) from ⟨b i, hWv _ (hb i).2⟩
  have fn_Bv : ∀ i, R4TCDiagSigma.Venue.fn (Bv i) = b i := fun i => rfl

  set mw : ℝ := min (α ^ (-s)) (β ^ (-s)) with hmw
  set Mw : ℝ := max (α ^ (-s)) (β ^ (-s)) with hMw
  have hmw0 : 0 < mw := lt_min (Real.rpow_pos_of_pos hα _) (Real.rpow_pos_of_pos (hα.trans hαβ) _)
  have hMw0 : 0 ≤ Mw := le_max_of_le_left (Real.rpow_nonneg hα.le _)

  obtain ⟨n, g, h, hg, hh, hfsum⟩ := exists_eq_sum_rightConv_of_isFactorizableTestFn L f hff
  have hgc : ∀ k, Continuous (g k) ∧ HasCompactSupport (g k) := fun k =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L (g k) (hg k)
  have hhc : ∀ k, Continuous (h k) ∧ HasCompactSupport (h k) := fun k =>
    continuous_and_hasCompactSupport_of_isFactorizableTestFn L (h k) (hh k)
  let A : Fin n → E →ₗ[ℂ] E := fun k => R4TCDiagSigma.Venue.convOp (g k) (hgc k).1 (hgc k).2
  let Adag : Fin n → E →ₗ[ℂ] E := fun k => R4TCDiagSigma.Venue.convOpFlat (g k) (hgc k).1 (hgc k).2
  let Bop : Fin n → E →ₗ[ℂ] E := fun k => R4TCDiagSigma.Venue.convOp (h k) (hhc k).1 (hhc k).2
  let TE : E →ₗ[ℂ] E := ∑ k, A k ∘ₗ Bop k
  have fn_TE : ∀ w : E, R4TCDiagSigma.Venue.fn (TE w) = convOp L f (R4TCDiagSigma.Venue.fn w) := by
    intro w
    show R4TCDiagSigma.Venue.fn ((∑ k, A k ∘ₗ Bop k) w) = rightConv L (R4TCDiagSigma.Venue.fn w) f
    rw [LinearMap.sum_apply, R4TCDiagSigma.Venue.fn_sum]
    rw [R4TCDiagSigma.ConvolutionAssociativity.rightConv_eq_sum_of_forall_eq_sum _ f
      (R4TCDiagSigma.Venue.continuous_fn w) g h
      (fun k => (hgc k).1) (fun k => (hgc k).2) (fun k => (hhc k).1) (fun k => (hhc k).2) hfsum]
    exact Finset.sum_congr rfl fun k _ => rfl
  have TE_def : ∀ w : E, TE w = ∑ k, A k (Bop k w) := fun w => by
    show (∑ k, A k ∘ₗ Bop k) w = _
    rw [LinearMap.sum_apply]
    rfl
  have hadj : ∀ k (w v : E), ⟪A k w, v⟫_ℂ = ⟪w, Adag k v⟫_ℂ :=
    fun k w v => R4TCDiagSigma.Venue.inner_convOp (g k) (hgc k).1 (hgc k).2 w v

  have hHS :=
    AutomorphicForm.exists_forall_sum_setIntegral_norm_sq_rightConv_le_of_orthogonal_of_isCuspidalFn_of_isFundamentalDomain_slab
      L α β hα hαβ Φ hΦs hΦ ξ s hs
  obtain ⟨HB, hHB⟩ : ∃ HB : Fin n → ℝ, ∀ k (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 L) L → ℂ),
      (∀ j, Continuous (e j)) → (∀ j, IsLsXiFunction (𝓞 L) L ⊤ ξ (e j)) →
      (∀ j, IsCuspidalFn ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) unipotentGL2 (e j)) →
      (∀ j, MemLp (e j) 2 (μ.restrict Φ)) →
      (∀ j j', j ≠ j' → ∫ x in Φ, e j x * conj (e j' x) ∂μ = 0) →
      (∀ j, ∫ x in Φ, ‖e j x‖ ^ 2 ∂μ ≤ 1) →
      (∑ j, ∫ x in Φ, ‖rightConv L (e j) (h k) x‖ ^ 2 ∂μ) ≤ HB k := by
    choose HB hHB using fun k => hHS (h k) (hh k)
    exact ⟨HB, fun k m e h1 h2 h3 h4 h5 h6 => (hHB k m e h1 h2 h3 h4 h5 h6).1⟩
  obtain ⟨HA, hHA⟩ : ∃ HA : Fin n → ℝ, ∀ k (m : ℕ) (e : Fin m → AdelicGL2 (𝓞 L) L → ℂ),
      (∀ j, Continuous (e j)) → (∀ j, IsLsXiFunction (𝓞 L) L ⊤ ξ (e j)) →
      (∀ j, IsCuspidalFn ((adelicAddHaar (𝓞 L) L)[|adelicBox L]) unipotentGL2 (e j)) →
      (∀ j, MemLp (e j) 2 (μ.restrict Φ)) →
      (∀ j j', j ≠ j' → ∫ x in Φ, e j x * conj (e j' x) ∂μ = 0) →
      (∀ j, ∫ x in Φ, ‖e j x‖ ^ 2 ∂μ ≤ 1) →
      (∑ j, ∫ x in Φ, ‖rightConv L (e j) (fun y => conj (g k y⁻¹) *
          ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) ≤
        HA k := by
    choose HA hHA using fun k => hHS (g k) (hg k)
    exact ⟨HA, fun k m e h1 h2 h3 h4 h5 h6 => (hHA k m e h1 h2 h3 h4 h5 h6).2⟩

  let VΨ : HeckeEigensystem L ℂ → Submodule ℂ E := fun Ψ => (W Ψ).comap (R4TCDiagSigma.Venue.ven ξ Φ).subtype
  have mem_VΨ : ∀ Ψ (w : E), w ∈ VΨ Ψ ↔ R4TCDiagSigma.Venue.fn w ∈ W Ψ := fun Ψ w => Iff.rfl
  have hBvV : ∀ i, Bv i ∈ VΨ (cls i) := fun i => (hb i).2
  have hfdW : ∀ Ψ ∈ cuspClasses L P ξ N SL, FiniteDimensional ℂ (W Ψ) := by
    intro Ψ hΨ
    have h := (hbs Ψ hΨ).2
    rw [show W Ψ = Submodule.span ℂ (b '' {i | cls i = Ψ}) from h.symm]
    exact FiniteDimensional.span_of_finite ℂ ((hbs Ψ hΨ).1.image b)
  have hfdV : ∀ Ψ ∈ cuspClasses L P ξ N SL, FiniteDimensional ℂ (VΨ Ψ) := by
    intro Ψ hΨ
    haveI := hfdW Ψ hΨ
    exact LinearEquiv.finiteDimensional (Submodule.comapSubtypeEquivOfLe (hWv Ψ)).symm
  have hdiag : ∀ Ψ (hΨ : Ψ ∈ cuspClasses L P ξ N SL),
      ∃ d : OrthonormalBasis (Fin (Module.finrank ℂ (VΨ Ψ))) ℂ (VΨ Ψ),
        (∀ p q, p ≠ q → R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d q : VΨ Ψ) : E) = 0) ∧
        ∀ p, R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E) =
          ((RCLike.re (R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E)) : ℝ) : ℂ) := by
    intro Ψ hΨ
    haveI := hfdV Ψ hΨ
    exact R4TCDiagSigma.Abstract.exists_orthonormalBasis_diag (V := VΨ Ψ)
      (fun v w => R4TCDiagSigma.Venue.uw (v : E) (w : E))
      (fun φ φ' ψ => by beta_reduce; rw [Submodule.coe_add]; exact R4TCDiagSigma.Venue.uw_add_left _ _ _)
      (fun c φ ψ => by beta_reduce; rw [Submodule.coe_smul]; exact R4TCDiagSigma.Venue.uw_smul_left _ _ _)
      (fun φ ψ => R4TCDiagSigma.Venue.conj_uw _ _)

  have key : ∀ (Ψ : HeckeEigensystem L ℂ) (hΨ : Ψ ∈ cuspClasses L P ξ N SL)
      (d : OrthonormalBasis (Fin (Module.finrank ℂ (VΨ Ψ))) ℂ (VΨ Ψ))
      (hd0 : ∀ p q, p ≠ q → R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d q : VΨ Ψ) : E) = 0)
      (hd1 : ∀ p, R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E) =
          ((RCLike.re (R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E)) : ℝ) : ℂ)),
      ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i (τ x))‖ ∂μ ≤
        ∑ k, (mw⁻¹ * ∑ p, ‖Adag k ((d p : VΨ Ψ) : E)‖ ^ 2 + ∑ i : {i // cls i = Ψ}, ‖Bop k (Bv i)‖ ^ 2) / 2 := by
    intro Ψ hΨ d hd0 hd1
    haveI := hfdV Ψ hΨ

    let ex : AdelicGL2 (𝓞 L) L → E := fun y => ∑ i : {i // cls i = Ψ}, conj (b i y) • Bv i
    let rx : AdelicGL2 (𝓞 L) L → E := fun x =>
      ∑ p, conj (R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x) • ((d p : VΨ Ψ) : E)
    have ex_def : ∀ y, ex y = ∑ i : {i // cls i = Ψ}, conj (b i y) • Bv i := fun y => rfl
    have rx_def : ∀ x, rx x = ∑ p, conj (R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x) • ((d p : VΨ Ψ) : E) :=
      fun x => rfl

    have hexV : ∀ y, ex y ∈ VΨ Ψ := fun y => by
      rw [ex_def]
      refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
      have h := hBvV i.1
      rw [i.2] at h
      exact h
    have hTexV : ∀ y, TE (ex y) ∈ VΨ Ψ := fun y => by
      rw [mem_VΨ, fn_TE]
      exact hRW Ψ _ ((mem_VΨ Ψ _).1 (hexV y))

    have hrep : ∀ (w : E), w ∈ VΨ Ψ → ∀ x, R4TCDiagSigma.Venue.fn w x = ⟪rx x, w⟫_ℂ := by
      intro w hw x
      rw [rx_def, sum_inner]
      have hsum : (∑ p, ⟪d p, (⟨w, hw⟩ : VΨ Ψ)⟫_ℂ • d p) = (⟨w, hw⟩ : VΨ Ψ) := d.sum_repr' _
      have hsum' : (∑ p, ⟪((d p : VΨ Ψ) : E), w⟫_ℂ • ((d p : VΨ Ψ) : E)) = w := by
        have := congrArg (fun v : VΨ Ψ => (v : E)) hsum
        simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner, Submodule.coe_mk] using this
      conv_lhs => rw [← hsum']
      rw [R4TCDiagSigma.Venue.fn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [R4TCDiagSigma.Venue.fn_smul, Pi.smul_apply, smul_eq_mul, inner_smul_left, Complex.conj_conj, mul_comm]

    have hker : ∀ x y, (∑ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i y)) =
        R4TCDiagSigma.Venue.fn (TE (ex y)) x := by
      intro x y
      rw [ex_def, map_sum, R4TCDiagSigma.Venue.fn_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, R4TCDiagSigma.Venue.fn_smul, Pi.smul_apply, smul_eq_mul, fn_TE, fn_Bv, mul_comm]

    have hpt : ∀ x y, ‖∑ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i y)‖ ≤
        ∑ k, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex y)‖ ^ 2) / 2 := by
      intro x y
      rw [hker x y, hrep _ (hTexV y) x, TE_def, inner_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [← inner_conj_symm, hadj, inner_conj_symm]
      calc ‖⟪Adag k (rx x), Bop k (ex y)⟫_ℂ‖ ≤ ‖Adag k (rx x)‖ * ‖Bop k (ex y)‖ := norm_inner_le_norm _ _
        _ ≤ (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex y)‖ ^ 2) / 2 := by
            nlinarith [sq_nonneg (‖Adag k (rx x)‖ - ‖Bop k (ex y)‖), norm_nonneg (Adag k (rx x)),
              norm_nonneg (Bop k (ex y))]

    have hB : ∀ k, Integrable (fun x => ‖Bop k (ex (τ x))‖ ^ 2) (μ.restrict Φ₀) ∧
        ∫ x in Φ₀, ‖Bop k (ex (τ x))‖ ^ 2 ∂μ = ∑ i : {i // cls i = Ψ}, ‖Bop k (Bv i)‖ ^ 2 := by
      intro k
      have hmap : ∀ y, Bop k (ex y) = ∑ i : {i // cls i = Ψ}, conj (b i y) • Bop k (Bv i) := fun y => by
        rw [ex_def, map_sum]
        exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
      simp_rw [hmap]
      have hP := integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
        (μ.restrict Φ) (fun i : {i // cls i = Ψ} => b i) (fun i => (hWf _ _ (hb i).2).2.2.1)
        (fun i => Bop k (Bv i)) (fun _ => 1)
        (fun i j => by
          by_cases hij : i = j
          · subst hij
            rw [if_pos rfl, hb₁]
            simp
          · rw [if_neg hij, hb₀ _ _ fun h' => hij (Subtype.ext h')])
      have hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L),
          (fun y => ‖∑ i : {i // cls i = Ψ}, conj (b i y) • Bop k (Bv i)‖ ^ 2) (globalPoints (𝓞 L) L γ * x) =
          (fun y => ‖∑ i : {i // cls i = Ψ}, conj (b i y) • Bop k (Bv i)‖ ^ 2) x := by
        intro γ x
        simp only [(hWf _ _ (hb _).2).2.1.left_invariant]
      obtain ⟨-, -, hT3, hT4⟩ := hT (fun y => ‖∑ i : {i // cls i = Ψ}, conj (b i y) • Bop k (Bv i)‖ ^ 2) hinv
      refine ⟨hT3.2 hP.1, ?_⟩
      rw [hT4, hP.2]
      simp only [one_mul]

    have hA : ∀ k, Integrable (fun x => ‖Adag k (rx x)‖ ^ 2) (μ.restrict Φ₀) ∧
        ∫ x in Φ₀, ‖Adag k (rx x)‖ ^ 2 ∂μ ≤ mw⁻¹ * ∑ p, ‖Adag k ((d p : VΨ Ψ) : E)‖ ^ 2 := by
      intro k
      have hmap : ∀ x, Adag k (rx x) =
          ∑ p, conj (R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x) • Adag k ((d p : VΨ Ψ) : E) := fun x => by
        rw [rx_def, map_sum]
        exact Finset.sum_congr rfl fun p _ => map_smul _ _ _
      simp_rw [hmap]
      have hP := integrable_norm_sq_sum_conj_smul_and_integral_eq_sum_mul_norm_sq_of_forall_integral_mul_conj_eq
        (μ.restrict Φ) (fun p => R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E)) (fun p => R4TCDiagSigma.Venue.memLp_fn _)
        (fun p => Adag k ((d p : VΨ Ψ) : E))
        (fun p => RCLike.re (R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E)))
        (fun p q => by
          by_cases hpq : p = q
          · subst hpq
            rw [if_pos rfl]
            exact hd1 p
          · rw [if_neg hpq]
            exact hd0 q p (Ne.symm hpq))
      have hinv : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L),
          (fun x => ‖∑ p, conj (R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x) • Adag k ((d p : VΨ Ψ) : E)‖ ^ 2)
            (globalPoints (𝓞 L) L γ * x) =
          (fun x => ‖∑ p, conj (R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x) • Adag k ((d p : VΨ Ψ) : E)‖ ^ 2)
            x := by
        intro γ x
        simp only [(R4TCDiagSigma.Venue.isLsXiFunction_fn _).left_invariant]
      obtain ⟨hT1, hT2, -, -⟩ :=
        hT (fun x => ‖∑ p, conj (R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x) • Adag k ((d p : VΨ Ψ) : E)‖ ^ 2) hinv
      refine ⟨hT1.2 hP.1, ?_⟩
      rw [hT2, hP.2, Finset.mul_sum]
      refine Finset.sum_le_sum fun p _ => ?_
      beta_reduce
      have h1 : RCLike.re (R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E)) =
          ∫ x in Φ, ‖R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x‖ ^ 2 ∂μ := by
        rw [R4TCDiagSigma.Venue.uw_self_eq, RCLike.re_to_complex, Complex.ofReal_re]
      have h2 : mw * ∫ x in Φ, ‖R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x‖ ^ 2 ∂μ ≤ ‖((d p : VΨ Ψ) : E)‖ ^ 2 :=
        R4TCDiagSigma.Venue.mul_uw_le_norm_sq _
      have h3 : ‖((d p : VΨ Ψ) : E)‖ = 1 := d.orthonormal.1 p
      rw [h3, one_pow] at h2
      rw [h1]
      have hX : (∫ x in Φ, ‖R4TCDiagSigma.Venue.fn ((d p : VΨ Ψ) : E) x‖ ^ 2 ∂μ) ≤ mw⁻¹ := by
        have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hmw0.le)
        rwa [← mul_assoc, inv_mul_cancel₀ hmw0.ne', one_mul, mul_one] at this
      exact mul_le_mul_of_nonneg_right hX (sq_nonneg _)

    have hLint : Integrable (fun x => ‖∑ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i (τ x))‖)
        (μ.restrict Φ₀) :=
      (integrable_finsetSum (Finset.univ : Finset {i // cls i = Ψ}) fun i _ => hK2 i).norm
    have hRint : Integrable (fun x => ∑ k, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex (τ x))‖ ^ 2) / 2)
        (μ.restrict Φ₀) := by
      refine integrable_finsetSum _ fun k _ => Integrable.div_const ?_ 2
      exact (hA k).1.add (hB k).1
    calc ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ}, convOp L f (b i) x * conj (b i (τ x))‖ ∂μ
        ≤ ∫ x in Φ₀, ∑ k, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex (τ x))‖ ^ 2) / 2 ∂μ := by
          refine integral_mono hLint hRint fun x => ?_
          exact hpt x (τ x)
      _ = ∑ k, ∫ x in Φ₀, (‖Adag k (rx x)‖ ^ 2 + ‖Bop k (ex (τ x))‖ ^ 2) / 2 ∂μ :=
          integral_finsetSum _ fun k _ => Integrable.div_const ((hA k).1.add (hB k).1) 2
      _ = ∑ k, (∫ x in Φ₀, ‖Adag k (rx x)‖ ^ 2 ∂μ + ∫ x in Φ₀, ‖Bop k (ex (τ x))‖ ^ 2 ∂μ) / 2 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [integral_div, integral_add (hA k).1 (hB k).1]
      _ ≤ ∑ k, (mw⁻¹ * ∑ p, ‖Adag k ((d p : VΨ Ψ) : E)‖ ^ 2 + ∑ i : {i // cls i = Ψ}, ‖Bop k (Bv i)‖ ^ 2) / 2 := by
          refine Finset.sum_le_sum fun k _ => div_le_div_of_nonneg_right ?_ two_pos.le
          rw [(hB k).2]
          exact add_le_add (hA k).2 le_rfl

  have hdiag' : ∀ Ψ : ↥(cuspClasses L P ξ N SL),
      ∃ d : OrthonormalBasis (Fin (Module.finrank ℂ (VΨ Ψ))) ℂ (VΨ Ψ),
        (∀ p q, p ≠ q → R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d q : VΨ Ψ) : E) = 0) ∧
        ∀ p, R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E) =
          ((RCLike.re (R4TCDiagSigma.Venue.uw ((d p : VΨ Ψ) : E) ((d p : VΨ Ψ) : E)) : ℝ) : ℂ) :=
    fun Ψ => hdiag Ψ.1 Ψ.2
  choose d hd0 hd1 using hdiag'

  have hVspan : ∀ Ψ ∈ cuspClasses L P ξ N SL,
      VΨ Ψ ≤ Submodule.span ℂ (Set.range fun i : {i // cls i = Ψ} => Bv i) := by
    intro Ψ hΨ w hw
    have hfnw : R4TCDiagSigma.Venue.fn w ∈ Submodule.span ℂ (b '' {i | cls i = Ψ}) := by
      rw [(hbs Ψ hΨ).2]
      exact hw
    have himg : b '' {i | cls i = Ψ} =
        (R4TCDiagSigma.Venue.ven ξ Φ).subtype '' (Set.range fun i : {i // cls i = Ψ} => Bv i) := by
      ext u
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨Bv i, ⟨⟨i, hi⟩, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨i.1, i.2, rfl⟩
    rw [himg, ← Submodule.map_span] at hfnw
    obtain ⟨w', hw', hww⟩ := hfnw
    have : w' = w := R4TCDiagSigma.Venue.fn_injective hww
    exact this ▸ hw'
  have huwBv : ∀ i j, cls i ≠ cls j → R4TCDiagSigma.Venue.uw (Bv i) (Bv j) = 0 := by
    intro i j hij
    show ∫ x in Φ, b j x * conj (b i x) ∂(R4TCDiagSigma.Venue.μ L) = 0
    exact hb₀ j i fun h => hij (h ▸ rfl)
  have hcross : ∀ (Ψ Ψ' : ↥(cuspClasses L P ξ N SL)), Ψ ≠ Ψ' → ∀ w ∈ VΨ Ψ, ∀ w' ∈ VΨ Ψ',
      R4TCDiagSigma.Venue.uw w w' = 0 := by
    intro Ψ Ψ' hne w hw w' hw'
    have hw1 := hVspan Ψ.1 Ψ.2 hw
    have hw2 := hVspan Ψ'.1 Ψ'.2 hw'
    refine Submodule.span_induction (p := fun w' _ => R4TCDiagSigma.Venue.uw w w' = 0) ?_ ?_ ?_ ?_ hw2
    · rintro _ ⟨j, rfl⟩
      refine Submodule.span_induction (p := fun w _ => R4TCDiagSigma.Venue.uw w (Bv j) = 0) ?_ ?_ ?_ ?_ hw1
      · rintro _ ⟨i, rfl⟩
        exact huwBv i j (by rw [i.2, j.2]; exact fun h => hne (Subtype.ext h))
      · exact R4TCDiagSigma.Venue.uw_zero_left _
      · intro u u' _ _ hu hu'
        exact (R4TCDiagSigma.Venue.uw_add_left _ _ _).trans (by rw [hu, hu', add_zero])
      · intro c u _ hu
        exact (R4TCDiagSigma.Venue.uw_smul_left _ _ _).trans (by rw [hu, mul_zero])
    · exact R4TCDiagSigma.Venue.uw_zero_right _
    · intro u u' _ _ hu hu'
      exact (R4TCDiagSigma.Venue.uw_add_right _ _ _).trans (by rw [hu, hu', add_zero])
    · intro c u _ hu
      exact (R4TCDiagSigma.Venue.uw_smul_right _ _ _).trans (by rw [hu, mul_zero])

  have hnorm_conv : ∀ (u : AdelicGL2 (𝓞 L) L → ℂ) (hu : Continuous u) (huc : HasCompactSupport u) (w : E),
      ‖R4TCDiagSigma.Venue.convOp u hu huc w‖ ^ 2 ≤
        Mw * ∫ x in Φ, ‖rightConv L (R4TCDiagSigma.Venue.fn w) u x‖ ^ 2 ∂μ := fun u hu huc w =>
    R4TCDiagSigma.Venue.norm_sq_le_mul_uw _

  set Bound : ℝ := ∑ k : Fin n, (mw⁻¹ * (Mw * (mw⁻¹ * HA k)) + Mw * HB k) / 2 with hBound
  have hpartial : ∀ t : Finset ↥(cuspClasses L P ξ N SL),
      ∑ Ψ ∈ t, ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, convOp L f (b i) x * conj (b i (τ x))‖ ∂μ ≤ Bound := by
    intro t

    let JB : Type := Σ Ψ : ↥t, {i // cls i = Ψ.1.1}
    let JA : Type := Σ Ψ : ↥t, Fin (Module.finrank ℂ (VΨ Ψ.1.1))
    let eB : JB → AdelicGL2 (𝓞 L) L → ℂ := fun j => b j.2.1
    let cA : ℂ := ((Real.sqrt mw : ℝ) : ℂ)
    let eA : JA → AdelicGL2 (𝓞 L) L → ℂ := fun j => cA • R4TCDiagSigma.Venue.fn ((d j.1.1 j.2 : VΨ j.1.1.1) : E)
    have eB_def : ∀ j, eB j = b j.2.1 := fun j => rfl
    have eA_def : ∀ j, eA j = cA • R4TCDiagSigma.Venue.fn ((d j.1.1 j.2 : VΨ j.1.1.1) : E) := fun j => rfl
    let σB := (Fintype.equivFin JB).symm
    let σA := (Fintype.equivFin JA).symm
    have hinjB : ∀ j j' : JB, j.2.1 = j'.2.1 → j = j' := by
      rintro ⟨⟨Ψ, hΨ⟩, ⟨i, hi⟩⟩ ⟨⟨Ψ', hΨ'⟩, ⟨i', hi'⟩⟩ (hii : i = i')
      subst hii
      have : Ψ = Ψ' := Subtype.ext (hi.symm.trans hi')
      subst this
      rfl
    have huwA : ∀ j j' : JA, j ≠ j' →
        R4TCDiagSigma.Venue.uw ((d j'.1.1 j'.2 : VΨ j'.1.1.1) : E) ((d j.1.1 j.2 : VΨ j.1.1.1) : E) = 0 := by
      rintro ⟨Ψ, p⟩ ⟨Ψ', p'⟩ hne
      by_cases hΨ : Ψ = Ψ'
      · subst hΨ
        have hpp : p' ≠ p := fun h => hne (by rw [h])
        exact hd0 Ψ.1 p' p hpp
      · exact hcross Ψ'.1 Ψ.1 (fun h => hΨ (Subtype.ext h).symm) _ (d Ψ'.1 p').2 _ (d Ψ.1 p).2

    have hBsum : ∀ k, ∑ j : JB, ‖Bop k (Bv j.2.1)‖ ^ 2 ≤ Mw * HB k := by
      intro k
      have h1 : ∀ j : JB, ‖Bop k (Bv j.2.1)‖ ^ 2 ≤ Mw * ∫ x in Φ, ‖rightConv L (eB j) (h k) x‖ ^ 2 ∂μ :=
        fun j => hnorm_conv (h k) (hhc k).1 (hhc k).2 (Bv j.2.1)
      have h2 : ∑ m : Fin (Fintype.card JB), ∫ x in Φ, ‖rightConv L (eB (σB m)) (h k) x‖ ^ 2 ∂μ ≤ HB k := by
        refine hHB k _ (fun m => eB (σB m)) (fun m => (hWf _ _ (hb _).2).1) (fun m => (hWf _ _ (hb _).2).2.1)
          (fun m => (hWf _ _ (hb _).2).2.2.2) (fun m => (hWf _ _ (hb _).2).2.2.1) (fun m m' hmm => ?_) (fun m => ?_)
        · exact hb₀ _ _ fun heq => hmm (σB.injective (hinjB _ _ heq))
        · rw [show (∫ x in Φ, ‖eB (σB m) x‖ ^ 2 ∂μ) = 1 from ?_]
          have h := hb₁ (σB m).2.1
          have h2 : (fun x => b (σB m).2.1 x * conj (b (σB m).2.1 x)) =
              fun x => ((‖b (σB m).2.1 x‖ ^ 2 : ℝ) : ℂ) := by
            funext x
            rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
          rw [h2, integral_complex_ofReal] at h
          exact_mod_cast h
      calc ∑ j : JB, ‖Bop k (Bv j.2.1)‖ ^ 2
          ≤ ∑ j : JB, Mw * ∫ x in Φ, ‖rightConv L (eB j) (h k) x‖ ^ 2 ∂μ := Finset.sum_le_sum fun j _ => h1 j
        _ = Mw * ∑ j : JB, ∫ x in Φ, ‖rightConv L (eB j) (h k) x‖ ^ 2 ∂μ := (Finset.mul_sum _ _ _).symm
        _ = Mw * ∑ m : Fin (Fintype.card JB), ∫ x in Φ, ‖rightConv L (eB (σB m)) (h k) x‖ ^ 2 ∂μ := by
            rw [← Equiv.sum_comp σB]
        _ ≤ Mw * HB k := mul_le_mul_of_nonneg_left h2 hMw0

    have hAsum : ∀ k, ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : VΨ j.1.1.1) : E)‖ ^ 2 ≤ Mw * (mw⁻¹ * HA k) := by
      intro k
      have hcA : cA * conj cA = ((mw : ℝ) : ℂ) := by
        show ((Real.sqrt mw : ℝ) : ℂ) * conj ((Real.sqrt mw : ℝ) : ℂ) = _
        rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hmw0.le]
      have hcA2 : ‖cA‖ ^ 2 = mw := by
        show ‖((Real.sqrt mw : ℝ) : ℂ)‖ ^ 2 = mw
        rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hmw0.le]
      have h1 : ∀ j : JA, ‖Adag k ((d j.1.1 j.2 : VΨ j.1.1.1) : E)‖ ^ 2 ≤
          Mw * (mw⁻¹ * ∫ x in Φ, ‖rightConv L (eA j) (fun y => conj (g k y⁻¹) *
            ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) := by
        intro j
        have h := hnorm_conv _ (R4TCDiagSigma.Venue.flat_continuous s (g k) (hgc k).1)
          (R4TCDiagSigma.Venue.flat_hasCompactSupport s (g k) (hgc k).2) ((d j.1.1 j.2 : VΨ j.1.1.1) : E)
        refine h.trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hMw0)
        have hsm : rightConv L (eA j) (fun y => conj (g k y⁻¹) *
            ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) =
            cA • rightConv L (R4TCDiagSigma.Venue.fn ((d j.1.1 j.2 : VΨ j.1.1.1) : E)) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) :=
          R4TCDiagSigma.Venue.rightConv_smul_left cA _ _
        rw [hsm]
        simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hcA2]
        rw [integral_const_mul, ← mul_assoc, inv_mul_cancel₀ hmw0.ne', one_mul]
      have h2 : ∑ m : Fin (Fintype.card JA), ∫ x in Φ, ‖rightConv L (eA (σA m)) (fun y => conj (g k y⁻¹) *
            ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ ≤
            HA k := by
        have hmemA : ∀ j : JA, R4TCDiagSigma.Venue.fn ((d j.1.1 j.2 : VΨ j.1.1.1) : E) ∈ W j.1.1.1 :=
          fun j => (mem_VΨ _ _).1 (d j.1.1 j.2).2
        refine hHA k _ (fun m => eA (σA m))
          (fun m => by beta_reduce; rw [eA_def]; exact (hWf _ _ (hmemA (σA m))).1.const_smul cA)
          (fun m => ?_) (fun m => ?_)
          (fun m => by beta_reduce; rw [eA_def]; exact (hWf _ _ (hmemA (σA m))).2.2.1.const_smul cA)
          (fun m m' hmm => ?_) (fun m => ?_)
        · have hl := (hWf _ _ (hmemA (σA m))).2.1
          exact ⟨fun γ x => by beta_reduce; rw [eA_def]; simp only [Pi.smul_apply, hl.left_invariant],
            fun z x => by
              beta_reduce; rw [eA_def]; simp only [Pi.smul_apply, smul_eq_mul, hl.central_transform]; ring⟩
        · beta_reduce
          have hz := (hWf _ _ (hmemA (σA m))).2.2.2
          intro x
          have h1 := hz x
          have hsplit : constantTermIntegrand unipotentGL2 (eA (σA m)) x =
              fun q => cA * constantTermIntegrand unipotentGL2
                (R4TCDiagSigma.Venue.fn ((d (σA m).1.1 (σA m).2 : VΨ (σA m).1.1.1) : E)) x q :=
            rfl
          unfold constantTerm at h1 ⊢
          rw [hsplit, integral_const_mul, h1, mul_zero]
        · have huw : R4TCDiagSigma.Venue.uw ((d (σA m').1.1 (σA m').2 : VΨ (σA m').1.1.1) : E)
              ((d (σA m).1.1 (σA m).2 : VΨ (σA m).1.1.1) : E) = 0 :=
            huwA (σA m) (σA m') fun heq => hmm (σA.injective heq)
          show ∫ x in Φ, eA (σA m) x * conj (eA (σA m') x) ∂μ = 0
          have : (fun x => eA (σA m) x * conj (eA (σA m') x)) = fun x => (cA * conj cA) *
              (R4TCDiagSigma.Venue.fn ((d (σA m).1.1 (σA m).2 : VΨ (σA m).1.1.1) : E) x *
                conj (R4TCDiagSigma.Venue.fn ((d (σA m').1.1 (σA m').2 : VΨ (σA m').1.1.1) : E) x)) := by
            funext x
            simp only [eA_def, Pi.smul_apply, smul_eq_mul, map_mul]
            ring
          rw [this, integral_const_mul]
          change cA * conj cA * R4TCDiagSigma.Venue.uw _ _ = 0
          rw [huw, mul_zero]
        · beta_reduce
          have hint2 : ∫ x in Φ, ‖eA (σA m) x‖ ^ 2 ∂μ =
              mw * ∫ x in Φ, ‖R4TCDiagSigma.Venue.fn ((d (σA m).1.1 (σA m).2 : VΨ (σA m).1.1.1) : E) x‖ ^ 2 ∂μ := by
            simp only [eA_def, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, hcA2]
            exact integral_const_mul _ _
          rw [hint2]
          have h2 := R4TCDiagSigma.Venue.mul_uw_le_norm_sq ((d (σA m).1.1 (σA m).2 : VΨ (σA m).1.1.1) : E)
          have h3 : ‖((d (σA m).1.1 (σA m).2 : VΨ (σA m).1.1.1) : E)‖ = 1 := (d (σA m).1.1).orthonormal.1 _
          rw [h3, one_pow] at h2
          exact h2
      calc ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : VΨ j.1.1.1) : E)‖ ^ 2
          ≤ ∑ j : JA, Mw * (mw⁻¹ * ∫ x in Φ, ‖rightConv L (eA j) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) :=
            Finset.sum_le_sum fun j _ => h1 j
        _ = Mw * (mw⁻¹ * ∑ j : JA, ∫ x in Φ, ‖rightConv L (eA j) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) := by
            rw [Finset.mul_sum, Finset.mul_sum]
        _ = Mw * (mw⁻¹ * ∑ m : Fin (Fintype.card JA), ∫ x in Φ, ‖rightConv L (eA (σA m)) (fun y => conj (g k y⁻¹) *
              ((NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det y) ^ (-s) : ℝ) : ℂ)) x‖ ^ 2 ∂μ) := by
            rw [← Equiv.sum_comp σA]
        _ ≤ Mw * (mw⁻¹ * HA k) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hmw0.le)) hMw0

    calc ∑ Ψ ∈ t, ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, convOp L f (b i) x * conj (b i (τ x))‖ ∂μ
        ≤ ∑ Ψ ∈ t, ∑ k, (mw⁻¹ * ∑ p, ‖Adag k ((d Ψ p : VΨ Ψ.1) : E)‖ ^ 2 +
            ∑ i : {i // cls i = Ψ.1}, ‖Bop k (Bv i)‖ ^ 2) / 2 :=
          Finset.sum_le_sum fun Ψ _ => key Ψ.1 Ψ.2 (d Ψ) (hd0 Ψ) (hd1 Ψ)
      _ = ∑ k, (mw⁻¹ * ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : VΨ j.1.1.1) : E)‖ ^ 2 +
            ∑ j : JB, ‖Bop k (Bv j.2.1)‖ ^ 2) / 2 := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          have hSA : ∑ Ψ ∈ t, ∑ p, ‖Adag k ((d Ψ p : VΨ Ψ.1) : E)‖ ^ 2 =
              ∑ j : JA, ‖Adag k ((d j.1.1 j.2 : VΨ j.1.1.1) : E)‖ ^ 2 := by
            rw [← Finset.sum_coe_sort t]
            exact (Fintype.sum_sigma (fun j : JA => ‖Adag k ((d j.1.1 j.2 : VΨ j.1.1.1) : E)‖ ^ 2)).symm
          have hSB : ∑ Ψ ∈ t, ∑ i : {i // cls i = Ψ.1}, ‖Bop k (Bv i)‖ ^ 2 = ∑ j : JB, ‖Bop k (Bv j.2.1)‖ ^ 2 := by
            rw [← Finset.sum_coe_sort t]
            exact (Fintype.sum_sigma (fun j : JB => ‖Bop k (Bv j.2.1)‖ ^ 2)).symm
          rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, hSA, hSB]
      _ ≤ Bound := Finset.sum_le_sum fun k _ =>
          div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left (hAsum k) (inv_nonneg.2 hmw0.le))
            (hBsum k)) two_pos.le

  refine (summable_subtype_and_compl (s := cuspClasses L P ξ N SL)).1 ⟨?_, ?_⟩
  · have hnn : 0 ≤ fun Ψ : ↥(cuspClasses L P ξ N SL) =>
        ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, convOp L f (b i) x * conj (b i (τ x))‖ ∂μ :=
      fun Ψ => integral_nonneg fun _ => norm_nonneg _
    exact summable_of_sum_le hnn hpartial
  · have hz : (fun Ψ : ↥((cuspClasses L P ξ N SL)ᶜ) =>
        ∫ x in Φ₀, ‖∑ i : {i // cls i = Ψ.1}, convOp L f (b i) x * conj (b i (τ x))‖ ∂μ) = 0 := by
      funext Ψ
      have hΨ : Ψ.1 ∉ cuspClasses L P ξ N SL := Ψ.2
      haveI : IsEmpty {i // cls i = Ψ.1} := ⟨fun i => hΨ (i.2 ▸ (hb i.1).1)⟩
      simp
    rw [hz]
    exact summable_zero

end S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab
end P2MW
export P2MW.S_AutomorphicForm_integrableOn_convOp_mul_conj_sigmaAdelicAct_symm_and_summable_setIntegral_norm_finsum_of_orthonormal_principalLevel_of_isFundamentalDomain_slab (solution)
