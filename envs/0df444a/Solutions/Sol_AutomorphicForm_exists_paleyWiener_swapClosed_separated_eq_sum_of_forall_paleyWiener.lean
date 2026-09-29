-- Prove2me | solution 1 for AutomorphicForm.exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/dbd67ade-6bc2-569b-a156-ac7522921f23

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_RationalTorusUnipotentQuotient
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_CarrierPins
import Mathlib.Analysis.Meromorphic.NormalForm
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift
import Theorems.Thm_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.whittakerCoefficient_zero LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm
open scoped NNReal ENNReal Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

noncomputable section

namespace Ws1
namespace SwapNorm

open NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

theorem nPC_coe (t : ℝ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((normPowChar F t x : ℂˣ) : ℂ) = ((ideleNorm F x : ℝ) : ℂ) ^ (Complex.I * t) := rfl

theorem nPC_add (a b : ℝ) : normPowChar F (a + b) = normPowChar F a * normPowChar F b := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, nPC_coe, nPC_coe, nPC_coe, Complex.ofReal_add, mul_add,
    Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]

theorem nPC_neg (a : ℝ) : normPowChar F (-a) = (normPowChar F a)⁻¹ := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.inv_apply]
  apply Units.ext
  rw [Units.val_inv_eq_inv_val, nPC_coe, nPC_coe, Complex.ofReal_neg, mul_neg, Complex.cpow_neg]

theorem nPC_half_mul_half (τ : ℝ) : normPowChar F (τ / 2) * normPowChar F (τ / 2) = normPowChar F τ := by
  rw [← nPC_add, add_halves]

theorem nPC_normOne (t : ℝ) {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ normOneIdeles F) : normPowChar F t x = 1 :=
  normPowChar_eq_one_of_ideleNorm_eq_one t ((mem_normOneIdeles_iff x).mp hx)

theorem nPC_unitary (t : ℝ) : IsUnitaryChar (𝓞 F) F (normPowChar F t) :=
  fun x => norm_coe_normPowChar_apply t x

theorem nPC_continuous (t : ℝ) : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((normPowChar F t x : ℂˣ) : ℂ) := by
  have hc := NumberField.TateGlobal.continuous_ideleNorm F
  show Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ideleNorm F x : ℝ) : ℂ) ^ (Complex.I * t)
  refine Continuous.cpow (Complex.continuous_ofReal.comp hc) continuous_const fun x => ?_
  exact Or.inl (by simpa using (ideleNorm_pos x))

theorem nPC_classChar (t : ℝ) : IsIdeleClassChar (𝓞 F) F (normPowChar F t) := by
  intro u
  apply normPowChar_eq_one_of_ideleNorm_eq_one
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F u
  unfold ideleNorm
  have : (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom u) = Units.map (algebraMap F (AdeleRing (𝓞 F) F)) u := rfl
  rw [this] at h
  rw [h]; rfl

theorem exists_shift (μ μ' : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hμu : IsUnitaryChar (𝓞 F) F μ) (hμ'u : IsUnitaryChar (𝓞 F) F μ')
    (hμc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
    (hμ'c : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ' x : ℂˣ) : ℂ))
    (h1 : ∀ x ∈ normOneIdeles F, μ' x = μ x) :
    ∃ τ : ℝ, μ' = μ * normPowChar F τ := by
  set χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ := μ' * μ⁻¹ with hχdef
  have hχapp : ∀ z, χ z = μ' z * (μ z)⁻¹ := fun z => rfl
  have hχu : IsUnitaryChar (𝓞 F) F χ := by
    intro z
    rw [hχapp, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_inv, hμ'u z, hμu z, inv_one, mul_one]
  have hχc : Continuous χ := by
    have hc : Continuous fun z => ((χ z : ℂˣ) : ℂ) := by
      have hfun : (fun z => ((χ z : ℂˣ) : ℂ)) = fun z => ((μ' z : ℂˣ) : ℂ) * ((μ z : ℂˣ) : ℂ)⁻¹ := by
        funext z; rw [hχapp, Units.val_mul, Units.val_inv_eq_inv_val]
      rw [hfun]
      exact hμ'c.mul (hμc.inv₀ fun z => Units.ne_zero _)
    exact Units.isOpenEmbedding_val.isInducing.continuous_iff.mpr hc
  have hχ1 : ∀ z ∈ normOneIdeles F, χ z = 1 := by
    intro z hz
    rw [hχapp, h1 z hz, mul_inv_cancel]
  obtain ⟨τ, hτ⟩ := NumberField.TateGlobal.exists_eq_normPowChar_of_forall_mem_normOneIdeles F χ hχc hχu hχ1
  refine ⟨τ, MonoidHom.ext fun z => ?_⟩
  rw [MonoidHom.mul_apply, ← hτ, hχapp, mul_comm, inv_mul_cancel_right]

section Index

variable {J K : Type} [Fintype J] [DecidableEq K]

def keySet (κ : J → K × K) : Finset (K × K) :=
  (Finset.univ.image κ) ∪ (Finset.univ.image (Prod.swap ∘ κ))

theorem mem_keySet_swap {κ : J → K × K} {k : K × K} (hk : k ∈ keySet κ) : k.swap ∈ keySet κ := by
  classical
  simp only [keySet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at hk ⊢
  rcases hk with ⟨j, hj⟩ | ⟨j, hj⟩
  · exact Or.inr ⟨j, by rw [hj]⟩
  · exact Or.inl ⟨j, by rw [← hj, Prod.swap_swap]⟩

theorem mem_keySet_self (κ : J → K × K) (j : J) : κ j ∈ keySet κ := by
  classical
  simp only [keySet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl ⟨j, rfl⟩

theorem mem_keySet_cases {κ : J → K × K} {k : K × K} (hk : k ∈ keySet κ) :
    (∃ j, κ j = k) ∨ (∃ j, (κ j).swap = k) := by
  classical
  simp only [keySet, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply] at hk
  exact hk

def swapIdx (κ : J → K × K) (e : ↥(keySet κ)) : ↥(keySet κ) := ⟨(e : K × K).swap, mem_keySet_swap e.2⟩

theorem swapIdx_swapIdx (κ : J → K × K) (e : ↥(keySet κ)) : swapIdx κ (swapIdx κ e) = e :=
  Subtype.ext (Prod.swap_swap _)

theorem swapIdx_eq_self_iff (κ : J → K × K) (e : ↥(keySet κ)) :
    swapIdx κ e = e ↔ (e : K × K).swap = (e : K × K) :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

end Index

end Ws1.SwapNorm

namespace Ws1
namespace SwapNorm

open NumberField.TateGlobal

section Closure

variable {F : Type} [Field F] [NumberField F]

theorem rightTranslatesSpanFinite_add {G : Type*} [Group G] (K : Subgroup G) {f g : G → ℂ}
    (hf : RightTranslatesSpanFinite K f) (hg : RightTranslatesSpanFinite K g) :
    RightTranslatesSpanFinite K (fun x => f x + g x) := by
  classical
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  refine ⟨s ∪ t, fun k hk => ?_⟩
  have h1 : (fun x => f (x * k)) ∈ Submodule.span ℂ ((s ∪ t : Finset (G → ℂ)) : Set (G → ℂ)) :=
    Submodule.span_mono (by intro x hx; exact Finset.mem_coe.mpr (Finset.mem_union_left _ (Finset.mem_coe.mp hx))) (hs k hk)
  have h2 : (fun x => g (x * k)) ∈ Submodule.span ℂ ((s ∪ t : Finset (G → ℂ)) : Set (G → ℂ)) :=
    Submodule.span_mono (by intro x hx; exact Finset.mem_coe.mpr (Finset.mem_union_right _ (Finset.mem_coe.mp hx))) (ht k hk)
  have := Submodule.add_mem _ h1 h2
  exact this

theorem rightTranslatesSpanFinite_sum {G : Type*} [Group G] (K : Subgroup G) {ι : Type*} (S : Finset ι)
    {f : ι → G → ℂ} (hf : ∀ i ∈ S, RightTranslatesSpanFinite K (f i)) :
    RightTranslatesSpanFinite K (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using rightTranslatesSpanFinite_const K (0 : ℂ)
  | insert a S ha ih =>
    have h := rightTranslatesSpanFinite_add K (hf a (Finset.mem_insert_self a S))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine (show (fun x => ∑ i ∈ insert a S, f i x) = fun x => f a x + ∑ i ∈ S, f i x from ?_) ▸ h
    funext x; rw [Finset.sum_insert ha]

theorem isArchKFinite_sum (F : Type) [Field F] [NumberField F] {ι : Type*} (S : Finset ι)
    {f : ι → AdelicGL2 (𝓞 F) F → ℂ} (hf : ∀ i ∈ S, IsArchKFinite F (f i)) :
    IsArchKFinite F (fun x => ∑ i ∈ S, f i x) :=
  fun w => rightTranslatesSpanFinite_sum _ S fun i hi => hf i hi w

theorem isKfSmooth_add (F : Type) [Field F] [NumberField F] {f g : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsKfSmooth F f) (hg : IsKfSmooth F g) : IsKfSmooth F (fun x => f x + g x) := by
  have h := FLT.SmoothVectors.IsSmoothVector.add hf hg
  exact h

theorem isKfSmooth_zero (F : Type) [Field F] [NumberField F] : IsKfSmooth F (fun _ : AdelicGL2 (𝓞 F) F => (0 : ℂ)) :=
  FLT.SmoothVectors.isSmoothVector_zero

theorem isKfSmooth_sum (F : Type) [Field F] [NumberField F] {ι : Type*} (S : Finset ι)
    {f : ι → AdelicGL2 (𝓞 F) F → ℂ} (hf : ∀ i ∈ S, IsKfSmooth F (f i)) :
    IsKfSmooth F (fun x => ∑ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isKfSmooth_zero F
  | insert a S ha ih =>
    have h := isKfSmooth_add F (hf a (Finset.mem_insert_self a S)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine (show (fun x => ∑ i ∈ insert a S, f i x) = fun x => f a x + ∑ i ∈ S, f i x from ?_) ▸ h
    funext x; rw [Finset.sum_insert ha]

theorem isInducedSection_sum {χ₁ χ₂ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} {ι : Type*} (S : Finset ι)
    {f : ι → AdelicGL2 (𝓞 F) F → ℂ} (hf : ∀ i ∈ S, IsInducedSection (𝓞 F) F χ₁ χ₂ (f i)) :
    IsInducedSection (𝓞 F) F χ₁ χ₂ (fun x => ∑ i ∈ S, f i x) := by
  have h : (fun x => ∑ i ∈ S, f i x) = ∑ i ∈ S, f i := by funext x; rw [Finset.sum_apply]
  rw [h]
  exact (inducedSectionSubmodule χ₁ χ₂).sum_mem fun i hi => hf i hi

theorem isSlabProfile_add {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsSlabProfile F Z ξ φ) (hψ : IsSlabProfile F Z ξ ψ) : IsSlabProfile F Z ξ (fun g => φ g + ψ g) where
  measurable := hφ.measurable.add hψ.measurable
  unipotent_mul := fun x g => by rw [hφ.unipotent_mul, hψ.unipotent_mul]
  borel_mul := fun γ hγ g => by rw [hφ.borel_mul γ hγ, hψ.borel_mul γ hγ]
  central_transform := fun z g => by rw [hφ.central_transform, hψ.central_transform]; ring
  bounded_on_slab := fun d₁ d₂ hd₁ => by
    obtain ⟨C₁, h₁⟩ := hφ.bounded_on_slab d₁ d₂ hd₁
    obtain ⟨C₂, h₂⟩ := hψ.bounded_on_slab d₁ d₂ hd₁
    exact ⟨C₁ + C₂, fun g hg => (norm_add_le _ _).trans (add_le_add (h₁ g hg) (h₂ g hg))⟩
  height_band := by
    obtain ⟨a₁, b₁, ha₁, h₁⟩ := hφ.height_band
    obtain ⟨a₂, b₂, ha₂, h₂⟩ := hψ.height_band
    refine ⟨min a₁ a₂, max b₁ b₂, lt_min ha₁ ha₂, fun g hg => ?_⟩
    by_cases h0 : φ g = 0
    · have : ψ g ≠ 0 := by intro h; exact hg (by rw [h0, h, add_zero])
      obtain ⟨hl, hu⟩ := h₂ g this
      exact ⟨le_trans (min_le_right _ _) hl, le_trans hu (le_max_right _ _)⟩
    · obtain ⟨hl, hu⟩ := h₁ g h0
      exact ⟨le_trans (min_le_left _ _) hl, le_trans hu (le_max_left _ _)⟩

theorem isSlabProfile_sum {Z : Subgroup (AdeleRing (𝓞 F) F)ˣ} {ξ : Z →* ℂˣ} {ι : Type*} (S : Finset ι)
    {f : ι → AdelicGL2 (𝓞 F) F → ℂ} (hf : ∀ i ∈ S, IsSlabProfile F Z ξ (f i)) :
    IsSlabProfile F Z ξ (fun g => ∑ i ∈ S, f i g) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using isSlabProfile_zero (F := F) Z ξ
  | insert a S ha ih =>
    have h := isSlabProfile_add (hf a (Finset.mem_insert_self a S)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine (show (fun x => ∑ i ∈ insert a S, f i x) = fun x => f a x + ∑ i ∈ S, f i x from ?_) ▸ h
    funext x; rw [Finset.sum_insert ha]

theorem one_add_abs_le (t τ : ℝ) : 1 + |t| ≤ (1 + |τ|) * (1 + |t - τ|) := by
  have h : |t| ≤ |τ| + |t - τ| := by
    calc |t| = |τ + (t - τ)| := by ring_nf
      _ ≤ |τ| + |t - τ| := abs_add_le _ _
  nlinarith [abs_nonneg τ, abs_nonneg (t - τ)]

end Closure

end Ws1.SwapNorm

theorem solution
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (Φ : Set (AdelicGL2 (𝓞 F) F))
      (ξ : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z →* ℂˣ)
      (_hξ : Continuous ξ) (_hξu : ∀ z, ‖((ξ z : ℂˣ) : ℂ)‖ = 1)
      (a b : ℝ)
      (n : ℕ) (μ₀ ν₀ : Fin n → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
      (_hμ₀ : ∀ j, IsUnitaryChar (𝓞 F) F (μ₀ j)) (_hν₀ : ∀ j, IsUnitaryChar (𝓞 F) F (ν₀ j))
      (_hμ₀ic : ∀ j, IsIdeleClassChar (𝓞 F) F (μ₀ j)) (_hν₀ic : ∀ j, IsIdeleClassChar (𝓞 F) F (ν₀ j))
      (_hμ₀c : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ₀ j x : ℂˣ) : ℂ))
      (_hν₀c : ∀ j, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν₀ j x : ℂˣ) : ℂ))
      (_hμ₀ν₀ : ∀ (j : Fin n) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ₀ j (z : (AdeleRing (𝓞 F) F)ˣ) * ν₀ j (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z)
      (ψf₀ : Fin n → ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf₀ : ∀ j s, IsInducedSection (𝓞 F) F (etaFst (μ₀ j) α hα s) (etaSnd (ν₀ j) α hα s) (ψf₀ j s))
      (_hψ₀jc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf₀ j p.1 p.2))
      (_hψ₀hol : ∀ j g, Differentiable ℂ (fun s => ψf₀ j s g))
      (_hψ₀K : ∀ j s, IsArchKFinite F (ψf₀ j s)) (_hψ₀sm : ∀ j s, IsKfSmooth F (ψf₀ j s))
      (_hψ₀Ku : ∀ (j : Fin n) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ j s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψ₀dec : ∀ (j : Fin n) (m₀ : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ m₀ * ‖ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₀ : Fin n → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψ₀ : ∀ j, AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ (ψ₀ j))
      (_hψ₀rep : ∀ (j : Fin n) (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ₀ j g = (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (_hψ₀band : ∀ (j : Fin n) (g : AdelicGL2 (𝓞 F) F), ψ₀ j g ≠ 0 →
        NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b),
    ∃ (ι : Type) (_ : Fintype ι) (μ ν : ι → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) (r : ι → ι)
      (ψf : ι → ℂ → AdelicGL2 (𝓞 F) F → ℂ) (ψ : AdelicGL2 (𝓞 F) F → ℂ),
      (∀ e, IsUnitaryChar (𝓞 F) F (μ e)) ∧ (∀ e, IsUnitaryChar (𝓞 F) F (ν e)) ∧
      (∀ e, IsIdeleClassChar (𝓞 F) F (μ e)) ∧ (∀ e, IsIdeleClassChar (𝓞 F) F (ν e)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ e x : ℂˣ) : ℂ)) ∧
      (∀ e, Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν e x : ℂˣ) : ℂ)) ∧
      (∀ (e : ι) (z : (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z),
        μ e (z : (AdeleRing (𝓞 F) F)ˣ) * ν e (z : (AdeleRing (𝓞 F) F)ˣ) = ξ z) ∧
      (∀ e, μ (r e) = ν e ∧ ν (r e) = μ e) ∧
      (∀ e e' : ι, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles F,
        μ e x ≠ μ e' x ∨ ν e x ≠ ν e' x) ∧
      (∀ e s, IsInducedSection (𝓞 F) F (etaFst (μ e) α hα s) (etaSnd (ν e) α hα s) (ψf e s)) ∧
      (∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf e p.1 p.2)) ∧
      (∀ e g, Differentiable ℂ (fun s => ψf e s g)) ∧
      (∀ e s, IsArchKFinite F (ψf e s)) ∧ (∀ e s, IsKfSmooth F (ψf e s)) ∧
      (∀ (e : ι) (w : InfinitePlace F), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf e s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W) ∧
      (∀ (e : ι) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 F) F)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t) ∧
      AutomorphicForm.IsSlabProfile F (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z ξ ψ ∧
      (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 F) F),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, ψ g ≠ 0 → NumberField.AdelicHeight.adelicHeight F g ∈ Set.Icc a b) ∧
      (ψ = fun g => ∑ j, ψ₀ j g) := by
  intro α hα d₁ d₂ _hd₁ _hd Φ ξ _hξ _hξu a b n μ₀ ν₀ hμ₀ hν₀ hμ₀ic hν₀ic hμ₀c hν₀c hμ₀ν₀ ψf₀ hψf₀ hψ₀jc hψ₀hol hψ₀K hψ₀sm hψ₀Ku hψ₀dec ψ₀ hψ₀ hψ₀rep hψ₀band
  classical

  have hαI : ∀ x, ((α x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm F x := fun x => rfl

  have hZtop : ∀ z : (AdeleRing (𝓞 F) F)ˣ, z ∈ (productionPinsOf F Φ (fun N => levelOne (𝓞 F) F N) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).Z := fun z => by
    rw [productionPinsOf_Z]; trivial
  set Ξ : (AdeleRing (𝓞 F) F)ˣ → ℂˣ := fun z => ξ ⟨z, hZtop z⟩ with hΞdef
  have hΞ : ∀ (j : Fin n) (z : (AdeleRing (𝓞 F) F)ˣ), μ₀ j z * ν₀ j z = Ξ z := fun j z => hμ₀ν₀ j ⟨z, hZtop z⟩

  set κ : Fin n → ((↥(NumberField.TateGlobal.normOneIdeles F) → ℂˣ) × (↥(NumberField.TateGlobal.normOneIdeles F) → ℂˣ)) :=
    fun j => (fun x => μ₀ j (x : (AdeleRing (𝓞 F) F)ˣ), fun x => ν₀ j (x : (AdeleRing (𝓞 F) F)ˣ)) with hκdef

  set Good : ↥(Ws1.SwapNorm.keySet κ) → (((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) × ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) → Prop := fun e p =>
    (∀ x : ↥(NumberField.TateGlobal.normOneIdeles F), p.1 (x : (AdeleRing (𝓞 F) F)ˣ) = e.1.1 x ∧
        p.2 (x : (AdeleRing (𝓞 F) F)ˣ) = e.1.2 x) ∧
    IsUnitaryChar (𝓞 F) F p.1 ∧ IsUnitaryChar (𝓞 F) F p.2 ∧
    IsIdeleClassChar (𝓞 F) F p.1 ∧ IsIdeleClassChar (𝓞 F) F p.2 ∧
    (Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((p.1 x : ℂˣ) : ℂ)) ∧
    (Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((p.2 x : ℂˣ) : ℂ)) ∧
    (∀ z : (AdeleRing (𝓞 F) F)ˣ, p.1 z * p.2 z = Ξ z) with hGood

  have hraw : ∀ e : ↥(Ws1.SwapNorm.keySet κ), ∃ p, Good e p := by
    intro e
    rcases Ws1.SwapNorm.mem_keySet_cases e.2 with ⟨j, hj⟩ | ⟨j, hj⟩
    · refine ⟨(μ₀ j, ν₀ j), ?_, hμ₀ j, hν₀ j, hμ₀ic j, hν₀ic j, hμ₀c j, hν₀c j, hΞ j⟩
      intro x; rw [← hj]; exact ⟨rfl, rfl⟩
    · refine ⟨(ν₀ j, μ₀ j), ?_, hν₀ j, hμ₀ j, hν₀ic j, hμ₀ic j, hν₀c j, hμ₀c j, fun z => by rw [mul_comm]; exact hΞ j z⟩
      intro x; rw [← hj]; exact ⟨rfl, rfl⟩
  have hgood_swap : ∀ e p, Good e p → Good (Ws1.SwapNorm.swapIdx κ e) p.swap := by
    intro e p hp
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hp
    exact ⟨fun x => ⟨(h0 x).2, (h0 x).1⟩, h2, h1, h4, h3, h6, h5, fun z => by rw [Prod.fst_swap, Prod.snd_swap, mul_comm]; exact h7 z⟩

  have hhalf : ∀ e p, Ws1.SwapNorm.swapIdx κ e = e → Good e p → ∃ p', Good e p' ∧ p'.2 = p'.1 := by
    intro e p he hp
    obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hp
    have hsd := (Ws1.SwapNorm.swapIdx_eq_self_iff κ e).mp he
    have hagree : ∀ x ∈ NumberField.TateGlobal.normOneIdeles F, p.2 x = p.1 x := by
      intro x hx
      have := h0 ⟨x, hx⟩
      rw [this.1, this.2]
      have : e.1.1 = e.1.2 := by
        have h := congrArg Prod.snd hsd
        simpa using h
      rw [this]
    obtain ⟨τ, hτ⟩ := Ws1.SwapNorm.exists_shift F p.1 p.2 h1 h2 h5 h6 hagree
    refine ⟨(p.1 * NumberField.TateGlobal.normPowChar F (τ / 2), p.1 * NumberField.TateGlobal.normPowChar F (τ / 2)), ?_, rfl⟩
    refine ⟨fun x => ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun z => ?_⟩
    · have hx1 := Ws1.SwapNorm.nPC_normOne F (τ / 2) x.2
      refine ⟨?_, ?_⟩
      · show p.1 x * NumberField.TateGlobal.normPowChar F (τ / 2) x = _
        rw [hx1, mul_one]; exact (h0 x).1
      · show p.1 x * NumberField.TateGlobal.normPowChar F (τ / 2) x = _
        rw [hx1, mul_one, ← hagree x x.2]; exact (h0 x).2
    · intro x; rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h1 x, Ws1.SwapNorm.nPC_unitary F _ x, one_mul]
    · intro x; rw [MonoidHom.mul_apply, Units.val_mul, norm_mul, h1 x, Ws1.SwapNorm.nPC_unitary F _ x, one_mul]
    · intro u; rw [MonoidHom.mul_apply, h3 u, Ws1.SwapNorm.nPC_classChar F _ u, one_mul]
    · intro u; rw [MonoidHom.mul_apply, h3 u, Ws1.SwapNorm.nPC_classChar F _ u, one_mul]
    · exact (show (fun x : (AdeleRing (𝓞 F) F)ˣ => ((p.1 x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.normPowChar F (τ / 2) x : ℂˣ) : ℂ)) =
          fun x => (((p.1 * NumberField.TateGlobal.normPowChar F (τ / 2)) x : ℂˣ) : ℂ) from funext fun x => by
            rw [MonoidHom.mul_apply, Units.val_mul]) ▸ (h5.mul (Ws1.SwapNorm.nPC_continuous F _))
    · exact (show (fun x : (AdeleRing (𝓞 F) F)ˣ => ((p.1 x : ℂˣ) : ℂ) * ((NumberField.TateGlobal.normPowChar F (τ / 2) x : ℂˣ) : ℂ)) =
          fun x => (((p.1 * NumberField.TateGlobal.normPowChar F (τ / 2)) x : ℂˣ) : ℂ) from funext fun x => by
            rw [MonoidHom.mul_apply, Units.val_mul]) ▸ (h5.mul (Ws1.SwapNorm.nPC_continuous F _))
    · show p.1 z * NumberField.TateGlobal.normPowChar F (τ / 2) z * (p.1 z * NumberField.TateGlobal.normPowChar F (τ / 2) z) = Ξ z
      rw [← h7 z, hτ, MonoidHom.mul_apply, ← Ws1.SwapNorm.nPC_half_mul_half F τ, MonoidHom.mul_apply]
      simp only [mul_comm, mul_left_comm, mul_assoc]
  choose raw hrawG using hraw
  have hhalf' : ∀ e : ↥(Ws1.SwapNorm.keySet κ), ∃ p', Ws1.SwapNorm.swapIdx κ e = e → Good e p' ∧ p'.2 = p'.1 := by
    intro e
    by_cases he : Ws1.SwapNorm.swapIdx κ e = e
    · obtain ⟨p', hp'⟩ := hhalf e (raw e) he (hrawG e)
      exact ⟨p', fun _ => hp'⟩
    · exact ⟨raw e, fun h => absurd h he⟩
  choose half hhalfG using hhalf'

  set eqv := Fintype.equivFin ↥(Ws1.SwapNorm.keySet κ) with heqv
  set rep : ↥(Ws1.SwapNorm.keySet κ) → (((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) × ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ)) := fun e =>
    if Ws1.SwapNorm.swapIdx κ e = e then half e
    else if ((eqv e : ℕ)) < ((eqv (Ws1.SwapNorm.swapIdx κ e) : ℕ)) then raw e
    else (raw (Ws1.SwapNorm.swapIdx κ e)).swap with hrep
  have rep_good : ∀ e, Good e (rep e) := by
    intro e
    simp only [hrep]
    split_ifs with h1 h2
    · exact ((hhalfG e) h1).1
    · exact hrawG e
    · have := hgood_swap _ _ (hrawG (Ws1.SwapNorm.swapIdx κ e))
      rwa [Ws1.SwapNorm.swapIdx_swapIdx] at this
  have rep_swap : ∀ e, rep (Ws1.SwapNorm.swapIdx κ e) = (rep e).swap := by
    intro e
    by_cases hsd : Ws1.SwapNorm.swapIdx κ e = e
    · simp only [hrep, hsd, if_true]
      have h := ((hhalfG e) hsd).2
      exact Prod.ext h.symm h
    · have hsd2 : ¬ (e = Ws1.SwapNorm.swapIdx κ e) := fun h => hsd h.symm
      have hne : (eqv e : ℕ) ≠ (eqv (Ws1.SwapNorm.swapIdx κ e) : ℕ) := by
        intro h; apply hsd
        exact (eqv.injective (Fin.ext h)).symm
      simp only [hrep]
      rw [Ws1.SwapNorm.swapIdx_swapIdx, if_neg hsd2, if_neg hsd]
      by_cases hlt : (eqv e : ℕ) < (eqv (Ws1.SwapNorm.swapIdx κ e) : ℕ)
      · rw [if_pos hlt, if_neg (not_lt.mpr hlt.le)]
      · rw [if_neg hlt, if_pos (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hne)), Prod.swap_swap]

  set μ : ↥(Ws1.SwapNorm.keySet κ) → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun e => (rep e).1 with hμdef
  set ν : ↥(Ws1.SwapNorm.keySet κ) → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ) := fun e => (rep e).2 with hνdef

  set cls : Fin n → ↥(Ws1.SwapNorm.keySet κ) := fun j => ⟨κ j, Ws1.SwapNorm.mem_keySet_self κ j⟩ with hcls
  have hshift : ∀ (e : ↥(Ws1.SwapNorm.keySet κ)) (j : Fin n), ∃ τ : ℝ, cls j = e →
      μ₀ j = μ e * NumberField.TateGlobal.normPowChar F τ ∧ ν₀ j = ν e * (NumberField.TateGlobal.normPowChar F τ)⁻¹ := by
    intro e j
    by_cases hj : cls j = e
    · obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := rep_good e
      have hk : (e : _) = κ j := by rw [← hj]
      have hagree : ∀ x ∈ NumberField.TateGlobal.normOneIdeles F, μ₀ j x = μ e x := by
        intro x hx
        have h := (h0 ⟨x, hx⟩).1
        show μ₀ j x = (rep e).1 x
        rw [h, hk]
      obtain ⟨τ, hτ⟩ := Ws1.SwapNorm.exists_shift F (μ e) (μ₀ j) h1 (hμ₀ j) h5 (hμ₀c j) hagree
      refine ⟨τ, fun _ => ⟨hτ, ?_⟩⟩
      refine MonoidHom.ext fun z => ?_
      have hp : μ₀ j z * ν₀ j z = μ e z * ν e z := by rw [hΞ j z, h7 z]
      rw [hτ, MonoidHom.mul_apply, mul_assoc] at hp
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply]
      have hp2 : NumberField.TateGlobal.normPowChar F τ z * ν₀ j z = ν e z := mul_left_cancel hp
      rw [← hp2, mul_comm (NumberField.TateGlobal.normPowChar F τ z) (ν₀ j z), mul_assoc, mul_inv_cancel, mul_one]
    · exact ⟨0, fun h => absurd h hj⟩
  choose T hT using hshift

  set J : ↥(Ws1.SwapNorm.keySet κ) → Finset (Fin n) := fun e => Finset.univ.filter (fun j => cls j = e) with hJ
  set ψf : ↥(Ws1.SwapNorm.keySet κ) → ℂ → AdelicGL2 (𝓞 F) F → ℂ :=
    fun e s g => ∑ j ∈ J e, ψf₀ j (s - (T e j : ℂ) * Complex.I) g with hψf
  have hJmem : ∀ e j, j ∈ J e → cls j = e := fun e j hj => (Finset.mem_filter.mp hj).2
  refine ⟨↥(Ws1.SwapNorm.keySet κ), inferInstance, μ, ν, Ws1.SwapNorm.swapIdx κ, ψf, fun g => ∑ j, ψ₀ j g,
    fun e => (rep_good e).2.1, fun e => (rep_good e).2.2.1, fun e => (rep_good e).2.2.2.1, fun e => (rep_good e).2.2.2.2.1,
    fun e => (rep_good e).2.2.2.2.2.1, fun e => (rep_good e).2.2.2.2.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  ·
    intro e z
    have := (rep_good e).2.2.2.2.2.2.2 z
    exact this
  ·
    intro e
    have h := rep_swap e
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  ·
    intro e e' hne
    by_contra hcon
    push_neg at hcon
    apply hne
    apply Subtype.ext
    obtain ⟨h0, -⟩ := rep_good e
    obtain ⟨h0', -⟩ := rep_good e'
    refine Prod.ext (funext fun x => ?_) (funext fun x => ?_)
    · have h := (hcon x x.2).1
      rw [← (h0 x).1, ← (h0' x).1]; exact h
    · have h := (hcon x x.2).2
      rw [← (h0 x).2, ← (h0' x).2]; exact h
  ·
    intro e s
    refine Ws1.SwapNorm.isInducedSection_sum (J e) fun j hj => ?_
    obtain ⟨hμj, hνj⟩ := hT e j (hJmem e j hj)
    have h := hψf₀ j (s - (T e j : ℂ) * Complex.I)
    have hE := AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift F α hα hαI
    rw [hμj, hνj, (hE (μ e) (T e j) _).1, (hE (ν e) (T e j) _).2.2.2, sub_add_cancel] at h
    exact h
  ·
    intro e
    show Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => ∑ j ∈ J e, ψf₀ j (p.1 - (T e j : ℂ) * Complex.I) p.2
    refine continuous_finset_sum _ fun j _ => ?_
    exact (hψ₀jc j).comp ((continuous_fst.sub continuous_const).prodMk continuous_snd)
  ·
    intro e g
    show Differentiable ℂ fun s => ∑ j ∈ J e, ψf₀ j (s - (T e j : ℂ) * Complex.I) g
    have hd : ∀ j ∈ J e, Differentiable ℂ (fun s => ψf₀ j (s - (T e j : ℂ) * Complex.I) g) := fun j _ =>
      (hψ₀hol j g).comp (differentiable_id.sub (differentiable_const _))
    have h := Differentiable.sum hd
    rw [show (∑ i ∈ J e, fun s => ψf₀ i (s - (T e i : ℂ) * Complex.I) g) = fun s => ∑ j ∈ J e, ψf₀ j (s - (T e j : ℂ) * Complex.I) g
      from (Finset.sum_fn (J e) _)] at h
    exact h
  ·
    intro e s
    exact Ws1.SwapNorm.isArchKFinite_sum F (J e) fun j _ => hψ₀K j _
  ·
    intro e s
    exact Ws1.SwapNorm.isKfSmooth_sum F (J e) fun j _ => hψ₀sm j _
  ·
    intro e w
    choose Wf hWf using fun j : Fin n => hψ₀Ku j w
    haveI : ∀ j, FiniteDimensional ℂ (Wf j) := fun j => (hWf j).1
    refine ⟨(J e).sup Wf, inferInstance, fun s g => ?_⟩
    show (fun k : ↥(archRowIsometrySubgroup F w) => ∑ j ∈ J e, ψf₀ j (s - (T e j : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 F) F))) ∈ (J e).sup Wf
    rw [show (fun k : ↥(archRowIsometrySubgroup F w) => ∑ j ∈ J e, ψf₀ j (s - (T e j : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 F) F))) =
        ∑ j ∈ J e, (fun k : ↥(archRowIsometrySubgroup F w) => ψf₀ j (s - (T e j : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 F) F)))
      from (Finset.sum_fn (J e) _).symm]
    exact Submodule.sum_mem _ fun j hj => (Finset.le_sup (f := Wf) hj) ((hWf j).2 _ g)
  ·
    intro e N σ₀ C hC
    choose m hm using fun j : Fin n => hψ₀dec j N σ₀ C hC
    refine ⟨fun t => ∑ j ∈ J e, (1 + |T e j|) ^ N * m j (t - T e j), ?_, ?_, ?_⟩
    · exact integrable_finset_sum _ fun j _ => ((hm j).1.comp_sub_right (T e j)).const_mul _
    · choose B hB using fun j : Fin n => (hm j).2.1
      refine ⟨∑ j ∈ J e, (1 + |T e j|) ^ N * B j, fun t => Finset.sum_le_sum fun j _ => ?_⟩
      exact mul_le_mul_of_nonneg_left (hB j _) (pow_nonneg (by positivity) _)
    · intro σ' hσ' t g hg
      show (1 + |t|) ^ N * ‖∑ j ∈ J e, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (T e j : ℂ) * Complex.I) g‖ ≤
        ∑ j ∈ J e, (1 + |T e j|) ^ N * m j (t - T e j)
      calc (1 + |t|) ^ N * ‖∑ j ∈ J e, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (T e j : ℂ) * Complex.I) g‖
          ≤ (1 + |t|) ^ N * ∑ j ∈ J e, ‖ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (T e j : ℂ) * Complex.I) g‖ :=
            mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (by positivity) _)
        _ = ∑ j ∈ J e, (1 + |t|) ^ N * ‖ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (T e j : ℂ) * Complex.I) g‖ := Finset.mul_sum _ _ _
        _ ≤ ∑ j ∈ J e, (1 + |T e j|) ^ N * m j (t - T e j) := Finset.sum_le_sum fun j _ => ?_
      have harg : (σ' : ℂ) + (t : ℂ) * Complex.I - (T e j : ℂ) * Complex.I = (σ' : ℂ) + ((t - T e j : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      have hdec := (hm j).2.2 σ' hσ' (t - T e j) g hg
      rw [harg]
      calc (1 + |t|) ^ N * ‖ψf₀ j ((σ' : ℂ) + ((t - T e j : ℝ) : ℂ) * Complex.I) g‖
          ≤ ((1 + |T e j|) * (1 + |t - T e j|)) ^ N * ‖ψf₀ j ((σ' : ℂ) + ((t - T e j : ℝ) : ℂ) * Complex.I) g‖ :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (Ws1.SwapNorm.one_add_abs_le t (T e j)) N) (norm_nonneg _)
        _ = (1 + |T e j|) ^ N * ((1 + |t - T e j|) ^ N * ‖ψf₀ j ((σ' : ℂ) + ((t - T e j : ℝ) : ℂ) * Complex.I) g‖) := by
            rw [mul_pow, mul_assoc]
        _ ≤ (1 + |T e j|) ^ N * m j (t - T e j) := mul_le_mul_of_nonneg_left hdec (pow_nonneg (by positivity) _)
  ·
    have := Ws1.SwapNorm.isSlabProfile_sum (Finset.univ : Finset (Fin n)) fun j _ => hψ₀ j
    simpa using this
  ·
    intro σ' g
    have hint : ∀ j : Fin n, Integrable (fun t : ℝ => ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g) := by
      intro j
      obtain ⟨m, hmI, -, hm⟩ := hψ₀dec j 0 |σ'| {g} isCompact_singleton
      have hcont : Continuous fun t : ℝ => ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g :=
        (hψ₀jc j).comp ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).prodMk continuous_const)
      refine Integrable.mono' hmI hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
      have := hm σ' le_rfl t g (Set.mem_singleton g)
      simpa using this
    have harg : ∀ (c t : ℝ), (σ' : ℂ) + (t : ℂ) * Complex.I - (c : ℂ) * Complex.I = (σ' : ℂ) + ((t - c : ℝ) : ℂ) * Complex.I := by
      intro c t; push_cast; ring
    have hshiftI : ∀ c : ℝ, ∀ j : Fin n, ∫ t : ℝ, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (c : ℂ) * Complex.I) g =
        ∫ t : ℝ, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g := by
      intro c j
      have := integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun t : ℝ => ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I) g) c
      rw [← this]
      congr 1; funext t; rw [harg]
    have hshiftInt : ∀ c : ℝ, ∀ j : Fin n, Integrable (fun t : ℝ => ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (c : ℂ) * Complex.I) g) := by
      intro c j
      have := (hint j).comp_sub_right c
      refine this.congr (Filter.Eventually.of_forall fun t => ?_)
      show ψf₀ j ((σ' : ℂ) + ((t - c : ℝ) : ℂ) * Complex.I) g = ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (c : ℂ) * Complex.I) g
      rw [harg]
    have hE : ∀ e : ↥(Ws1.SwapNorm.keySet κ), (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g = ∑ j ∈ J e, ψ₀ j g := by
      intro e
      show (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ∑ j ∈ J e, ψf₀ j ((σ' : ℂ) + (t : ℂ) * Complex.I - (T e j : ℂ) * Complex.I) g = _
      rw [integral_finset_sum _ (fun j _ => hshiftInt (T e j) j), Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hshiftI (T e j) j, ← hψ₀rep j σ' g]
    rw [Finset.sum_congr rfl fun e _ => hE e]
    exact (Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (cls j)) fun j => ψ₀ j g).symm
  ·
    intro g hg
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg
    exact hψ₀band j g hj

end

end S_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_exists_paleyWiener_swapClosed_separated_eq_sum_of_forall_paleyWiener (solution)
