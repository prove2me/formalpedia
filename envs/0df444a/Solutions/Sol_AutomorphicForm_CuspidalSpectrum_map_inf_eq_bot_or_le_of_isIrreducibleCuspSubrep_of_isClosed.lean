-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/319b1b81-f37e-5dc5-aaec-149a731898fb

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_exists_idempotent_cutProjector_of_isCompact
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_rightTranslate_mem_cuspMemberSubmodule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
p2m_attr_erase "instance" "AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self"
p2m_attr_erase "simp" "AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace F55M

variable (F : Type) [Field F] [NumberField F]

def appendFamily (t₁ t₂ : ArchTypeFamily F) : ArchTypeFamily F :=
  ⟨fun w => t₁.card w + t₂.card w, fun w => Fin.append (t₁.rep w) (t₂.rep w)⟩

theorem archCutSubmodule_le_append_left (t₁ t₂ : ArchTypeFamily F) :
    archCutSubmodule F t₁ ≤ archCutSubmodule F (appendFamily F t₁ t₂) := by
  intro φ hφ
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt F w (t₁.rep w i)) ≤ ⨆ j, archTypeSubmoduleAt F w ((appendFamily F t₁ t₂).rep w j) := by
    refine iSup_le fun i => ?_
    have : archTypeSubmoduleAt F w (t₁.rep w i) =
        archTypeSubmoduleAt F w ((appendFamily F t₁ t₂).rep w (Fin.castAdd (t₂.card w) i)) := by
      simp [appendFamily]
    rw [this]
    exact le_iSup (fun j => archTypeSubmoduleAt F w ((appendFamily F t₁ t₂).rep w j)) _
  exact hle (hφ w)

theorem archCutSubmodule_le_append_right (t₁ t₂ : ArchTypeFamily F) :
    archCutSubmodule F t₂ ≤ archCutSubmodule F (appendFamily F t₁ t₂) := by
  intro φ hφ
  rw [mem_archCutSubmodule_iff] at hφ ⊢
  intro w
  have hle : (⨆ i, archTypeSubmoduleAt F w (t₂.rep w i)) ≤ ⨆ j, archTypeSubmoduleAt F w ((appendFamily F t₁ t₂).rep w j) := by
    refine iSup_le fun i => ?_
    have : archTypeSubmoduleAt F w (t₂.rep w i) =
        archTypeSubmoduleAt F w ((appendFamily F t₁ t₂).rep w (Fin.natAdd (t₁.card w) i)) := by
      simp [appendFamily]
    rw [this]
    exact le_iSup (fun j => archTypeSubmoduleAt F w ((appendFamily F t₁ t₂).rep w j)) _
  exact hle (hφ w)

theorem exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys := by
  refine Submodule.span_induction (p := fun φ _ => ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, -, tys, htys⟩; exact ⟨tys, htys⟩
  · exact ⟨⟨fun _ => 0, fun _ i => i.elim0⟩, Submodule.zero_mem _⟩
  · rintro a b - - ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨appendFamily F t₁ t₂, Submodule.add_mem _ (archCutSubmodule_le_append_left F t₁ t₂ h₁)
      (archCutSubmodule_le_append_right F t₁ t₂ h₂)⟩
  · rintro c a - ⟨t, h⟩; exact ⟨t, Submodule.smul_mem _ c h⟩

theorem isCuspSubrep_iInf (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (p : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) → Prop) (hp : ∀ W, p W → IsCuspSubrep F pins ξ W)
    (W₁ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (h₁ : p W₁) :
    IsCuspSubrep F pins ξ (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : p W), W) := by
  have key : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ},
      φ ∈ (⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : p W), W) ↔ ∀ W, p W → φ ∈ W := by
    intro φ
    simp only [Submodule.mem_iInf]
  refine ⟨(iInf₂_le W₁ h₁).trans (hp W₁ h₁).le, ?_, ?_, ?_⟩
  · intro g hg φ hφ
    exact key.mpr fun W hW => (hp W hW).rightTranslate_fin_mem g hg φ (key.mp hφ W hW)
  · intro w k φ hφ
    exact key.mpr fun W hW => (hp W hW).rightTranslate_arch_mem w k φ (key.mp hφ W hW)
  · intro f tys hf hft φ hφ
    exact key.mpr fun W hW => (hp W hW).rightConv_mem f tys hf hft φ (key.mp hφ W hW)

end F55M

end

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsIrreducibleCuspSubrep F hΦ₀ σ ξ M)
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hYc : Y ≤ cuspMemberSubmodule F Φ₀ ξ)
    (hYM : ∀ (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : ψ ∈ Y), toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hYc hψ⟩ ∈ M)
    (hYU : ∀ ψ ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (L : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hL : IsClosed (L : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hLk : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L),
        rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L))
    (hLhecke : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ (n : ℕ) (reps : Fin n → AdelicGL2 (𝓞 F) F),
      (∀ i, ∃ u ∈ U, ∃ u' ∈ U, reps i = u * g * u') →
      (∀ x : AdelicGL2 (𝓞 F) F, (∃ u ∈ U, ∃ u' ∈ U, x = u * g * u') → ∃ i, ∃ u ∈ U, x = reps i * u) →
      (∀ i j, (reps i)⁻¹ * reps j ∈ U → i = j) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L) ⊓ Representation.invariants ((rightRegular F).comp U.subtype),
        (fun x => ∑ i, φ (x * reps i)) ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L))
    (hLconv : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F h → IsArchBiFinite F tys h →
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x) →
      ∀ φ ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L), rightConv F φ h ∈ Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L)) :
    Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ⊓ L = ⊥ ∨
      Submodule.map ((toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc)) ⊤ ≤ L := by
  classical
  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    unfold cuspSubcarrier; exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  set pins : CarrierPins F := fdPins F Φ₀ with hpins
  set Lf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
    Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) L) with hLf
  have memLf : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ Lf ↔
      ∃ hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ, toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ ∈ L := by
    intro φ
    constructor
    · rintro ⟨ψ, hψ, rfl⟩; exact ⟨ψ.2, by simpa using hψ⟩
    · rintro ⟨hφ, hl⟩; exact ⟨⟨φ, hφ⟩, hl, rfl⟩
  set LU : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Representation.invariants ((rightRegular F).comp U.subtype) with hLU
  have memLU : ∀ {φ : AdelicGL2 (𝓞 F) F → ℂ}, φ ∈ LU ↔ ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, φ (x * u) = φ x := by
    intro φ
    rw [hLU, Representation.mem_invariants]
    constructor
    · intro h x u hu; exact congrFun (h ⟨u, hu⟩) x
    · intro h u; funext x; exact h x u u.2
  set A : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := archCutSubmodule F tys with hA

  set VM : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := cuspKFiniteSubmodule F pins ξ ⊓
    Submodule.map (cuspMemberSubmodule F Φ₀ ξ).subtype (Submodule.comap (toCuspSubcarrier F hΦ₀ σ ξ) M) with hVM
  have hVM : IsCuspSubrep F pins ξ VM :=
    AutomorphicForm.CuspidalSpectrum.isCuspSubrep_cuspKFiniteSubmodule_fdPins_inf_map_subtype_comap_toCuspSubcarrier_of_isClosedCuspSubrep
      F hΦ₀ σ ξ hσ M hM.1
  have hKFm : cuspKFiniteSubmodule F pins ξ ≤ cuspMemberSubmodule F Φ₀ ξ := by
    refine Submodule.span_le.mpr ?_
    rintro φ ⟨hsat, hcont, -⟩
    have h1 := hsat 1
    have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
    rw [this] at h1
    exact ⟨h1, hcont⟩
  have hYVM : Y ≤ VM := by
    intro y hy
    refine ⟨Submodule.subset_span ⟨fun g => ?_, (hYc hy).2, tys, hYt hy⟩, ⟨⟨y, hYc hy⟩, hYM y hy, rfl⟩⟩
    exact (AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g y (hYc hy)).1
  have hYLU : Y ≤ LU := fun y hy => memLU.mpr (hYU y hy)

  let p : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) → Prop := fun W => IsCuspSubrep F pins ξ W ∧ VM ⊓ LU ⊓ A ⊓ Lf ≤ W
  set W₀ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := ⨅ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (_ : p W), W with hW₀
  have hpVM : p VM := ⟨hVM, fun φ hφ => hφ.1.1.1⟩
  have hW₀ : IsCuspSubrep F pins ξ W₀ := F55M.isCuspSubrep_iInf F pins ξ p (fun W hW => hW.1) VM hpVM
  have hW₀VM : W₀ ≤ VM := iInf₂_le VM hpVM
  have hZW₀ : VM ⊓ LU ⊓ A ⊓ Lf ≤ W₀ := le_iInf₂ fun W hW => hW.2
  have hW₀m : W₀ ≤ cuspMemberSubmodule F Φ₀ ξ := hW₀VM.trans (hVM.le.trans hKFm)

  have hcut : W₀ ⊓ LU ⊓ A ≤ Lf :=
    AutomorphicForm.CuspidalConstituent.iInf_isCuspSubrep_inf_invariants_inf_archCutSubmodule_le F Φ₀ ξ U hU O hO hUO tys
      VM hVM Lf hLk hLhecke hLconv

  set N : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    (Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ)
      (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W₀)).topologicalClosure with hN
  have hNc : IsClosedCuspSubrep F hΦ₀ σ ξ N :=
    AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep F hΦ₀ σ ξ W₀ hW₀
  have hNM : N ≤ M := by
    rw [hN]
    refine Submodule.topologicalClosure_minimal _ ?_ hM.1.isClosed
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨-, ⟨m, hm, hmw⟩⟩ := hW₀VM hw
    have : m = w := Subtype.ext hmw
    rw [this] at hm
    exact hm
  rcases hM.2.2 N hNc hNM with h0 | hNM'
  ·
    left
    rw [eq_bot_iff]
    rintro v ⟨⟨y, -, rfl⟩, hvL⟩
    have hyLf : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ Lf := memLf.mpr ⟨hYc y.2, hvL⟩
    have hyW₀ : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ W₀ := hZW₀ ⟨⟨⟨hYVM y.2, hYLU y.2⟩, hYt y.2⟩, hyLf⟩
    have hvN : (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc) y ∈ N := by
      rw [hN]
      exact Submodule.le_topologicalClosure _ ⟨⟨y, hYc y.2⟩, hyW₀, rfl⟩
    rw [h0, Submodule.mem_bot] at hvN
    rw [Submodule.mem_bot]
    exact hvN
  ·
    right
    rintro _ ⟨y, -, rfl⟩
    obtain ⟨P, -, -, hPid, hPcut, -⟩ :=
      AutomorphicForm.CuspidalSpectrum.exists_idempotent_cutProjector_of_isCompact F hΦ₀ σ ξ hσ U hU O hO hUO tys
    set v := (toCuspSubcarrier F hΦ₀ σ ξ).comp (Submodule.inclusion hYc) y with hv
    have hvdef : v = toCuspSubcarrier F hΦ₀ σ ξ ⟨y, hYc y.2⟩ := rfl
    have hPv : P v = v := by rw [hvdef]; exact hPid y (hYc y.2) (hYU y y.2) (hYt y.2)
    have hvM : v ∈ M := by rw [hvdef]; exact hYM y y.2

    have hPW₀ : ∀ x ∈ Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ) (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W₀),
        P x ∈ L := by
      rintro _ ⟨w, hw, rfl⟩
      have hwK : (w : AdelicGL2 (𝓞 F) F → ℂ) ∈ cuspKFiniteSubmodule F pins ξ := hVM.le (hW₀VM hw)
      obtain ⟨tys', htys'⟩ := F55M.exists_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule F pins ξ hwK
      obtain ⟨w', hw'm, hw'U, hw't, hw'V, hPw⟩ := hPcut w w.2 ⟨tys', htys'⟩
      have hw'W₀ : w' ∈ W₀ := hw'V W₀ hW₀.rightTranslate_fin_mem hW₀.rightTranslate_arch_mem hw
      have hw'Lf : w' ∈ Lf := hcut ⟨⟨hw'W₀, memLU.mpr hw'U⟩, hw't⟩
      obtain ⟨hm', hl'⟩ := memLf.mp hw'Lf
      have : toCuspSubcarrier F hΦ₀ σ ξ w = toCuspSubcarrier F hΦ₀ σ ξ ⟨w, w.2⟩ := rfl
      rw [this, hPw]
      exact hl'

    have hPN : ∀ x ∈ N, P x ∈ L := by
      intro x hx
      rw [hN] at hx
      have hcl : (P : ↥(cuspSubcarrier F hΦ₀ σ ξ) → ↥(cuspSubcarrier F hΦ₀ σ ξ)) ''
          closure ((Submodule.map (toCuspSubcarrier F hΦ₀ σ ξ) (Submodule.comap (cuspMemberSubmodule F Φ₀ ξ).subtype W₀)) : Set _) ⊆
          closure (L : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
        refine (image_closure_subset_closure_image P.continuous).trans (closure_mono ?_)
        rintro _ ⟨z, hz, rfl⟩
        exact hPW₀ z hz
      have := hcl ⟨x, by rwa [← Submodule.topologicalClosure_coe], rfl⟩
      rwa [hL.closure_eq] at this
    have := hPN v (hNM' ▸ hvM)
    rwa [hPv] at this

end S_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_map_inf_eq_bot_or_le_of_isIrreducibleCuspSubrep_of_isClosed (solution)
