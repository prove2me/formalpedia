-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/cc8fe92d-bf40-5750-9323-2d90eadd5278

import Theorems.Thm_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_ofChar_of_forall_isReal
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
import Theorems.Thm_LanglandsTunnell_casimir_pos_or_discrete_or_zero_of_weightSet
import Theorems.Thm_AutomorphicForm_archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt
import Theorems.Thm_AutomorphicForm_apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
import Theorems.Thm_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions AutomorphicForm.compactSpace_maximalCompactAway AutomorphicForm.compactSpace_adelicMaximalCompact AutomorphicForm.isProbabilityMeasure_maximalCompactHaar AutomorphicForm.isHaarMeasure_maximalCompactHaar AutomorphicForm.compactSpace_maximalCompactAt AutomorphicForm.isProbabilityMeasure_maximalCompactAwayHaar AutomorphicForm.isHaarMeasure_maximalCompactAwayHaar AutomorphicForm.isProbabilityMeasure_maximalCompactAtHaar AutomorphicForm.isHaarMeasure_maximalCompactAtHaar"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalSpectrum.fdPins_μ AutomorphicForm.CuspidalSpectrum.fdPins_nS"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalSpectrum.fdPins_ν AutomorphicForm.CuspidalSpectrum.fdPins_gen AutomorphicForm.CuspidalSpectrum.fdPins_U AutomorphicForm.CuspidalSpectrum.fdPins_D AutomorphicForm.CuspidalSpectrum.fdPins_Z AutomorphicForm.CuspidalSpectrum.mem_detNormSlab AutomorphicForm.CuspidalSpectrum.fdPins_eq AutomorphicForm.CuspidalSpectrum.fdPins_mS AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero AutomorphicForm.mem_inducedSectionSubmodule_iff AutomorphicForm.mem_borelSubgroup_iff AutomorphicForm.borelDiagFst_apply_val AutomorphicForm.borelDiagSnd_apply_val"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem solution
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (w : InfinitePlace K) (hw : w.IsReal)
    (lam : ℂ) (hlam : ∀ x ∈ V, IsArchSmoothAt hw x ∧ archCasimirAt hw x = lam • x) :
    lam.im = 0 ∧
      (0 < lam.re ∨
        (∃ k₀ : ℕ, 2 ≤ k₀ ∧ lam = ((k₀ : ℂ) / 2) * (1 - (k₀ : ℂ) / 2) ∧
          ∀ (n : ℤ) (N' : Ideal (𝓞 K)) (tys' : AutomorphicForm.ArchTypeFamily K) (x : AdelicGL2 (𝓞 K) K → ℂ),
            N' ≠ ⊥ → x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
              (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
              (adelicBox K)) N' ⊓ archCutSubmodule K tys' →
            (∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) x) →
            HasArchCharacterAt₀ K w (archWeightCharAt hw n) x → x ≠ 0 → (k₀ : ℤ) ≤ |n| ∧ (n - k₀) % 2 = 0) ∨
        (lam = 0 ∧ ∀ x ∈ V, ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
          Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hw h) = x g)) := by
  classical

  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  obtain ⟨m, ys, hys, hyspure, hysum⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
      K c u d₁ d₂ T hc hd₁ hd hcov ξ N hN tys V hV y hy
  obtain ⟨j₀, hj₀⟩ : ∃ j, ys j ≠ 0 := by
    by_contra h
    push Not at h
    apply hy0
    rw [hysum]
    exact Finset.sum_eq_zero fun j _ => h j

  let S : Set ℤ := {n | ∃ (N' : Ideal (𝓞 K)) (χ' : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ)
      (x : AdelicGL2 (𝓞 K) K → ℂ), N' ≠ ⊥ ∧
        x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N' ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ') ∧
        x ≠ 0 ∧ χ' w = archWeightCharAt hw n}

  have memS : ∀ (n : ℤ) (N' : Ideal (𝓞 K)) (tys' : AutomorphicForm.ArchTypeFamily K) (x : AdelicGL2 (𝓞 K) K → ℂ),
      N' ≠ ⊥ → x ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N' ⊓ archCutSubmodule K tys' →
      (∀ (v : InfinitePlace K) (hv : v.IsReal), ∃ m : ℤ, HasArchCharacterAt₀ K v (archWeightCharAt hv m) x) →
      HasArchCharacterAt₀ K w (archWeightCharAt hw n) x → x ≠ 0 → n ∈ S := by
    intro n N' tys' x hN' hx hpure hxw hx0
    choose mv hmv using hpure
    let χx : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
      fun v => archWeightCharAt (hreal v) (if v = w then n else mv v (hreal v))
    have hχxw : χx w = archWeightCharAt hw n := by
      show archWeightCharAt (hreal w) (if w = w then n else mv w (hreal w)) = archWeightCharAt hw n
      rw [if_pos rfl]
    have hxχ : x ∈ archCutSubmodule K (ArchTypeFamily.ofChar K χx) := by
      refine (mem_archCutSubmodule_ofChar_iff K χx x).2 fun v => ?_
      by_cases hv : v = w
      · subst hv; rw [hχxw]; exact hxw
      · show HasArchCharacterAt₀ K v (archWeightCharAt (hreal v) (if v = w then n else mv v (hreal v))) x
        rw [if_neg hv]; exact hmv v (hreal v)
    exact ⟨N', χx, x, hN', ⟨⟨hx.1.1, hx.1.2⟩, hxχ⟩, hx0, hχxw⟩

  have posS : ∀ n ∈ S, lam.im = 0 ∧ 0 ≤ 4 * lam.re + n * (n - 2) ∧ 0 ≤ 4 * lam.re + n * (n + 2) ∧
      (0 < 4 * lam.re + n * (n - 2) → n - 2 ∈ S) ∧ (0 < 4 * lam.re + n * (n + 2) → n + 2 ∈ S) := by
    rintro n ⟨N', χ', x, hN', hx, hx0, hχ'w⟩
    have hP := AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_ofChar_of_forall_isReal
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ hreal N' hN' χ' w hw n hχ'w lam hlam x hx hx0
    obtain ⟨him, hm, hp, hlow, hrai⟩ := hP

    let χ'' : ℤ → ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ :=
      fun m v => if hv : v = w then hv ▸ archWeightCharAt hw m else χ' v
    have hχ''₁ : ∀ (m : ℤ) (v : InfinitePlace K), v ≠ w → χ'' m v = χ' v := by
      intro m v hv; show (if hv : v = w then hv ▸ archWeightCharAt hw m else χ' v) = χ' v; rw [dif_neg hv]
    have hχ''₂ : ∀ m : ℤ, χ'' m w = archWeightCharAt hw m := by
      intro m; show (if hv : w = w then hv ▸ archWeightCharAt hw m else χ' w) = archWeightCharAt hw m; rw [dif_pos rfl]
    have hG := AutomorphicForm.CuspidalConstituent.iterate_lower_mem_cut_ofChar_and_iterate_raise_mem_cut_ofChar
      K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV hreal N' hN' χ' w hw n hχ'w χ'' hχ''₁ hχ''₂ x hx
    refine ⟨him, hm, hp, fun hpos => ?_, fun hpos => ?_⟩
    · have hne := hlow.2 hpos
      have hmem := hG.1 1
      simp only [Function.iterate_one, Nat.cast_one, mul_one] at hmem
      exact ⟨N', χ'' (n - 2), _, hN', hmem, hne, hχ''₂ (n - 2)⟩
    · have hne := hrai.2 hpos
      have hmem := hG.2 1
      simp only [Function.iterate_one, Nat.cast_one, mul_one] at hmem
      exact ⟨N', χ'' (n + 2), _, hN', hmem, hne, hχ''₂ (n + 2)⟩

  have hz := memS _ N tys (ys j₀) hN (hys j₀) (hyspure j₀) (Classical.choose_spec (hyspure j₀ w hw)) hj₀
  have him : lam.im = 0 := (posS _ hz).1
  have hSne : S.Nonempty := ⟨_, hz⟩

  have hcl := LanglandsTunnell.casimir_pos_or_discrete_or_zero_of_weightSet lam.re S hSne
    (fun n hn => (posS n hn).2.1) (fun n hn => (posS n hn).2.2.1)
    (fun n hn h => (posS n hn).2.2.2.1 h) (fun n hn h => (posS n hn).2.2.2.2 h)
  have hlamre : lam = ((lam.re : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [him]
  refine ⟨him, ?_⟩
  rcases hcl with hA | ⟨k₀, hk₀, hlamk, hgap⟩ | ⟨hlam0, h0S⟩
  · exact Or.inl hA
  · refine Or.inr (Or.inl ⟨k₀, hk₀, ?_, ?_⟩)
    · rw [hlamre, hlamk]; push_cast; ring
    · intro n N' tys' x hN' hx hpure hxw hx0
      exact hgap n (memS n N' tys' x hN' hx hpure hxw hx0)
  · refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [hlamre, hlam0]; simp
    · obtain ⟨N', χ', z, hN', hzcut, hz0, hχ'w⟩ := h0S
      have hzV : z ∈ V := hzcut.1.1
      have hzs : IsArchSmoothAt hw z := (hlam z hzV).1
      have hP := AutomorphicForm.CuspidalConstituent.casimir_im_eq_zero_and_nonneg_and_lower_ne_zero_of_mem_cut_ofChar_of_forall_isReal
        K c u d₁ d₂ T hc hd₁ hd hcov ξ V hV w₀ hξ hreal N' hN' χ' w hw 0 hχ'w lam hlam z hzcut hz0
      obtain ⟨-, -, -, hlow, hrai⟩ := hP
      have hre0 : lam.re = 0 := hlam0
      have hL : archDerivAt hw .H z - Complex.I • (archDerivAt hw .E z + archDerivAt hw .Fm z) = 0 := by
        by_contra h
        have := hlow.1 h
        rw [hre0] at this; push_cast at this; linarith
      have hR : archDerivAt hw .H z + Complex.I • (archDerivAt hw .E z + archDerivAt hw .Fm z) = 0 := by
        by_contra h
        have := hrai.1 h
        rw [hre0] at this; push_cast at this; linarith

      have hzw : HasArchCharacterAt₀ K w (archWeightCharAt hw 0) z := by
        have := (mem_archCutSubmodule_ofChar_iff K χ' z).1 hzcut.2 w
        rwa [hχ'w] at this
      have hK := AutomorphicForm.archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt K w hw 0 z hzs hzw
      have hE : archDerivAt hw .E z = 0 := by
        funext g
        show archDerivAt hw .E z g = 0
        have h1 := congrFun hL g
        have h2 := congrFun hR g
        have h3 := congrFun hK g
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Int.cast_zero,
          mul_zero, zero_mul] at h1 h2 h3
        have h4 : archDerivAt hw .E z g + archDerivAt hw .Fm z g = 0 := by
          have h5 : (2 * Complex.I) * (archDerivAt hw .E z g + archDerivAt hw .Fm z g) = 0 := by
            linear_combination h2 - h1
          rcases mul_eq_zero.1 h5 with h6 | h6
          · exfalso; apply Complex.I_ne_zero; simpa using h6
          · exact h6
        linear_combination (h4 + h3) / 2
      have hF : archDerivAt hw .Fm z = 0 := by
        funext g
        show archDerivAt hw .Fm z g = 0
        have h1 := congrFun hL g
        have h2 := congrFun hR g
        have h3 := congrFun hK g
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Int.cast_zero,
          mul_zero, zero_mul] at h1 h2 h3
        have h4 : archDerivAt hw .E z g + archDerivAt hw .Fm z g = 0 := by
          have h5 : (2 * Complex.I) * (archDerivAt hw .E z g + archDerivAt hw .Fm z g) = 0 := by
            linear_combination h2 - h1
          rcases mul_eq_zero.1 h5 with h6 | h6
          · exfalso; apply Complex.I_ne_zero; simpa using h6
          · exact h6
        linear_combination (h4 - h3) / 2
      have hinv : ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
          z (g * archRealGLAt hw h) = z g :=
        fun g h hh => AutomorphicForm.apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero
          K w hw z hzs hE hF g h hh
      intro x hx g h hh
      exact AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
        K _ ξ V hV w hw z hzV hz0 hinv x hx g h hh

end S_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_casimir_real_and_pos_or_discrete_or_trivial_of_isCuspConstituent_of_forall_isReal (solution)
