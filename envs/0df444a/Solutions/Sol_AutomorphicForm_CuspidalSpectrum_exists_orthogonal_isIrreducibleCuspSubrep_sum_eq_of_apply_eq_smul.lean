-- Prove2me | solution 1 for AutomorphicForm.CuspidalSpectrum.exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/2c043f05-2927-540e-a78a-58178e3977e6

import Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import Theorems.Thm_AutomorphicForm_CuspidalSpectrum_isClosedCuspSubrep_orthogonal
import Theorems.Thm_Submodule_finiteDimensional_of_isCompactOperator_of_forall_apply_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
p2m_open "IsDedekindDomain AutomorphicForm P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul.AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering"
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Submodule p2m_export "Submodule" "finiteDimensional_inf_right finrank_eq_zero eq_of_le_of_finrank_le smul_mem mem_bot mem_sInf HasOrthogonalProjection.exists_orthogonal isClosed_topologicalClosure map_mono zero one finrank_lt_finrank_of_lt orthogonal ext isOrtho_iff_le HasOrthogonalProjection inf_orthogonal_eq_bot smul finiteDimensional_of_isCompactOperator_of_forall_apply_eq" end Submodule
p2m_open_scoped "Submodule" in
theorem Submodule.exists_le_minimal_inf_ne_bot_of_forall_sInf_of_forall_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : Submodule ℂ E → Prop)
    (hPinf : ∀ S : Set (Submodule ℂ E), (∀ N ∈ S, P N) → P (sInf S))
    (hPorth : ∀ N, P N → P Nᗮ)
    (E₀ : Submodule ℂ E) [FiniteDimensional ℂ ↥E₀]
    (hsplit : ∀ N, P N → ∀ x ∈ E₀, ∃ y ∈ N ⊓ E₀, x - y ∈ Nᗮ)
    (W : Submodule ℂ E) (hW : P W) (hWE : W ⊓ E₀ ≠ ⊥) :
    ∃ N : Submodule ℂ E, N ≤ W ∧ P N ∧ N ≠ ⊥ ∧ N ⊓ E₀ ≠ ⊥ ∧
      ∀ N' : Submodule ℂ E, P N' → N' ≤ N → N' = ⊥ ∨ N' = N := by
  classical

  have hex : ∃ k : ℕ, ∃ N : Submodule ℂ E, N ≤ W ∧ P N ∧ N ⊓ E₀ ≠ ⊥ ∧ Module.finrank ℂ ↥(N ⊓ E₀) = k :=
    ⟨_, W, le_rfl, hW, hWE, rfl⟩
  obtain ⟨N, hNW, hPN, hNE, hNk⟩ := Nat.find_spec hex
  have hmin : ∀ M : Submodule ℂ E, M ≤ W → P M → M ⊓ E₀ ≠ ⊥ →
      Module.finrank ℂ ↥(N ⊓ E₀) ≤ Module.finrank ℂ ↥(M ⊓ E₀) := by
    intro M hMW hPM hME
    rw [hNk]
    exact Nat.find_min' hex ⟨M, hMW, hPM, hME, rfl⟩

  set D : Submodule ℂ E := N ⊓ E₀ with hD
  set N' : Submodule ℂ E := sInf {M : Submodule ℂ E | P M ∧ D ≤ M} with hN'
  have hPN' : P N' := hPinf _ fun M hM => hM.1
  have hDN' : D ≤ N' := le_sInf fun M hM => hM.2
  have hN'N : N' ≤ N := sInf_le ⟨hPN, inf_le_left⟩
  have hN'E : N' ⊓ E₀ = D :=
    le_antisymm (fun x hx => ⟨hN'N hx.1, hx.2⟩) (le_inf hDN' inf_le_right)
  have hDne : D ≠ ⊥ := hNE
  refine ⟨N', hN'N.trans hNW, hPN', ?_, by rwa [hN'E], ?_⟩
  · intro h
    exact hDne (le_bot_iff.mp (h ▸ hDN'))
  · intro M hPM hMN'
    by_cases hME : M ⊓ E₀ = ⊥
    ·
      left
      have hDM : D ≤ Mᗮ := by
        intro e he
        obtain ⟨y, hy, hey⟩ := hsplit M hPM e he.2
        have hy0 : y = 0 := by
          have : y ∈ (⊥ : Submodule ℂ E) := hME ▸ hy
          exact (Submodule.mem_bot ℂ).mp this
        rw [hy0, sub_zero] at hey
        exact hey
      have hN'M : N' ≤ Mᗮ := sInf_le ⟨hPorth M hPM, hDM⟩
      have : M ≤ M ⊓ Mᗮ := le_inf le_rfl (hMN'.trans hN'M)
      rw [Submodule.inf_orthogonal_eq_bot] at this
      exact le_bot_iff.mp this
    ·
      right
      have hle : M ⊓ E₀ ≤ D := fun x hx => ⟨hN'N (hMN' hx.1), hx.2⟩
      have hfin : Module.finrank ℂ ↥D ≤ Module.finrank ℂ ↥(M ⊓ E₀) :=
        hmin M (hMN'.trans (hN'N.trans hNW)) hPM hME
      haveI : FiniteDimensional ℂ ↥D := Submodule.finiteDimensional_inf_right _ _
      have heq : M ⊓ E₀ = D := Submodule.eq_of_le_of_finrank_le hle hfin
      have hDM : D ≤ M := heq ▸ inf_le_left
      exact le_antisymm hMN' (sInf_le ⟨hPM, hDM⟩)

p2m_open_scoped "Submodule" in
theorem Submodule.exists_orthogonal_minimal_sum_eq_of_forall_sInf_of_forall_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (P : Submodule ℂ E → Prop)
    (hPinf : ∀ S : Set (Submodule ℂ E), (∀ N ∈ S, P N) → P (sInf S))
    (hPorth : ∀ N, P N → P Nᗮ)
    (E₀ : Submodule ℂ E) [FiniteDimensional ℂ ↥E₀]
    (hsplit : ∀ N, P N → ∀ x ∈ E₀, ∃ y ∈ N ⊓ E₀, x - y ∈ Nᗮ)
    (W : Submodule ℂ E) (hW : P W) (v : E) (hv : v ∈ W ⊓ E₀) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ E) (vs : Fin n → E),
      (∀ i, M i ≤ W ∧ P (M i) ∧ M i ≠ ⊥ ∧ ∀ N' : Submodule ℂ E, P N' → N' ≤ M i → N' = ⊥ ∨ N' = M i) ∧
      (Pairwise fun i j => (M i) ⟂ (M j)) ∧
      (∀ i, vs i ∈ M i ⊓ E₀) ∧
      v = ∑ i, vs i := by
  classical

  suffices key : ∀ (d : ℕ) (W : Submodule ℂ E), P W → Module.finrank ℂ ↥(W ⊓ E₀) ≤ d → ∀ v ∈ W ⊓ E₀,
      ∃ (n : ℕ) (M : Fin n → Submodule ℂ E) (vs : Fin n → E),
        (∀ i, M i ≤ W ∧ P (M i) ∧ M i ≠ ⊥ ∧ ∀ N' : Submodule ℂ E, P N' → N' ≤ M i → N' = ⊥ ∨ N' = M i) ∧
        (Pairwise fun i j => (M i) ⟂ (M j)) ∧ (∀ i, vs i ∈ M i ⊓ E₀) ∧ v = ∑ i, vs i from
    key _ W hW le_rfl v hv
  intro d
  induction d with
  | zero =>
    intro W hW hd v hv
    haveI : FiniteDimensional ℂ ↥(W ⊓ E₀) := Submodule.finiteDimensional_inf_right _ _
    have hbot : W ⊓ E₀ = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hd)
    have hv0 : v = 0 := by rw [hbot] at hv; exact (Submodule.mem_bot ℂ).mp hv
    exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hv0]⟩
  | succ d ih =>
    intro W hW hd v hv
    by_cases hv0 : v = 0
    · exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, by simp [hv0]⟩

    have hWE : W ⊓ E₀ ≠ ⊥ := fun h => hv0 ((Submodule.mem_bot ℂ).mp (h ▸ hv))
    obtain ⟨M₁, hM₁W, hPM₁, hM₁ne, hM₁E, hM₁min⟩ :=
      Submodule.exists_le_minimal_inf_ne_bot_of_forall_sInf_of_forall_orthogonal P hPinf hPorth E₀ hsplit W hW hWE

    obtain ⟨y, hy, hz⟩ := hsplit M₁ hPM₁ v hv.2
    set z := v - y with hzdef

    set W' : Submodule ℂ E := W ⊓ M₁ᗮ with hW'
    have hPW' : P W' := by
      have : W' = sInf {W, M₁ᗮ} := by rw [hW', sInf_pair]
      rw [this]
      refine hPinf _ ?_
      intro N hN
      rcases hN with rfl | rfl
      · exact hW
      · exact hPorth M₁ hPM₁
    have hzW' : z ∈ W' ⊓ E₀ := by
      refine ⟨⟨W.sub_mem hv.1 (hM₁W hy.1), hz⟩, E₀.sub_mem hv.2 hy.2⟩
    haveI : FiniteDimensional ℂ ↥(W ⊓ E₀) := Submodule.finiteDimensional_inf_right _ _
    have hlt : Module.finrank ℂ ↥(W' ⊓ E₀) < Module.finrank ℂ ↥(W ⊓ E₀) := by
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne (fun x hx => ⟨hx.1.1, hx.2⟩) fun heq => hM₁E ?_

      rw [← le_bot_iff, ← Submodule.inf_orthogonal_eq_bot M₁]
      intro x hx
      have hx' : x ∈ W' ⊓ E₀ := heq ▸ ⟨hM₁W hx.1, hx.2⟩
      exact ⟨hx.1, hx'.1.2⟩
    have hd' : Module.finrank ℂ ↥(W' ⊓ E₀) ≤ d := Nat.lt_succ_iff.mp (lt_of_lt_of_le hlt hd)
    obtain ⟨n, M, vs, hM, hMo, hvs, hsum⟩ := ih W' hPW' hd' z hzW'

    refine ⟨n + 1, Fin.cons M₁ M, Fin.cons y vs, ?_, ?_, ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_)
      · simpa only [Fin.cons_zero] using ⟨hM₁W, hPM₁, hM₁ne, hM₁min⟩
      · simp only [Fin.cons_succ]
        obtain ⟨h1, h2, h3, h4⟩ := hM i
        exact ⟨h1.trans inf_le_left, h2, h3, h4⟩
    ·
      intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;> rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · exact absurd rfl hij
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact (Submodule.isOrtho_iff_le.mpr (((hM j').1.trans inf_le_right))).symm
      · simp only [Fin.cons_zero, Fin.cons_succ]
        exact Submodule.isOrtho_iff_le.mpr ((hM i').1.trans inf_le_right)
      · simp only [Fin.cons_succ]
        exact hMo fun h => hij (congrArg Fin.succ h)
    · refine Fin.cases ?_ (fun i => ?_)
      · simpa only [Fin.cons_zero] using hy
      · simpa only [Fin.cons_succ] using hvs i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ, ← hsum, hzdef, add_sub_cancel]

p2m_open_scoped "Submodule" in
theorem Submodule.exists_mem_sub_mem_orthogonal_and_apply_eq_smul
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (N : Submodule ℂ E) [N.HasOrthogonalProjection] (T : E →ₗ[ℂ] E)
    (hTN : ∀ m ∈ N, T m ∈ N) (hTN' : ∀ m ∈ Nᗮ, T m ∈ Nᗮ) (lam : ℂ) (x : E) (hx : T x = lam • x) :
    ∃ y ∈ N, x - y ∈ Nᗮ ∧ T y = lam • y := by
  obtain ⟨y, hyN, hz⟩ := Submodule.HasOrthogonalProjection.exists_orthogonal (K := N) x
  have h1 : T y - lam • y ∈ N := N.sub_mem (hTN y hyN) (N.smul_mem lam hyN)
  have h3 : T (x - y) ∈ Nᗮ := hTN' _ hz
  have h4 : lam • (x - y) ∈ Nᗮ := Nᗮ.smul_mem lam hz
  have h5 : T (x - y) - lam • (x - y) ∈ Nᗮ := Nᗮ.sub_mem h3 h4
  have heq : T (x - y) - lam • (x - y) = -(T y - lam • y) := by
    rw [map_sub, smul_sub, hx, sub_sub_sub_cancel_left, neg_sub]
  have h2 : T y - lam • y ∈ Nᗮ := by
    have := Nᗮ.neg_mem h5
    rwa [heq, neg_neg] at this
  have h0 : T y - lam • y = 0 := by
    have hmem : T y - lam • y ∈ N ⊓ Nᗮ := ⟨h1, h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact ⟨y, hyN, hz, sub_eq_zero.mp h0⟩

namespace AutomorphicForm
p2m_export "AutomorphicForm" "ArchTypeFamily IsArchBiFinite AdelicGL2 rightConv IsFactorizableTestFn CuspidalSpectrum.isClosedCuspSubrep_orthogonal"
namespace HilbertExhaust
p2m_open "AutomorphicForm"

variable {F : Type} [Field F] [NumberField F]

theorem isClosedCuspSubrep_sInf {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (S : Set (Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ))) (hS : ∀ M ∈ S, IsClosedCuspSubrep F hΦ₀ σ ξ M) :
    IsClosedCuspSubrep F hΦ₀ σ ξ (sInf S) := by
  refine ⟨?_, fun g hg T hT => ?_, fun w k T hT => ?_, fun f tys hf hft T hT => ?_⟩
  · have : ((sInf S : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) : Set ↥(cuspSubcarrier F hΦ₀ σ ξ))
        = ⋂ M ∈ S, (M : Set ↥(cuspSubcarrier F hΦ₀ σ ξ)) := by
      ext x
      simp only [SetLike.mem_coe, Submodule.mem_sInf, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun M hM => (hS M hM).isClosed
  · exact le_sInf fun M hM => (Submodule.map_mono (sInf_le hM)).trans ((hS M hM).map_le_of_rightTranslate_fin g hg T hT)
  · exact le_sInf fun M hM => (Submodule.map_mono (sInf_le hM)).trans ((hS M hM).map_le_of_rightTranslate_arch w k T hT)
  · exact le_sInf fun M hM => (Submodule.map_mono (sInf_le hM)).trans ((hS M hM).map_le_of_rightConv f tys hf hft T hT)

end AutomorphicForm.HilbertExhaust

end

open AutomorphicForm.HilbertExhaust in

theorem solution
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (tys : ArchTypeFamily F)
    (hft : IsArchBiFinite F tys f)
    (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hTc : IsCuspLift F hΦ₀ σ ξ (fun φ => rightConv F φ f) Tc) (hcpt : IsCompactOperator Tc)
    (lam : ℂ) (hlam : lam ≠ 0) (v : ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hv : Tc v = lam • v) :
    ∃ (n : ℕ) (M : Fin n → Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (vs : Fin n → ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ i, IsIrreducibleCuspSubrep F hΦ₀ σ ξ (M i)) ∧
      (Pairwise fun i j => (M i) ⟂ (M j)) ∧
      (∀ i, vs i ∈ M i ∧ Tc (vs i) = lam • vs i) ∧
      v = ∑ i, vs i := by
  classical

  have hPinf : ∀ S : Set (Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)),
      (∀ N ∈ S, IsClosedCuspSubrep F hΦ₀ σ ξ N) → IsClosedCuspSubrep F hΦ₀ σ ξ (sInf S) :=
    fun S hS => isClosedCuspSubrep_sInf hΦ₀ σ ξ S hS
  have hPorth : ∀ N, IsClosedCuspSubrep F hΦ₀ σ ξ N → IsClosedCuspSubrep F hΦ₀ σ ξ Nᗮ :=
    fun N hN => AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal F hΦ₀ σ ξ hσ N hN

  set E₀ : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ) :=
    LinearMap.ker ((Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) - lam • LinearMap.id) with hE₀
  have hmemE₀ : ∀ w, w ∈ E₀ ↔ Tc w = lam • w := fun w => by
    rw [hE₀, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  haveI : FiniteDimensional ℂ ↥E₀ :=
    Submodule.finiteDimensional_of_isCompactOperator_of_forall_apply_eq (T := lam⁻¹ • Tc)
      (by rw [ContinuousLinearMap.coe_smul']; exact hcpt.smul lam⁻¹) E₀ fun w hw => by
      rw [ContinuousLinearMap.smul_apply, (hmemE₀ w).mp hw, smul_smul, inv_mul_cancel₀ hlam, one_smul]

  haveI : CompleteSpace ↥(cuspSubcarrier F hΦ₀ σ ξ) := by
    have : IsClosed ((cuspSubcarrier F hΦ₀ σ ξ : Submodule ℂ (Carrier F Φ₀ σ)) : Set (Carrier F Φ₀ σ)) := by
      unfold cuspSubcarrier
      exact Submodule.isClosed_topologicalClosure _
    exact this.completeSpace_coe

  have hsplit : ∀ N, IsClosedCuspSubrep F hΦ₀ σ ξ N → ∀ x ∈ E₀, ∃ y ∈ N ⊓ E₀, x - y ∈ Nᗮ := by
    intro N hN x hx
    haveI : CompleteSpace ↥N := hN.isClosed.completeSpace_coe
    have hTN : ∀ m ∈ N, Tc m ∈ N := fun m hm => hN.map_le_of_rightConv f tys hf hft Tc hTc ⟨m, hm, rfl⟩
    have hTN' : ∀ m ∈ Nᗮ, Tc m ∈ Nᗮ := fun m hm => (hPorth N hN).map_le_of_rightConv f tys hf hft Tc hTc ⟨m, hm, rfl⟩
    obtain ⟨y, hyN, hz, hTy⟩ := Submodule.exists_mem_sub_mem_orthogonal_and_apply_eq_smul N
      (Tc : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) hTN hTN' lam x ((hmemE₀ x).mp hx)
    exact ⟨y, ⟨hyN, (hmemE₀ y).mpr hTy⟩, hz⟩

  have hPtop : IsClosedCuspSubrep F hΦ₀ σ ξ ⊤ := by
    have := hPinf ∅ (fun N hN => hN.elim)
    rwa [sInf_empty] at this
  obtain ⟨n, M, vs, hM, hMo, hvs, hsum⟩ :=
    Submodule.exists_orthogonal_minimal_sum_eq_of_forall_sInf_of_forall_orthogonal
      (IsClosedCuspSubrep F hΦ₀ σ ξ) hPinf hPorth E₀ hsplit ⊤ hPtop v ⟨trivial, (hmemE₀ v).mpr hv⟩
  exact ⟨n, M, vs, fun i => ⟨(hM i).2.1, (hM i).2.2.1, (hM i).2.2.2⟩, hMo,
    fun i => ⟨(hvs i).1, (hmemE₀ _).mp (hvs i).2⟩, hsum⟩

#print axioms solution

end S_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul
end P2MW
export P2MW.S_AutomorphicForm_CuspidalSpectrum_exists_orthogonal_isIrreducibleCuspSubrep_sum_eq_of_apply_eq_smul (solution)
