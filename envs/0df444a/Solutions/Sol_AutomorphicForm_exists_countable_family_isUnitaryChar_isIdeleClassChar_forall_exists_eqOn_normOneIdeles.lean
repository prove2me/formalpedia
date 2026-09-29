-- Prove2me | solution 1 for AutomorphicForm.exists_countable_family_isUnitaryChar_isIdeleClassChar_forall_exists_eqOn_normOneIdeles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/3987a267-3370-5d47-856b-26b76ac1bc40

import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_countable_family_isUnitaryChar_isIdeleClassChar_forall_exists_eqOn_normOneIdeles
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false

open NumberField

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "IsIdeleClassChar IsUnitaryChar"
namespace E3Count
p2m_open "AutomorphicForm"

theorem norm_sub_one_sq (z : ℂ) (hz : ‖z‖ = 1) : ‖z - 1‖ ^ 2 = 2 - 2 * z.re := by
  have hx : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz, one_pow]
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
  nlinarith [hx]

theorem norm_sq_sub_one_sq (z : ℂ) (hz : ‖z‖ = 1) :
    ‖z ^ 2 - 1‖ ^ 2 = ‖z - 1‖ ^ 2 * (4 - ‖z - 1‖ ^ 2) := by
  have hx : z.re * z.re + z.im * z.im = 1 := by
    rw [← Complex.normSq_apply, ← Complex.sq_norm, hz, one_pow]
  have hz2 : ‖z ^ 2‖ = 1 := by rw [norm_pow, hz, one_pow]
  rw [norm_sub_one_sq (z ^ 2) hz2, norm_sub_one_sq z hz]
  have hre : (z ^ 2).re = z.re * z.re - z.im * z.im := by rw [pow_two, Complex.mul_re]
  rw [hre]
  nlinarith [hx]

theorem exists_pow_one_le_norm_sub_one (z : ℂ) (hz : ‖z‖ = 1) (hz1 : z ≠ 1) :
    ∃ n : ℕ, 1 ≤ ‖z ^ n - 1‖ := by
  by_contra h
  push Not at h
  have a0 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
  have hsq : ∀ n : ℕ, ‖z ^ n - 1‖ ^ 2 < 1 := fun n => by
    have h1 := h n
    have h0 := norm_nonneg (z ^ n - 1)
    nlinarith
  have step : ∀ k : ℕ, 3 ^ k * ‖z - 1‖ ^ 2 ≤ ‖z ^ (2 ^ k) - 1‖ ^ 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hzk : ‖z ^ (2 ^ k)‖ = 1 := by rw [norm_pow, hz, one_pow]
      have hlt := hsq (2 ^ k)
      rw [pow_succ 2 k, pow_mul, norm_sq_sub_one_sq _ hzk]
      have hnn : 0 ≤ ‖z ^ 2 ^ k - 1‖ ^ 2 := by positivity
      have h3 : 0 ≤ (3 : ℝ) ^ k * ‖z - 1‖ ^ 2 := by positivity
      have h3k : (3 : ℝ) ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
      have hb : 0 ≤ ‖z ^ 2 ^ k - 1‖ ^ 2 * (1 - ‖z ^ 2 ^ k - 1‖ ^ 2) := mul_nonneg hnn (sub_nonneg.mpr hlt.le)
      rw [h3k]
      nlinarith [ih, hlt, hnn, hb]
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖z - 1‖ ^ 2)⁻¹ (by norm_num : (1 : ℝ) < 3)
  have hpos : 0 < ‖z - 1‖ ^ 2 := by positivity
  have h1 : 1 ≤ 3 ^ k * ‖z - 1‖ ^ 2 := by
    have := mul_lt_mul_of_pos_right hk hpos
    rw [inv_mul_cancel₀ hpos.ne'] at this
    exact this.le
  have := hsq (2 ^ k)
  linarith [step k]

theorem countable_of_one_le_dist {X : Type*} [MetricSpace X] [SecondCountableTopology X] (T : Set X)
    (hT : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → 1 ≤ dist x y) : T.Countable := by
  classical
  obtain ⟨B, hBc, -, hB⟩ := TopologicalSpace.exists_countable_basis X
  have hx : ∀ x : X, ∃ b ∈ B, x ∈ b ∧ b ⊆ Metric.ball x (1 / 2) := fun x =>
    hB.exists_subset_of_mem_open (Metric.mem_ball_self (by norm_num)) Metric.isOpen_ball
  choose f hfB hxf hfball using hx
  have hinj : Set.InjOn f T := by
    intro x hx y hy hxy
    by_contra hne
    have hy' : y ∈ Metric.ball x (1 / 2) := hfball x (hxy ▸ hxf y)
    have := hT x hx y hy hne
    rw [Metric.mem_ball, dist_comm] at hy'
    linarith
  obtain ⟨g, hg⟩ := (Set.countable_iff_exists_injOn).mp hBc
  exact (Set.countable_iff_exists_injOn).mpr ⟨fun x => g (f x), fun x hx y hy hxy => hinj hx hy (hg (hfB x) (hfB y) hxy)⟩

variable (K : Type) [Field K] [NumberField K]

def Adm (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) : Prop :=
  AutomorphicForm.IsUnitaryChar (𝓞 K) K μ ∧ AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ ∧
    Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)

variable {K}

theorem secondCountableTopology_units : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := by
  haveI := NumberField.AdeleRing.secondCountableTopology K
  haveI : SecondCountableTopology (MulOpposite (AdeleRing (𝓞 K) K)) :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem apply_eq_of_principal_mul {μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ} (hμ : AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ)
    (η : Kˣ) (κ : (AdeleRing (𝓞 K) K)ˣ) :
    μ (Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom η * κ) = μ κ := by
  rw [map_mul, RingHom.toMonoidHom_eq_coe, hμ η, one_mul]

end AutomorphicForm.E3Count

open AutomorphicForm.E3Count in
theorem solution
    (K : Type) [Field K] [NumberField K] :
    ∃ (ι : Type) (_ : Countable ι) (χ : ι → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ)),
      (∀ i, AutomorphicForm.IsUnitaryChar (𝓞 K) K (χ i) ∧ AutomorphicForm.IsIdeleClassChar (𝓞 K) K (χ i) ∧
        Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((χ i z : ℂˣ) : ℂ)) ∧
      ∀ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ,
        AutomorphicForm.IsUnitaryChar (𝓞 K) K μ → AutomorphicForm.IsIdeleClassChar (𝓞 K) K μ →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)) →
        ∃ i, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ z = χ i z := by
  classical
  haveI : SecondCountableTopology (AdeleRing (𝓞 K) K)ˣ := secondCountableTopology_units
  obtain ⟨F, hFc, hF1, hFcov⟩ :=
    NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul K
  haveI : CompactSpace F := isCompact_iff_compactSpace.mp hFc

  let T : Set C(F, ℂ) := {g | ∃ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, Adm K μ ∧ ∀ x : F, g x = ((μ (x : (AdeleRing (𝓞 K) K)ˣ) : ℂˣ) : ℂ)}

  have hsep : ∀ g ∈ T, ∀ g' ∈ T, g ≠ g' → 1 ≤ dist g g' := by
    rintro g ⟨μ, ⟨hμu, hμc, -⟩, hg⟩ g' ⟨μ', ⟨hμ'u, hμ'c, -⟩, hg'⟩ hne

    have hx0 : ∃ x : F, g x ≠ g' x := by
      by_contra h
      push Not at h
      exact hne (ContinuousMap.ext h)
    obtain ⟨x₀, hx₀⟩ := hx0
    set ψ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := μ / μ' with hψ
    have hψapply : ∀ z, ((ψ z : ℂˣ) : ℂ) = ((μ z : ℂˣ) : ℂ) * (((μ' z : ℂˣ) : ℂ))⁻¹ := fun z => by
      simp only [hψ, MonoidHom.div_apply, div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    have hψnorm : ∀ z, ‖((ψ z : ℂˣ) : ℂ)‖ = 1 := fun z => by
      rw [hψapply, norm_mul, norm_inv, hμu z, hμ'u z, inv_one, mul_one]
    have hψclass : AutomorphicForm.IsIdeleClassChar (𝓞 K) K ψ := fun u => by
      simp only [hψ, MonoidHom.div_apply, hμc u, hμ'c u, div_one]
    set w : ℂ := ((ψ (x₀ : (AdeleRing (𝓞 K) K)ˣ) : ℂˣ) : ℂ) with hw
    have hw1 : w ≠ 1 := by
      intro h1
      apply hx₀
      rw [hg, hg']
      have hne0 : ((μ' (x₀ : (AdeleRing (𝓞 K) K)ˣ) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have := hψapply (x₀ : (AdeleRing (𝓞 K) K)ˣ)
      rw [← hw, h1] at this
      field_simp at this
      exact this.symm
    obtain ⟨n, hn⟩ := exists_pow_one_le_norm_sub_one w (hψnorm _) hw1

    have hxn : (x₀ : (AdeleRing (𝓞 K) K)ˣ) ^ n ∈ NumberField.TateGlobal.normOneIdeles K :=
      pow_mem (hF1 x₀.2) n
    obtain ⟨η, κ, hκ, hdec⟩ := hFcov _ hxn
    have hwn : w ^ n = ((ψ κ : ℂˣ) : ℂ) := by
      rw [hw, ← Units.val_pow_eq_pow_val, ← map_pow, hdec, apply_eq_of_principal_mul hψclass]
    rw [hwn, hψapply] at hn

    have hk1 : 1 ≤ ‖((μ κ : ℂˣ) : ℂ) - ((μ' κ : ℂˣ) : ℂ)‖ := by
      have hne0 : ((μ' κ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
      have : ((μ κ : ℂˣ) : ℂ) * (((μ' κ : ℂˣ) : ℂ))⁻¹ - 1 = (((μ κ : ℂˣ) : ℂ) - ((μ' κ : ℂˣ) : ℂ)) * (((μ' κ : ℂˣ) : ℂ))⁻¹ := by
        field_simp
      rw [this, norm_mul, norm_inv, hμ'u κ, inv_one, mul_one] at hn
      exact hn
    calc (1 : ℝ) ≤ ‖((μ κ : ℂˣ) : ℂ) - ((μ' κ : ℂˣ) : ℂ)‖ := hk1
      _ = dist (g ⟨κ, hκ⟩) (g' ⟨κ, hκ⟩) := by rw [dist_eq_norm, hg, hg']
      _ ≤ dist g g' := ContinuousMap.dist_apply_le_dist _
  have hTc : T.Countable := countable_of_one_le_dist T hsep
  haveI : Countable T := hTc.to_subtype

  have hT : ∀ t : T, ∃ μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ, Adm K μ ∧ ∀ x : F, (t : C(F, ℂ)) x = ((μ (x : (AdeleRing (𝓞 K) K)ˣ) : ℂˣ) : ℂ) :=
    fun t => t.2
  choose χ hχadm hχres using hT
  refine ⟨T, inferInstance, χ, fun t => hχadm t, fun μ hμu hμc hμcont => ?_⟩
  let g : C(F, ℂ) := ⟨fun x => ((μ (x : (AdeleRing (𝓞 K) K)ˣ) : ℂˣ) : ℂ), hμcont.comp continuous_subtype_val⟩
  have hgT : g ∈ T := ⟨μ, ⟨hμu, hμc, hμcont⟩, fun x => rfl⟩
  refine ⟨⟨g, hgT⟩, fun z hz => ?_⟩
  obtain ⟨η, κ, hκ, rfl⟩ := hFcov z hz
  rw [apply_eq_of_principal_mul hμc, apply_eq_of_principal_mul (hχadm ⟨g, hgT⟩).2.1]
  exact Units.ext ((hχres ⟨g, hgT⟩ ⟨κ, hκ⟩).symm ▸ rfl)

end
end S_AutomorphicForm_exists_countable_family_isUnitaryChar_isIdeleClassChar_forall_exists_eqOn_normOneIdeles
end P2MW
export P2MW.S_AutomorphicForm_exists_countable_family_isUnitaryChar_isIdeleClassChar_forall_exists_eqOn_normOneIdeles (solution)
