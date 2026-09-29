-- Prove2me | solution 1 for AutomorphicForm.integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6268ca51-e560-5412-8bb0-c260e3b20886

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
import Definitions.Def_AutomorphicForm_GeometricRemainder
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_AutomorphicForm_TruncationOperator
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicHeight
import Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_AutomorphicForm_ResidualSpan
import Definitions.Def_NumberField_NormPowChar
import Theorems.Thm_AutomorphicForm_orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
import Theorems.Thm_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift
import Theorems.Thm_AutomorphicForm_exists_forall_inv_vol_mul_axis_continuation_weylIntertwining_eq_sum_and_exists_forall_eq_sum_of_paleyWiener_matched_swap
import Theorems.Thm_AutomorphicForm_integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
import Theorems.Thm_AutomorphicForm_exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instMeasurableSpaceRestrictedProduct_definitions instBorelSpaceRestrictedProduct_definitions MeasureTheory.instMeasurableNegSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableMulSubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemSubgroup_definitions MeasureTheory.instMeasurableMul₂SubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableAddSubtypeMemAddSubgroup_definitions MeasureTheory.instMeasurableInvSubtypeMemSubgroup_definitions"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22LocalIntegral_zero_left LanglandsTunnell.RankinSelberg.rs22GlobalIntegral_zero_right ContinuousAddEquiv.preimage_mulLeft_smul"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

noncomputable section

namespace Ws31
namespace C4

open MeasureTheory AutomorphicForm NumberField.TateGlobal

variable (K : Type) [Field K] [NumberField K]

theorem etaFst_mul_normPowChar (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαI : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm K x) (τ t : ℝ) :
    etaFst (μ * normPowChar K τ) α hα ((t : ℂ) * Complex.I) = etaFst μ α hα (((t + τ : ℝ) : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaFst_apply, etaFst_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαI, mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 2
  push_cast; ring

theorem etaSnd_mul_normPowChar_inv (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαI : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm K x) (τ t : ℝ) :
    etaSnd (ν * (normPowChar K τ)⁻¹) α hα ((t : ℂ) * Complex.I) = etaSnd ν α hα (((t + τ : ℝ) : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaSnd_apply, etaSnd_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαI, mul_assoc,
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 2
  push_cast; ring

theorem etaFst_mul_normPowChar' (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαI : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm K x) (τ : ℝ) (s : ℂ) :
    etaFst (μ * normPowChar K τ) α hα s = etaFst μ α hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaFst_apply, etaFst_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαI, mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 2
  ring

theorem etaFst_mul_normPowChar_inv' (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαI : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm K x) (τ : ℝ) (s : ℂ) :
    etaFst (μ * (normPowChar K τ)⁻¹) α hα s = etaFst μ α hα (s - (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaFst_apply, etaFst_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαI, mul_assoc,
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 2
  ring

theorem etaSnd_mul_normPowChar' (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαI : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm K x) (τ : ℝ) (s : ℂ) :
    etaSnd (ν * normPowChar K τ) α hα s = etaSnd ν α hα (s - (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaSnd_apply, etaSnd_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαI, mul_assoc,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 2
  ring

theorem etaSnd_mul_normPowChar_inv' (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαI : ∀ x, ((α x : ℝˣ) : ℝ) = ideleNorm K x) (τ : ℝ) (s : ℂ) :
    etaSnd (ν * (normPowChar K τ)⁻¹) α hα s = etaSnd ν α hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [etaSnd_apply, etaSnd_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_mul, Units.val_mul,
    MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    cpowChar_apply_val, cpowChar_apply_val, coe_normPowChar_apply, hαI, mul_assoc,
    ← Complex.cpow_neg, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (ideleNorm_pos x).ne')]
  congr 2
  ring

omit [NumberField K] in
theorem exists_not_mem_finset [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S := by
  classical
  by_contra h
  push Not at h

  have key : ∀ p : ℕ, p.Prime → ∃ v : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ v.asIdeal := by
    intro p hp
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hprime : (Ideal.span {(p : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp hp)
    haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
      hprime.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0)
    have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ Ideal.span {(p : ℤ)} := by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le
    obtain ⟨P, hPmax, hP⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) hker
    have hpP : (p : 𝓞 K) ∈ P := by
      have : (p : ℤ) ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) P := by rw [hP]; exact Ideal.mem_span_singleton_self _
      rw [Ideal.mem_comap] at this
      exact_mod_cast this
    have hPne : P ≠ ⊥ := by
      intro hb
      rw [hb, Ideal.mem_bot] at hpP
      exact hp.ne_zero (by exact_mod_cast hpP)
    exact ⟨⟨P, hPmax.isPrime, hPne⟩, hpP⟩
  choose vp hvp using key

  have hinj : ∀ p q : ℕ, ∀ (hp : p.Prime) (hq : q.Prime), vp p hp = vp q hq → p = q := by
    intro p q hp hq hpq
    by_contra hne
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have h1 : (1 : 𝓞 K) ∈ (vp p hp).asIdeal := by
      have hab' := congrArg (Int.cast : ℤ → 𝓞 K) hab
      push_cast at hab'
      rw [← hab']
      exact (vp p hp).asIdeal.add_mem ((vp p hp).asIdeal.mul_mem_left _ (hvp p hp))
        ((vp p hp).asIdeal.mul_mem_left _ (hpq ▸ hvp q hq))
    exact (vp p hp).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

  let F : {p : ℕ // p.Prime} → {v : HeightOneSpectrum (𝓞 K) // v ∈ S} := fun p => ⟨vp p.1 p.2, h _⟩
  have hF : Function.Injective F := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    exact Subtype.ext (hinj p q hp hq (congrArg Subtype.val hpq))
  haveI : Finite {v : HeightOneSpectrum (𝓞 K) // v ∈ S} := Finite.of_fintype _
  have : Finite {p : ℕ // p.Prime} := Finite.of_injective F hF
  exact Nat.infinite_setOf_prime (Set.finite_coe_iff.mp this)

theorem ne_bot_of_forall_dvd_mem {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ S) : N ≠ ⊥ := by
  intro hb
  obtain ⟨v, hv⟩ := exists_not_mem_finset K S
  exact hv (hN v (by rw [hb]; exact dvd_zero _))

open NumberField.AdelicLevel in
theorem idealBound_mul_le {N M : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hM : M ≠ ⊥) (v : HeightOneSpectrum (𝓞 K)) :
    idealBound (𝓞 K) (N * M) v ≤ idealBound (𝓞 K) N v := by
  classical
  have hNM : N * M ≠ ⊥ := mul_ne_zero hN hM
  rw [idealBound_of_ne_bot hNM, idealBound_of_ne_bot hN, WithZero.exp_le_exp, neg_le_neg_iff, Int.ofNat_le,
    ← Associates.mk_mul_mk,
    Associates.count_mul (Associates.mk_ne_zero.mpr hN) (Associates.mk_ne_zero.mpr hM)
      (Associates.irreducible_mk.mpr v.irreducible)]
  exact Nat.le_add_right _ _

open NumberField.AdelicLevel in
theorem idealBall_mul_subset {N M : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hM : M ≠ ⊥) :
    idealBall (𝓞 K) K (N * M) ⊆ idealBall (𝓞 K) K N := fun _ hx v =>
  (hx v).trans (idealBound_mul_le K hN hM v)

open NumberField.AdelicLevel in
theorem principalLevel_mul_le {N M : Ideal (𝓞 K)} (hN : N ≠ ⊥) (hM : M ≠ ⊥) :
    principalLevel (𝓞 K) K (N * M) ≤ principalLevel (𝓞 K) K N := by
  have hball := idealBall_mul_subset K hN hM
  have h1 : ∀ m, IsLevelOneMatrix (𝓞 K) K (N * M) m → IsLevelOneMatrix (𝓞 K) K N m :=
    fun m hm => ⟨⟨hm.integral, hball hm.lowerLeft⟩, hball hm.lowerRight⟩
  have hfin : finiteLevelOne (𝓞 K) K (N * M) ≤ finiteLevelOne (𝓞 K) K N :=
    fun g hg => ⟨h1 _ hg.1, h1 _ hg.2⟩
  have hlev : levelOne (𝓞 K) K (N * M) ≤ levelOne (𝓞 K) K N := Subgroup.comap_mono hfin
  exact inf_le_inf hlev (Subgroup.map_mono hlev)

theorem shifted_datum (φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ) (O : Set ℂ) (E Nn : ℂ → AdelicGL2 (𝓞 K) K → ℂ) (c : ℝ)
    (h : IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => E s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nn s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => E p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nn p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        E s g = φ s g + ∑' ξ : K, φ s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nn s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φ s) g)) :
    IsOpen ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧ IsPreconnected ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧ {s : ℂ | s.re = 0} ⊆ ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => (fun s' g' => E (s' + ((c : ℂ) * Complex.I)) g') s g) ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => (fun s' g' => Nn (s' + ((c : ℂ) * Complex.I)) g') s g) ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => (fun s' g' => E (s' + ((c : ℂ) * Complex.I)) g') p.1 p.2) (((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => (fun s' g' => Nn (s' + ((c : ℂ) * Complex.I)) g') p.1 p.2) (((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        (fun s' g' => E (s' + ((c : ℂ) * Complex.I)) g') s g = (fun s' => φ (s' + ((c : ℂ) * Complex.I))) s g + ∑' ξ : K, (fun s' => φ (s' + ((c : ℂ) * Complex.I))) s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        (fun s' g' => Nn (s' + ((c : ℂ) * Complex.I)) g') s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) ((fun s' => φ (s' + ((c : ℂ) * Complex.I))) s) g) := by
  obtain ⟨hO, hOc, hax, hhalf, hEa, hNa, hEc, hNc, hEid, hNid⟩ := h
  have hre : ∀ s : ℂ, (s + ((c : ℂ) * Complex.I)).re = s.re := fun s => by simp
  have hmaps : Set.MapsTo (fun s : ℂ => s + ((c : ℂ) * Complex.I)) ((fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O) O :=
    fun s hs => hs
  refine ⟨hO.preimage (continuous_id.add continuous_const), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : (fun s : ℂ => s + ((c : ℂ) * Complex.I)) ⁻¹' O = (fun s : ℂ => s - ((c : ℂ) * Complex.I)) '' O := by
      ext s
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h; exact ⟨s + ((c : ℂ) * Complex.I), h, by ring⟩
      · rintro ⟨s', h', rfl⟩; simpa using h'
    rw [this]
    exact hOc.image _ (continuous_id.sub continuous_const).continuousOn
  · intro s hs; show s + ((c : ℂ) * Complex.I) ∈ O; exact hax (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre, hs])
  · intro s hs; show s + ((c : ℂ) * Complex.I) ∈ O; exact hhalf (by simp only [Set.mem_setOf_eq] at hs ⊢; rw [hre]; exact hs)
  · intro g; exact (hEa g).comp ((analyticOnNhd_id).add analyticOnNhd_const) hmaps
  · intro g; exact (hNa g).comp ((analyticOnNhd_id).add analyticOnNhd_const) hmaps
  · exact hEc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn)
      (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  · exact hNc.comp (((continuous_fst.add continuous_const).prodMk continuous_snd).continuousOn)
      (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  · intro s hs g; exact hEid (s + ((c : ℂ) * Complex.I)) (by rw [hre]; exact hs) g
  · intro s hs g; exact hNid (s + ((c : ℂ) * Complex.I)) (by rw [hre]; exact hs) g

theorem integral_mul_conj_symm {X : Type*} [MeasurableSpace X] (μ : Measure X) (a b : X → ℂ) :
    ∫ x, a x * conj (b x) ∂μ = conj (∫ x, b x * conj (a x) ∂μ) := by
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_conj, mul_comm]

theorem integrable_mul_conj_of_continuous {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [CompactSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f g : X → ℂ) (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => f x * conj (g x)) μ := by
  have hc : Continuous fun x => f x * conj (g x) := hf.mul (Complex.continuous_conj.comp hg)
  have := hc.continuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ (μ := μ)
  simpa using this

theorem main
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (Oψ : ιP → Set ℂ) (Eψ Nψ : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ : ∀ i : ιP,
      IsOpen (Oψ i) ∧ IsPreconnected (Oψ i) ∧ {s : ℂ | s.re = 0} ⊆ (Oψ i) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (Oψ i) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ i s g) (Oψ i)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ i s g) (Oψ i)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ i s g = ψf i s g + ∑' ξ : K, ψf i s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) g))
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hNψ : ∀ (i : ιP), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (_hNE : ∀ (e : ιE) (j : Fin (nE e)), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (i : ιP) (t : ℝ) (k' : Fin (nE (em i))),
    (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
        conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
    (∀ l : Fin (nE (em (rP i))),
      ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
          conj (φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) := by
  intro αm hαm ιE _iC μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan
    OE EE NE hEE f hf hfc hfact hbi harch
    ιP _iP μP νP hμP hνP hμPic hνPic hμPc hμνP rP hr hdistP φf ψf hφf hψf hφjc hψjc hφhol hψhol hψK hψsm hψKu hνPc hφdec hψdec
    Oψ Eψ Nψ hEψ em τ hem hNψ hNE i t k'
  classical
  have hαI : ∀ x, ((αm x : ℝˣ) : ℝ) = ideleNorm K x := fun _ => rfl
  have hcs : ∀ (F : ℂ → AdelicGL2 (𝓞 K) K → ℂ), Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => F p.1 p.2) → ∀ s, Continuous (F s) :=
    fun F hF s => hF.comp (continuous_const.prodMk continuous_id)

  have hcK : ∀ (u : AdelicGL2 (𝓞 K) K → ℂ), Continuous u → Continuous fun k : adelicMaximalCompact K => u (k : AdelicGL2 (𝓞 K) K) :=
    fun u hu => hu.comp continuous_subtype_val
  have hint : ∀ (u v : AdelicGL2 (𝓞 K) K → ℂ), Continuous u → Continuous v →
      Integrable (fun k : adelicMaximalCompact K => u (k : AdelicGL2 (𝓞 K) K) * conj (v (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
    fun u v hu hv => integrable_mul_conj_of_continuous (maximalCompactHaar K) _ _ (hcK u hu) (hcK v hv)
  have hpair : ∀ (Φ' : AdelicGL2 (𝓞 K) K → ℂ), Continuous Φ' → ∀ (m : ℕ) (W : Fin m → AdelicGL2 (𝓞 K) K → ℂ), (∀ l, Continuous (W l)) → ∀ (c : Fin m → ℂ),
      ∫ k, Φ' (k : AdelicGL2 (𝓞 K) K) * conj (∑ l, c l * W l (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∑ l, conj (c l) * ∫ k, Φ' (k : AdelicGL2 (𝓞 K) K) * conj (W l (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro Φ' hΦ' m W hW c
    have : (fun k : adelicMaximalCompact K => Φ' (k : AdelicGL2 (𝓞 K) K) * conj (∑ l, c l * W l (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => ∑ l, conj (c l) * (Φ' (k : AdelicGL2 (𝓞 K) K) * conj (W l (k : AdelicGL2 (𝓞 K) K))) := by
      funext k; rw [map_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by rw [map_mul]; ring
    rw [this, integral_finset_sum _ fun l _ => (hint _ _ hΦ' (hW l)).const_mul _]
    simp only [integral_const_mul]
  have hcoef : ∀ (m : ℕ) (W : Fin m → AdelicGL2 (𝓞 K) K → ℂ), (∀ l, Continuous (W l)) →
      (∀ l l', ∫ k, W l (k : AdelicGL2 (𝓞 K) K) * conj (W l' (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = if l = l' then 1 else 0) →
      ∀ (c : Fin m → ℂ) (l : Fin m),
      ∫ k, (∑ l', c l' * W l' (k : AdelicGL2 (𝓞 K) K)) * conj (W l (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = c l := by
    intro m W hW hon c l
    have : (fun k : adelicMaximalCompact K => (∑ l', c l' * W l' (k : AdelicGL2 (𝓞 K) K)) * conj (W l (k : AdelicGL2 (𝓞 K) K))) =
        fun k : adelicMaximalCompact K => ∑ l', c l' * (W l' (k : AdelicGL2 (𝓞 K) K) * conj (W l (k : AdelicGL2 (𝓞 K) K))) := by
      funext k; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, integral_finset_sum _ fun l' _ => (hint _ _ (hW l') (hW l)).const_mul (c l')]
    simp only [integral_const_mul, hon, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']; simp

  have hrr : rP (rP i) = i := by
    by_contra hne
    obtain ⟨x, -, hx⟩ := hdistP (rP (rP i)) i hne
    rw [(hr (rP i)).1, (hr (rP i)).2, (hr i).1, (hr i).2] at hx
    exact hx.elim (fun h => h rfl) (fun h => h rfl)

  obtain ⟨N', hN'0, hlevψ⟩ :=
    AutomorphicForm.exists_ne_bot_forall_apply_mul_eq_of_mem_principalLevel_of_isKfSmooth_of_differentiable K (ψf i) (hψsm i) (hψhol i)
  have hN0 : N ≠ ⊥ := ne_bot_of_forall_dvd_mem K hN
  have hM0 : N * N' ≠ ⊥ := mul_ne_zero hN0 hN'0
  have hMN : principalLevel (𝓞 K) K (N * N') ≤ principalLevel (𝓞 K) K N := principalLevel_mul_le K hN0 hN'0
  have hMN' : principalLevel (𝓞 K) K (N * N') ≤ principalLevel (𝓞 K) K N' := by
    rw [mul_comm]; exact principalLevel_mul_le K hN'0 hN0
  have hlevEM : ∀ (e : ιE) (j : Fin (nE e)) (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K (N * N') ⊓ finiteAdelicGL2Subgroup K,
      φE e j s (g * u) = φE e j s g := fun e j s g u hu => hφElev e j s g u ⟨hMN hu.1, hu.2⟩
  have hlevψM : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K (N * N') ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g :=
    fun s g u hu => hlevψ s g u ⟨hMN' hu.1, hu.2⟩

  have hP1 : ∀ s : ℂ, etaFst (μP i) αm hαm s = etaFst (μ (em i)) αm hαm (s + (((τ i : ℝ) : ℂ) * Complex.I)) ∧
      etaSnd (νP i) αm hαm s = etaSnd (ν (em i)) αm hαm (s + (((τ i : ℝ) : ℂ) * Complex.I)) := by
    intro s
    have h := AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift K αm hαm hαI
    refine ⟨?_, ?_⟩
    · rw [(hem i).1]; exact (h (μ (em i)) (τ i) s).1
    · rw [(hem i).2]; exact (h (ν (em i)) (τ i) s).2.2.2
  have hP2 : ∀ s : ℂ, etaFst (νP i) αm hαm s = etaFst (μ (em (rP i))) αm hαm (s + (((τ (rP i) : ℝ) : ℂ) * Complex.I)) ∧
      etaSnd (μP i) αm hαm s = etaSnd (ν (em (rP i))) αm hαm (s + (((τ (rP i) : ℝ) : ℂ) * Complex.I)) := by
    intro s
    have h := AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift K αm hαm hαI
    refine ⟨?_, ?_⟩
    · rw [← (hr i).1, (hem (rP i)).1]; exact (h (μ (em (rP i))) (τ (rP i)) s).1
    · rw [← (hr i).2, (hem (rP i)).2]; exact (h (ν (em (rP i))) (τ (rP i)) s).2.2.2

  have hFsec : ∀ s : ℂ, IsInducedSection (𝓞 K) K (etaFst (μP i) αm hαm s) (etaSnd (νP i) αm hαm s)
      ((fun s' => φE (em i) k' (s' + (((τ i : ℝ) : ℂ) * Complex.I))) s) := by
    intro s; rw [(hP1 s).1, (hP1 s).2]; exact hφE (em i) k' _
  have hGsec : ∀ (l : Fin (nE (em (rP i)))) (s : ℂ),
      IsInducedSection (𝓞 K) K (etaFst (νP i) αm hαm s) (etaSnd (μP i) αm hαm s)
      ((fun s' => φE (em (rP i)) l (s' + (((τ (rP i) : ℝ) : ℂ) * Complex.I))) s) := by
    intro l s; rw [(hP2 s).1, (hP2 s).2]; exact hφE (em (rP i)) l _
  have hShK : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ) (s : ℂ), IsArchKFinite K ((fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s) :=
    fun e j c s => hφEK e j _
  have hShsm : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ) (s : ℂ), IsKfSmooth K ((fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s) :=
    fun e j c s => hφEf e j _
  have hShjc : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ), Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => (fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) p.1 p.2) :=
    fun e j c => (hφEjc e j).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
  have hShhol : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ) (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => (fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s g) :=
    fun e j c g => (hφEhol e j g).comp (differentiable_id.add_const _)
  have hShKu : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        (fun k : ↥(archRowIsometrySubgroup K w) => (fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W :=
    fun e j c w => (hφEKu e j w).imp fun W hW => ⟨hW.1, fun s g => hW.2 _ g⟩
  have hShlevM : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ) (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K (N * N') ⊓ finiteAdelicGL2Subgroup K,
      (fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s (g * u) = (fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s g :=
    fun e j c s g u hu => hlevEM e j _ g u hu
  have hShlevN : ∀ (e : ιE) (j : Fin (nE e)) (c : ℝ) (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      (fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s (g * u) = (fun s' => φE e j (s' + ((c : ℂ) * Complex.I))) s g :=
    fun e j c s g u hu => hφElev e j _ g u hu
  have hdatG : ∀ l : Fin (nE (em (rP i))), _ := fun l => shifted_datum K (φE (em (rP i)) l) (OE (em (rP i)) l) (EE (em (rP i)) l) (NE (em (rP i)) l) (τ (rP i)) (hEE (em (rP i)) l)
  have hdatF := shifted_datum K (φE (em i) k') (OE (em i) k') (EE (em i) k') (NE (em i) k') (τ i) (hEE (em i) k')

  have hc1 : -((t : ℂ) * Complex.I) + (((τ (rP i) : ℝ) : ℂ) * Complex.I) = (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) := by push_cast; ring
  have hc2 : ((t : ℂ) * Complex.I) + (((τ i : ℝ) : ℂ) * Complex.I) = (((t + τ i : ℝ) : ℂ) * Complex.I) := by push_cast; ring

  have hA : ∀ l : Fin (nE (em (rP i))),
      ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro l
    have h := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
      K (N * N') hM0 hαm (μP i) (νP i) (hμP i) (hνP i) (hμPic i) (hνPic i) (hμPc i) (hνPc i)
      (ψf i) (hψf i) (hψK i) (hψsm i) (hψjc i) (hψhol i) (hψKu i) hlevψM
      (fun s' => φE (em (rP i)) l (s' + (((τ (rP i) : ℝ) : ℂ) * Complex.I))) (hGsec l) (hShK _ l _) (hShsm _ l _) (hShjc _ l _) (hShhol _ l _) (hShKu _ l _) (hShlevM _ l _)
      (Oψ i) (Eψ i) (Nψ i) (hEψ i)
      _ _ _ (hdatG l) t
    simp only [hc1] at h
    exact h

  have hB : ∀ l : Fin (nE (em (rP i))),
      ∫ k, φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro l
    have h := AutomorphicForm.integral_mul_conj_axis_continuation_weylIntertwiningIntegral_eq_of_swap_pair_of_principalLevel_of_ne_bot
      K N hN0 hαm (μP i) (νP i) (hμP i) (hνP i) (hμPic i) (hνPic i) (hμPc i) (hνPc i)
      (fun s' => φE (em i) k' (s' + (((τ i : ℝ) : ℂ) * Complex.I))) hFsec (hShK _ k' _) (hShsm _ k' _) (hShjc _ k' _) (hShhol _ k' _) (hShKu _ k' _) (hShlevN _ k' _)
      (fun s' => φE (em (rP i)) l (s' + (((τ (rP i) : ℝ) : ℂ) * Complex.I))) (hGsec l) (hShK _ l _) (hShsm _ l _) (hShjc _ l _) (hShhol _ l _) (hShKu _ l _) (hShlevN _ l _)
      _ _ _ hdatF _ _ _ (hdatG l) t
    simp only [hc1, hc2] at h
    exact h

  obtain ⟨hWon, hWprops⟩ :=
    AutomorphicForm.orthonormal_and_isInducedSection_inv_vol_mul_axis_continuation_weylIntertwiningIntegral_of_flat_orthonormal_family
      K N tysK hαm (μ (em (rP i))) (ν (em (rP i))) (hμ _) (hν _) (hμic _) (hνic _) (hμc _) (hνc _) (nE (em (rP i))) (φE (em (rP i)))
      (hφE _) (hφEK _) (hφEf _) (hφEjc _) (hφEhol _) (hφEKu _) (hφEflat _) (hφElev _) (hφEty _) (hφEon _)
      (OE _) (EE _) (NE _) (hEE _) (-t + τ (rP i))
  simp only [] at hWon
  have hWc : ∀ l : Fin (nE (em (rP i))), Continuous (fun g : AdelicGL2 (𝓞 K) K => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) g) :=
    fun l => (hWprops l).2.1
  have hφon' : ∀ l l' : Fin (nE (em (rP i))),
      ∫ k, φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em (rP i)) l' (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) = if l = l' then 1 else 0 := by
    intro l l'
    rw [← hφEon (em (rP i)) l l']
    exact integral_congr_ae (Filter.Eventually.of_forall fun k => by
      show φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em (rP i)) l' (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) = _
      rw [hφEflat (em (rP i)) l _ k, hφEflat (em (rP i)) l' _ k])

  obtain ⟨-, hNψc, -, -⟩ :=
    AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
      K hαm (μP i) (νP i) (hμP i) (hνP i) (hμPic i) (hνPic i) (hμPc i) (hνPc i) N' (ψf i)
      (hψf i) (hψK i) (hψsm i) (hψjc i) (hψhol i) (hψKu i) hlevψ (Oψ i) (Eψ i) (Nψ i) (hEψ i) t

  have hC3 := AutomorphicForm.exists_forall_inv_vol_mul_axis_continuation_weylIntertwining_eq_sum_and_exists_forall_eq_sum_of_paleyWiener_matched_swap
    K α β hα hαβ SK ξK hξc hξt N hN tysK hξu hαm ιE μ ν hμ hν hμic hνic hμc hνc hμν hdist nE φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty hφEon hφEspan OE EE NE hEE f hf hfc hfact hbi harch ιP μP νP hμP hνP hμPic hνPic hμPc hμνP rP hr hdistP φf ψf hφf hψf hφjc hψjc hφhol hψhol hψK hψsm hψKu hνPc hφdec hψdec Oψ Eψ Nψ hEψ em τ hem hNψ hNE
  obtain ⟨hC3a, -⟩ := hC3 i t
  obtain ⟨-, hC3b⟩ := hC3 (rP i) (-t)
  rw [hrr] at hC3b
  simp only [neg_neg] at hC3b
  obtain ⟨c, hc⟩ := hC3b k'
  obtain ⟨d, hd⟩ := hC3a k'

  have hcd : ∀ l, c l = d l := by
    intro l
    have h1 : c l = ∫ k, φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      rw [← hcoef _ (fun l g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) g) hWc hWon c l]
      exact integral_congr_ae (Filter.Eventually.of_forall fun k => by beta_reduce; rw [hc k])
    have h2 : d l = ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
      rw [← hcoef _ (fun l g => φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) g) (fun l => hcs _ (hφEjc _ l) _) hφon' d l]
      exact integral_congr_ae (Filter.Eventually.of_forall fun k => by beta_reduce; rw [hd k])
    rw [h1, h2, hB l]
  refine ⟨?_, hA⟩

  have eL : ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (∑ l, c l * (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K))) ∂(maximalCompactHaar K) :=
    integral_congr_ae (Filter.Eventually.of_forall fun k => by beta_reduce; rw [hc k])
  have eR : ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (∑ l, d l * φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
    integral_congr_ae (Filter.Eventually.of_forall fun k => by beta_reduce; rw [hd k])
  rw [eL, eR, hpair (ψf i ((t : ℂ) * Complex.I)) (hcs _ (hψjc i) _) _ (fun l g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) g) hWc c,
    hpair (fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ i ((t : ℂ) * Complex.I) g) hNψc _ (fun l g => φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) g) (fun l => hcs _ (hφEjc _ l) _) d]
  refine Finset.sum_congr rfl fun l _ => ?_
  beta_reduce
  rw [hcd l, hA l]

end Ws31.C4

end

open AutomorphicForm in

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ), μ e z * ν e z = ξK ⟨z, Subgroup.mem_top z⟩)
      (_hdist : ∀ e e' : ιE, e ≠ e' → ∃ z ∈ NumberField.TateGlobal.normOneIdeles K,
        μ e z ≠ μ e' z ∨ ν e z ≠ ν e' z)
      (nE : ιE → ℕ)
      (φE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ e j s, IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm s) (etaSnd (ν e) αm hαm s) (φE e j s))
      (_hφEK : ∀ e j s, IsArchKFinite K (φE e j s))
      (_hφEf : ∀ e j s, IsKfSmooth K (φE e j s))
      (_hφEjc : ∀ e j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE e j p.1 p.2))
      (_hφEhol : ∀ e j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE e j s g))
      (_hφEKu : ∀ e j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE e j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ e j (s : ℂ) (k : adelicMaximalCompact K),
        φE e j s (k : AdelicGL2 (𝓞 K) K) = φE e j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ e j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE e j s (g * u) = φE e j s g)
      (_hφEty : ∀ e j (s : ℂ), φE e j s ∈ archCutSubmodule K tysK)
      (_hφEon : ∀ e i j, ∫ k, φE e i 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        if i = j then 1 else 0)
      (_hφEspan : ∀ (e : ιE) (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst (μ e) αm hαm ((t : ℂ) * Complex.I)) (etaSnd (ν e) αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK →
        φ₀ ∈ Submodule.span ℂ (Set.range fun j : Fin (nE e) => φE e j ((t : ℂ) * Complex.I)))
      (OE : ∀ e : ιE, Fin (nE e) → Set ℂ) (EE NE : ∀ e : ιE, Fin (nE e) → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEE : ∀ (e : ιE) (j : Fin (nE e)),
      IsOpen (OE e j) ∧ IsPreconnected (OE e j) ∧ {s : ℂ | s.re = 0} ⊆ (OE e j) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (OE e j) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => EE e j s g) (OE e j)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => NE e j s g) (OE e j)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => EE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => NE e j p.1 p.2) ((OE e j) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        EE e j s g = φE e j s g + ∑' ξ : K, φE e j s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        NE e j s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (φE e j s) g))
      (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f),
      IsFactorizableTestFn K f →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f →
      IsArchBiFinite K tysK f →
    ∀
      (ιP : Type) [Fintype ιP]
      (μP νP : ιP → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μP e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (νP e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μP e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (νP e))
      (_hμc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP e x : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιP)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP e (z : (AdeleRing (𝓞 K) K)ˣ) * νP e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP : ιP → ιP) (_hr : ∀ e, μP (rP e) = νP e ∧ νP (rP e) = μP e)
      (_hdist : ∀ e e' : ιP, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP e x ≠ μP e' x ∨ νP e x ≠ νP e' x)
      (φf ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (φf e s))
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hφjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φf e p.1 p.2))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hφhol : ∀ e g, Differentiable ℂ (fun s => φf e s g))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hφdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (Oψ : ιP → Set ℂ) (Eψ Nψ : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ : ∀ i : ιP,
      IsOpen (Oψ i) ∧ IsPreconnected (Oψ i) ∧ {s : ℂ | s.re = 0} ⊆ (Oψ i) ∧ {s : ℂ | 1 / 2 < s.re} ⊆ (Oψ i) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ i s g) (Oψ i)) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ i s g) (Oψ i)) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ i p.1 p.2) ((Oψ i) ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ i s g = ψf i s g + ∑' ξ : K, ψf i s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ i s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf i s) g))
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hNψ : ∀ (i : ιP), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (_hNE : ∀ (e : ιE) (j : Fin (nE e)), ∃ (A : ℝ) (n : ℕ), ∀ (t : ℝ) (k : adelicMaximalCompact K),
        ‖NE e j ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ ≤ A * (1 + |t|) ^ n)
      (i : ιP) (t : ℝ) (k' : Fin (nE (em i))),
    (∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
      ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
        conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em i) k' (((t + τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) ∧
    (∀ l : Fin (nE (em (rP i))),
      ∫ k, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
          conj ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * NE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) =
        ∫ k, ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ * Nψ i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) *
          conj (φE (em (rP i)) l (((-t + τ (rP i) : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) :=
  Ws31.C4.main K α β hα hαβ SK ξK hξc hξt N hN tysK hξu

end S_AutomorphicForm_integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched
end P2MW
export P2MW.S_AutomorphicForm_integral_mul_conj_eq_integral_axis_continuation_weylIntertwining_mul_conj_axis_continuation_weylIntertwining_of_paleyWiener_matched (solution)
