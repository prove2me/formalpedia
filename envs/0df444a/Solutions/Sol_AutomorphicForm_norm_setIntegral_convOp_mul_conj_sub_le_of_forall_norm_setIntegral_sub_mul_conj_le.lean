-- Prove2me | solution 1 for AutomorphicForm.norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/8484c007-d6b8-5a18-b871-bc62afd240a9

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
import Theorems.Thm_AutomorphicForm_isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain
import Theorems.Thm_AutomorphicForm_isKfSmooth_convOp_and_apply_mul_eq_of_isBiInvariantUnder_principalLevel_of_ne_bot
import Theorems.Thm_AutomorphicForm_convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
import Theorems.Thm_AutomorphicForm_star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous
import Theorems.Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar
import Theorems.Thm_MeasureTheory_Measure_isInvInvariant_of_isMulRightInvariant
import Theorems.Thm_AutomorphicForm_eLpNorm_convOp_le_ofReal_integral_norm_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology_generalLinearGroup_finTwo
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.CuspidalConstituent.rightRegular_apply AutomorphicForm.ArchDirComplex.iH.sizeOf_spec"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm
open scoped ENNReal

noncomputable section

namespace LhsStab

variable (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]

abbrev pins (α β : ℝ) : CarrierPins K :=
  productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
    (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

variable {K}

theorem memLp_of_aut {α β : ℝ} {ξ : (pins K α β).Z →* ℂˣ} {u : AdelicGL2 (𝓞 K) K → ℂ}
    (hu : IsAutomorphicFnAt K (pins K α β) ξ u) :
    MemLp u 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) :=
  ((lsXiMemberAt_iff (𝓞 K) K (pins K α β).μ (pins K α β).Z ξ (pins K α β).D u).mp hu).2

theorem aut_smul {α β : ℝ} {ξ : (pins K α β).Z →* ℂˣ} {u : AdelicGL2 (𝓞 K) K → ℂ}
    (hu : IsAutomorphicFnAt K (pins K α β) ξ u) (c : ℂ) :
    IsAutomorphicFnAt K (pins K α β) ξ (fun g => c * u g) := by
  have h := (lsXiMemberAt_iff (𝓞 K) K (pins K α β).μ (pins K α β).Z ξ (pins K α β).D u).mp hu
  refine (lsXiMemberAt_iff (𝓞 K) K (pins K α β).μ (pins K α β).Z ξ (pins K α β).D _).mpr ⟨⟨?_, ?_⟩, h.2.const_mul c⟩
  · intro γ g; rw [h.1.left_invariant]
  · intro z g; rw [h.1.central_transform]; ring

section L2

variable {X : Type*} [MeasurableSpace X] (ν : Measure X)

theorem integral_mul_conj_eq_inner {a b : X → ℂ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    ∫ x, a x * conj (b x) ∂ν = inner ℂ (hb.toLp b) (ha.toLp a) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
  rw [hxa, hxb, RCLike.inner_apply, mul_comm]

theorem norm_integral_mul_conj_le {a b : X → ℂ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    ‖∫ x, a x * conj (b x) ∂ν‖ ≤ (eLpNorm a 2 ν).toReal * (eLpNorm b 2 ν).toReal := by
  rw [integral_mul_conj_eq_inner ν ha hb, mul_comm]
  refine (norm_inner_le_norm _ _).trans ?_
  rw [Lp.norm_toLp, Lp.norm_toLp]

theorem integrable_mul_conj {a b : X → ℂ} (ha : MemLp a 2 ν) (hb : MemLp b 2 ν) :
    Integrable (fun x => a x * conj (b x)) ν := by
  have h := L2.integrable_inner (𝕜 := ℂ) (hb.toLp b) (ha.toLp a)
  refine h.congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hxa hxb
  rw [hxa, hxb, RCLike.inner_apply, mul_comm]

theorem integral_mul_conj_swap (a b : X → ℂ) :
    ∫ x, a x * conj (b x) ∂ν = conj (∫ x, b x * conj (a x) ∂ν) := by
  rw [← integral_conj]
  congr 1; funext x
  rw [map_mul, Complex.conj_conj, mul_comm]

theorem integral_mul_conj_eq_zero_of_eLpNorm_eq_zero {a b : X → ℂ} (hb : MemLp b 2 ν)
    (h0 : eLpNorm b 2 ν = 0) : ∫ x, a x * conj (b x) ∂ν = 0 := by
  have hb0 : b =ᵐ[ν] 0 := (eLpNorm_eq_zero_iff hb.aestronglyMeasurable two_ne_zero).mp h0
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hb0] with x hx
  rw [hx, Pi.zero_apply, map_zero, mul_zero]

end L2

end LhsStab

end

open LhsStab in
theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (_hf : Continuous f) (_hfc : HasCompactSupport f)
    (_hff : IsFactorizableTestFn K f)
    (_hfb : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) f)
    (_hft : IsArchBiFinite K tysK f)
    (ε : ℝ) (_hε : 0 < ε)
    (u₁ u₂ v₁ v₂ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hu₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u₁) (_hu₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK u₂)
    (_hv₁ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v₁) (_hv₂ : IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v₂) :
    letI := adeleBorel (𝓞 K) K
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v₁ (g * u') = v₁ g) →
      v₁ ∈ archCutSubmodule K tysK →
    (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v₂ (g * u') = v₂ g) →
      v₂ ∈ archCutSubmodule K tysK →
    (∀ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g) →
        v ∈ archCutSubmodule K tysK →
        eLpNorm v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ 1 →
        ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (u₁ g - v₁ g) * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ ε) →
    (∀ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK v →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g) →
        v ∈ archCutSubmodule K tysK →
        eLpNorm v 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)) ≤ 1 →
        ‖∫ g in AutomorphicForm.canonicalTruncationDomain K α β, (u₂ g - v₂ g) * conj (v g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)‖ ≤ ε) →
    ‖(∫ g in AutomorphicForm.canonicalTruncationDomain K α β, convOp K f u₂ g * conj (u₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) -
        (∫ g in AutomorphicForm.canonicalTruncationDomain K α β, convOp K f v₂ g * conj (v₁ g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K))‖ ≤
      (∫ g, ‖f g‖ ∂(adelicGLHaar (Fin 2) (𝓞 K) K)) * ε *
        ((eLpNorm u₁ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))).toReal + (eLpNorm u₂ 2 ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β))).toReal + ε) := by
  classical

  set Φ := AutomorphicForm.canonicalTruncationDomain K α β with hΦdef
  set μ : Measure (AdelicGL2 (𝓞 K) K) := adelicGLHaar (Fin 2) (𝓞 K) K with hμ
  intro hv₁L hv₁T hv₂L hv₂T h₁ h₂
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar K
  haveI : SecondCountableTopology (AdelicGL2 (𝓞 K) K) :=
    NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo K
  haveI : (adelicGLHaar (Fin 2) (𝓞 K) K).IsInvInvariant :=
    MeasureTheory.Measure.isInvInvariant_of_isMulRightInvariant (adelicGLHaar (Fin 2) (𝓞 K) K)

  have hNbot : N ≠ ⊥ := by
    intro hN0
    have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ SK := fun v =>
      hN v (by rw [hN0]; exact ⟨⊥, by simp⟩)
    have hker : RingHom.ker (algebraMap ℤ (𝓞 K)) ≤ ⊥ :=
      ((RingHom.injective_iff_ker_eq_bot _).mp (RingHom.injective_int _)).le
    have key : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K),
        v.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
      intro p
      have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp p.2
      have hp0 : (p : ℤ) ≠ 0 := hp.ne_zero
      haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
        ((Ideal.span_singleton_prime hp0).mpr hp).isMaximal (by simpa [Ideal.span_singleton_eq_bot] using hp0)
      obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K)
        (Ideal.span {(p : ℤ)}) (le_trans hker bot_le)
      have hQbot : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQmax (RingOfIntegers.not_isField K)
      exact ⟨⟨Q, hQmax.isPrime, hQbot⟩, hQ⟩
    choose vp hvp using key
    have hinj : Function.Injective vp := by
      intro p q hpq
      have h := hvp p
      rw [hpq, hvp q] at h
      have h' : Associated (q : ℤ) (p : ℤ) := Ideal.span_singleton_eq_span_singleton.mp h
      have hn : (q : ℤ).natAbs = (p : ℤ).natAbs := Int.natAbs_eq_iff_associated.mpr h'
      exact Subtype.ext (by simpa using hn.symm)
    haveI : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOf_prime
    haveI : Infinite (HeightOneSpectrum (𝓞 K)) := Infinite.of_injective vp hinj
    have hfin : Finite (HeightOneSpectrum (𝓞 K)) :=
      Finite.of_injective (fun v => (⟨v, hall v⟩ : {v // v ∈ SK}))
        (fun a b h => congrArg Subtype.val h)
    exact not_finite (HeightOneSpectrum (𝓞 K))

  set fs : AdelicGL2 (𝓞 K) K → ℂ := fun x => conj (f x⁻¹) with hfs
  have hfs_c : Continuous fs := Complex.continuous_conj.comp (_hf.comp continuous_inv)
  have hfs_cs : HasCompactSupport fs :=
    ((_hfc.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 K) K))).comp_left (map_zero _))
  have hfs_bi : IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) fs := by
    intro u' hu' g
    have h := _hfb u'⁻¹ (inv_mem hu') g⁻¹
    refine ⟨?_, ?_⟩
    · show conj (f (u' * g)⁻¹) = conj (f g⁻¹)
      rw [mul_inv_rev, h.2]
    · show conj (f (g * u')⁻¹) = conj (f g⁻¹)
      rw [mul_inv_rev, h.1]
  have hfs_arch : IsArchBiFinite K tysK fs := by
    have h1 := (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous K tysK f _hf).1 _hft.2
    have h2 := (AutomorphicForm.star_mem_archCutSubmodule_and_star_mem_archDualCutSubmodule_of_continuous K tysK
      (fun x => f x⁻¹) (_hf.comp continuous_inv)).2 _hft.1
    refine ⟨?_, h2⟩
    have : (fun x : AdelicGL2 (𝓞 K) K => fs x⁻¹) = fun x => conj (f x) := by
      funext x; simp only [hfs, inv_inv]
    rw [this]; exact h1

  have hfs_norm : ∫ x, ‖fs x‖ ∂μ = ∫ x, ‖f x‖ ∂μ := by
    have : (fun x => ‖fs x‖) = fun x => (fun y => ‖f y‖) x⁻¹ := by
      funext x; simp only [hfs, RCLike.norm_conj]
    rw [this, integral_inv_eq_self (fun y => ‖f y‖) μ]
  have hf1 : 0 ≤ ∫ x, ‖f x‖ ∂μ := integral_nonneg fun _ => norm_nonneg _

  have aut_R : ∀ (F : AdelicGL2 (𝓞 K) K → ℂ), Continuous F → HasCompactSupport F →
      IsBiInvariantUnder K (principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) F → IsArchBiFinite K tysK F →
      ∀ w : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (pins K α β) ξK w →
      IsAutomorphicFnAt K (pins K α β) ξK (convOp K F w) ∧
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, convOp K F w (g * u') = convOp K F w g) ∧
      convOp K F w ∈ archCutSubmodule K tysK := by
    intro F hF hFc hFb hFt w hw
    exact ⟨AutomorphicForm.isAutomorphicFnAt_convOp_of_isAutomorphicFnAt_canonicalTruncationDomain K α β hα hαβ ξK hξc hξu w hw F hF hFc,
      (AutomorphicForm.isKfSmooth_convOp_and_apply_mul_eq_of_isBiInvariantUnder_principalLevel_of_ne_bot K N hNbot F hFb w).2,
      AutomorphicForm.convOp_mem_archCutSubmodule_of_isArchBiFinite_of_isAutomorphicFnAt K α β hα hαβ ξK hξc w hw F hF hFc tysK hFt⟩
  obtain ⟨hRv₂, hRv₂L, hRv₂T⟩ := aut_R f _hf _hfc _hfb _hft v₂ _hv₂
  obtain ⟨hRu₁, hRu₁L, hRu₁T⟩ := aut_R fs hfs_c hfs_cs hfs_bi hfs_arch u₁ _hu₁

  set n : (AdelicGL2 (𝓞 K) K → ℂ) → ℝ := fun w => (eLpNorm w 2 (μ.restrict Φ)).toReal with hn
  have n_nonneg : ∀ w, 0 ≤ n w := fun w => ENNReal.toReal_nonneg

  have weak : ∀ (d w : AdelicGL2 (𝓞 K) K → ℂ),
      (∀ v : AdelicGL2 (𝓞 K) K → ℂ, IsAutomorphicFnAt K (pins K α β) ξK v →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, v (g * u') = v g) →
        v ∈ archCutSubmodule K tysK → eLpNorm v 2 (μ.restrict Φ) ≤ 1 →
        ‖∫ g in Φ, d g * conj (v g) ∂μ‖ ≤ ε) →
      IsAutomorphicFnAt K (pins K α β) ξK w →
      (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, w (g * u') = w g) →
      w ∈ archCutSubmodule K tysK →
      ‖∫ g in Φ, d g * conj (w g) ∂μ‖ ≤ ε * n w := by
    intro d w h hw hwL hwT
    have hwM : MemLp w 2 (μ.restrict Φ) := memLp_of_aut hw
    have hne : eLpNorm w 2 (μ.restrict Φ) ≠ ⊤ := hwM.eLpNorm_ne_top
    by_cases hz : n w = 0
    · have h0 : eLpNorm w 2 (μ.restrict Φ) = 0 := by
        have := (ENNReal.toReal_eq_zero_iff _).mp hz
        exact this.resolve_right hne
      rw [integral_mul_conj_eq_zero_of_eLpNorm_eq_zero (μ.restrict Φ) hwM h0, norm_zero, hz, mul_zero]
    have hpos : 0 < n w := lt_of_le_of_ne (n_nonneg w) (Ne.symm hz)
    set c : ℝ := (n w)⁻¹ with hc
    have hcpos : 0 < c := inv_pos.mpr hpos

    have hv : IsAutomorphicFnAt K (pins K α β) ξK (fun g => (c : ℂ) * w g) := aut_smul hw c
    have hvL : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u' ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
        (fun g => (c : ℂ) * w g) (g * u') = (fun g => (c : ℂ) * w g) g := fun g u' hu' => by
      simp only [hwL g u' hu']
    have hvT : (fun g => (c : ℂ) * w g) ∈ archCutSubmodule K tysK := by
      have : (fun g => (c : ℂ) * w g) = (c : ℂ) • w := rfl
      rw [this]; exact Submodule.smul_mem _ _ hwT
    have hvN : eLpNorm (fun g => (c : ℂ) * w g) 2 (μ.restrict Φ) ≤ 1 := by
      rw [show (fun g => (c : ℂ) * w g) = (c : ℂ) • w from rfl, eLpNorm_const_smul, ← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos,
        ← ENNReal.ofReal_toReal hne, ← ENNReal.ofReal_mul (le_of_lt hcpos)]
      have : c * n w = 1 := inv_mul_cancel₀ hz
      rw [show (eLpNorm w 2 (μ.restrict Φ)).toReal = n w from rfl, this, ENNReal.ofReal_one]
    have hb := h _ hv hvL hvT hvN
    have hscal : ∫ g in Φ, d g * conj ((fun g => (c : ℂ) * w g) g) ∂μ = (c : ℂ) * ∫ g in Φ, d g * conj (w g) ∂μ := by
      rw [← integral_const_mul]
      congr 1; funext g
      simp only [map_mul, Complex.conj_ofReal]; ring
    rw [hscal, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos] at hb
    calc ‖∫ g in Φ, d g * conj (w g) ∂μ‖ = n w * (c * ‖∫ g in Φ, d g * conj (w g) ∂μ‖) := by
          rw [← mul_assoc, show n w * c = 1 from mul_inv_cancel₀ hz, one_mul]
      _ ≤ n w * ε := mul_le_mul_of_nonneg_left hb (n_nonneg w)
      _ = ε * n w := mul_comm _ _

  have mu₁ := memLp_of_aut _hu₁
  have mu₂ := memLp_of_aut _hu₂
  have mv₁ := memLp_of_aut _hv₁
  have mv₂ := memLp_of_aut _hv₂
  have mRv₂ := memLp_of_aut hRv₂
  have mRu₁ := memLp_of_aut hRu₁

  have opb : ∀ (F : AdelicGL2 (𝓞 K) K → ℂ) (hF : Continuous F) (hFc : HasCompactSupport F) (w : AdelicGL2 (𝓞 K) K → ℂ),
      IsAutomorphicFnAt K (pins K α β) ξK w → n (convOp K F w) ≤ (∫ x, ‖F x‖ ∂μ) * n w := by
    intro F hF hFc w hw
    have h := AutomorphicForm.eLpNorm_convOp_le_ofReal_integral_norm_mul_eLpNorm_restrict_canonicalTruncationDomain_of_isAutomorphicFnAt
      K α β hα hαβ ξK hξc hξu F hF hFc w hw
    have hne : eLpNorm w 2 (μ.restrict Φ) ≠ ⊤ := (memLp_of_aut hw).eLpNorm_ne_top
    have hF1 : 0 ≤ ∫ x, ‖F x‖ ∂μ := integral_nonneg fun _ => norm_nonneg _
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hne) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hF1] at this
  have bRv₂ : n (convOp K f v₂) ≤ (∫ x, ‖f x‖ ∂μ) * n v₂ := opb f _hf _hfc v₂ _hv₂
  have bRu₁ : n (convOp K fs u₁) ≤ (∫ x, ‖f x‖ ∂μ) * n u₁ := by
    have := opb fs hfs_c hfs_cs u₁ _hu₁; rwa [hfs_norm] at this

  have bv₂ : n v₂ ≤ n u₂ + ε := by
    by_cases hz : n v₂ = 0
    · rw [hz]; linarith [n_nonneg u₂]
    have hpos : 0 < n v₂ := lt_of_le_of_ne (n_nonneg v₂) (Ne.symm hz)
    have hw := weak (fun g => u₂ g - v₂ g) v₂ h₂ _hv₂ hv₂L hv₂T

    have hsplit : ∫ g in Φ, (u₂ g - v₂ g) * conj (v₂ g) ∂μ
        = (∫ g in Φ, u₂ g * conj (v₂ g) ∂μ) - ∫ g in Φ, v₂ g * conj (v₂ g) ∂μ := by
      rw [← integral_sub (integrable_mul_conj _ mu₂ mv₂) (integrable_mul_conj _ mv₂ mv₂)]
      congr 1; funext g; ring
    have hself : ∫ g in Φ, v₂ g * conj (v₂ g) ∂μ = ((n v₂) ^ 2 : ℝ) := by
      rw [integral_mul_conj_eq_inner _ mv₂ mv₂, inner_self_eq_norm_sq_to_K, Lp.norm_toLp]
      push_cast; rfl
    have hcs : ‖∫ g in Φ, u₂ g * conj (v₂ g) ∂μ‖ ≤ n u₂ * n v₂ := norm_integral_mul_conj_le _ mu₂ mv₂
    have key : (n v₂) ^ 2 ≤ n u₂ * n v₂ + ε * n v₂ := by
      have e1 : ((n v₂) ^ 2 : ℝ) = ‖(((n v₂) ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      rw [e1, ← hself, show (∫ g in Φ, v₂ g * conj (v₂ g) ∂μ) = (∫ g in Φ, u₂ g * conj (v₂ g) ∂μ) -
        ∫ g in Φ, (u₂ g - v₂ g) * conj (v₂ g) ∂μ by rw [hsplit]; ring]
      exact (norm_sub_le _ _).trans (add_le_add hcs hw)
    nlinarith

  have adjA := AutomorphicForm.setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
    K α β hα hαβ ξK hξc hξu u₁ u₂ _hu₁ _hu₂ f _hf _hfc
  have adjC := AutomorphicForm.setIntegral_mul_conj_convOp_eq_setIntegral_convOp_conj_inv_mul_conj_of_isAutomorphicFnAt
    K α β hα hαβ ξK hξc hξu u₁ v₂ _hu₁ _hv₂ f _hf _hfc

  set A := ∫ g in Φ, convOp K f u₂ g * conj (u₁ g) ∂μ with hA
  set B := ∫ g in Φ, convOp K f v₂ g * conj (v₁ g) ∂μ with hB
  set C := ∫ g in Φ, convOp K f v₂ g * conj (u₁ g) ∂μ with hC

  have hAC : ‖A - C‖ ≤ (∫ x, ‖f x‖ ∂μ) * ε * n u₁ := by
    have eA : A = conj (∫ g in Φ, convOp K fs u₁ g * conj (u₂ g) ∂μ) := by
      rw [hA, integral_mul_conj_swap]; exact congrArg _ adjA
    have eC : C = conj (∫ g in Φ, convOp K fs u₁ g * conj (v₂ g) ∂μ) := by
      rw [hC, integral_mul_conj_swap]; exact congrArg _ adjC
    have e : A - C = conj (∫ g in Φ, convOp K fs u₁ g * conj (u₂ g - v₂ g) ∂μ) := by
      rw [eA, eC, ← map_sub, ← integral_sub (integrable_mul_conj _ mRu₁ mu₂) (integrable_mul_conj _ mRu₁ mv₂)]
      congr 2; funext g; rw [map_sub]; ring
    rw [e, RCLike.norm_conj, integral_mul_conj_swap, RCLike.norm_conj]
    have hw := weak (fun g => u₂ g - v₂ g) (convOp K fs u₁) h₂ hRu₁ hRu₁L hRu₁T
    calc ‖∫ g in Φ, (u₂ g - v₂ g) * conj (convOp K fs u₁ g) ∂μ‖ ≤ ε * n (convOp K fs u₁) := hw
      _ ≤ ε * ((∫ x, ‖f x‖ ∂μ) * n u₁) := mul_le_mul_of_nonneg_left bRu₁ (le_of_lt _hε)
      _ = (∫ x, ‖f x‖ ∂μ) * ε * n u₁ := by ring

  have hCB : ‖C - B‖ ≤ (∫ x, ‖f x‖ ∂μ) * ε * (n u₂ + ε) := by
    have e : C - B = conj (∫ g in Φ, (u₁ g - v₁ g) * conj (convOp K f v₂ g) ∂μ) := by
      rw [hC, hB, ← integral_sub (integrable_mul_conj _ mRv₂ mu₁) (integrable_mul_conj _ mRv₂ mv₁), ← integral_mul_conj_swap]
      congr 1; funext g; rw [map_sub]; ring
    rw [e, RCLike.norm_conj]
    have hw := weak (fun g => u₁ g - v₁ g) (convOp K f v₂) h₁ hRv₂ hRv₂L hRv₂T
    calc ‖∫ g in Φ, (u₁ g - v₁ g) * conj (convOp K f v₂ g) ∂μ‖ ≤ ε * n (convOp K f v₂) := hw
      _ ≤ ε * ((∫ x, ‖f x‖ ∂μ) * n v₂) := mul_le_mul_of_nonneg_left bRv₂ (le_of_lt _hε)
      _ ≤ ε * ((∫ x, ‖f x‖ ∂μ) * (n u₂ + ε)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left bv₂ hf1) (le_of_lt _hε)
      _ = (∫ x, ‖f x‖ ∂μ) * ε * (n u₂ + ε) := by ring

  calc ‖A - B‖ = ‖(A - C) + (C - B)‖ := by congr 1; ring
    _ ≤ ‖A - C‖ + ‖C - B‖ := norm_add_le _ _
    _ ≤ (∫ x, ‖f x‖ ∂μ) * ε * n u₁ + (∫ x, ‖f x‖ ∂μ) * ε * (n u₂ + ε) := add_le_add hAC hCB
    _ = (∫ x, ‖f x‖ ∂μ) * ε * (n u₁ + n u₂ + ε) := by ring

end S_AutomorphicForm_norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le
end P2MW
export P2MW.S_AutomorphicForm_norm_setIntegral_convOp_mul_conj_sub_le_of_forall_norm_setIntegral_sub_mul_conj_le (solution)
