-- Prove2me | solution 1 for AutomorphicForm.exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/779174a2-caff-530a-9ee2-bacd5d662eec

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_AutomorphicForm_CanonicalTruncationDomain
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
import Theorems.Thm_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
import Theorems.Thm_AutomorphicForm_integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
import Theorems.Thm_MeasureTheory_sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
import Theorems.Thm_AutomorphicForm_axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing"
p2m_attr_erase "simp" "UnramifiedWhittaker.ProductMeasureData.mk.injEq UnramifiedWhittaker.ProductMeasureData.mk.sizeOf_spec AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply"
p2m_attr_erase "simp" "RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply AutomorphicForm.WeylIntegrable.coe_intLattice AutomorphicForm.WeylIntegrable.coe_yUnit AutomorphicForm.WeylIntegrable.finOfIntegral_apply EisensteinGeneral.Piece.FactorizationDatum.mk.sizeOf_spec EisensteinGeneral.Piece.FactorizationDatum.mk.injEq AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply LanglandsTunnell.ArchPlace.complexTestFun_zero_apply LanglandsTunnell.ArchPlace.norm_anglePhase LanglandsTunnell.ArchPlace.realTestFun_zero_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open AutomorphicForm

noncomputable section

namespace KSUP

theorem infinite_heightOneSpectrum (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  classical

  have hex : ∀ p : Nat.Primes, ∃ Q : Ideal (𝓞 K), Q.IsMaximal ∧
      Q.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {(p : ℤ)} := by
    intro p
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime (by exact_mod_cast p.2.ne_zero)).mpr (Nat.prime_iff_prime_int.mp p.2)).isMaximal
        (by rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast p.2.ne_zero)
    exact Ideal.exists_ideal_over_maximal_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
  choose Q hQmax hQcomap using hex
  have hQne : ∀ p : Nat.Primes, Q p ≠ ⊥ := by
    intro p h
    have h2 := hQcomap p
    rw [h, Ideal.comap_bot_of_injective _ (algebraMap ℤ (𝓞 K)).injective_int] at h2
    have : ((p : ℕ) : ℤ) ∈ (⊥ : Ideal ℤ) := by rw [h2]; exact Ideal.subset_span (Set.mem_singleton _)
    rw [Ideal.mem_bot] at this
    exact_mod_cast (p.2.ne_zero : (p : ℕ) ≠ 0) |> fun h0 => h0 (by exact_mod_cast this)
  refine Infinite.of_injective (fun p : Nat.Primes => (⟨Q p, (hQmax p).isPrime, hQne p⟩ : HeightOneSpectrum (𝓞 K))) ?_
  intro p q hpq
  have h1 : Q p = Q q := by
    have := congrArg (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal) hpq
    exact this
  have h2 : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hQcomap p, ← hQcomap q, h1]
  rw [Ideal.span_singleton_eq_span_singleton] at h2
  have h3 : ((p : ℕ) : ℤ).natAbs = ((q : ℕ) : ℤ).natAbs := Int.natAbs_eq_iff_associated.mpr h2
  simp only [Int.natAbs_natCast] at h3
  exact Subtype.ext h3

theorem ne_bot_of_forall_dvd_mem {K : Type} [Field K] [NumberField K] (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK) : N ≠ ⊥ := by
  intro h
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ SK := fun v => hN v (by rw [h]; exact dvd_zero _)
  have hfin : (Set.univ : Set (HeightOneSpectrum (𝓞 K))).Finite := (SK.finite_toSet).subset fun v _ => hall v
  haveI := infinite_heightOneSpectrum K
  exact Set.infinite_univ (α := HeightOneSpectrum (𝓞 K)) hfin

theorem sq_le_of_mem {K : Type} [Field K] [NumberField K] {D : ℕ}
    (V : Submodule ℂ (adelicMaximalCompact K → ℂ)) (hVfd : FiniteDimensional ℂ V) (hVD : Module.finrank ℂ V ≤ D)
    (hVc : ∀ f ∈ V, Continuous f) (hVr : ∀ f ∈ V, ∀ k : adelicMaximalCompact K, (fun x => f (x * k)) ∈ V)
    (f : adelicMaximalCompact K → ℂ) (hf : f ∈ V) (hf1 : ∫ y, ‖f y‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
    (k : adelicMaximalCompact K) : ‖f k‖ ≤ Real.sqrt D := by
  haveI := hVfd
  haveI : BorelSpace (adelicMaximalCompact K) := Subtype.borelSpace _
  haveI : (maximalCompactHaar K).Regular := by unfold maximalCompactHaar; infer_instance
  have h := MeasureTheory.sq_norm_apply_mul_measureReal_le_finrank_mul_integral_sq_norm_of_forall_mul_right_mem
    (maximalCompactHaar K) V hVc hVr f hf k
  rw [probReal_univ, mul_one] at h
  have h2 : ‖f k‖ ^ 2 ≤ (D : ℝ) := by
    refine h.trans ?_
    calc (Module.finrank ℂ V : ℝ) * ∫ y, ‖f y‖ ^ 2 ∂(maximalCompactHaar K) ≤ (D : ℝ) * 1 :=
          mul_le_mul (by exact_mod_cast hVD) hf1 (integral_nonneg fun _ => by positivity) (Nat.cast_nonneg _)
      _ = D := mul_one _
  rw [← Real.sqrt_sq (norm_nonneg (f k))]
  exact Real.sqrt_le_sqrt h2

theorem integral_mul_conj_eq_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℂ) :
    ∫ x, f x * conj (f x) ∂μ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  calc ∫ x, f x * conj (f x) ∂μ = ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show f x * conj (f x) = ((‖f x‖ ^ 2 : ℝ) : ℂ)
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    _ = ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := integral_ofReal

theorem main
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g))
      (t : ℝ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K →
      ‖ψf ((t : ℂ) * Complex.I) k‖ ≤ C ∧
        ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) k‖ ≤ C := by
  intro αm
  have hNb : N ≠ ⊥ := ne_bot_of_forall_dvd_mem SK N hN
  obtain ⟨D, hD⟩ :=
    AutomorphicForm.exists_forall_exists_submodule_maximalCompact_finrank_le_restrict_mem_of_isInducedSection_principalLevel_archCutSubmodule
      K N hNb tysK
  refine ⟨Real.sqrt D + 1, by positivity, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν τμ τν hτμ hτν mμ mν hmμ hmν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat
    hψflev hψfty hψfn Oψ Eψ Nψ hEψ t k hk
  have hsD : Real.sqrt D ≤ Real.sqrt D + 1 := by linarith

  have hψc : ∀ s, Continuous (ψf s) := fun s =>
    hψfjc.comp (continuous_const.prodMk continuous_id)
  have hψKu0 : ∀ s, ∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K,
        (fun k : ↥(archRowIsometrySubgroup K w) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := by
    intro s w; obtain ⟨W, hW, hmem⟩ := hψfKu w; exact ⟨W, hW, fun g => hmem s g⟩

  have hflatK : ∀ s, (fun k : adelicMaximalCompact K => ψf s (k : AdelicGL2 (𝓞 K) K)) =
      fun k : adelicMaximalCompact K => ψf 0 (k : AdelicGL2 (𝓞 K) K) := fun s => funext fun k => hψfflat s k
  constructor
  ·
    obtain ⟨V, hVfd, hVD, hVc, hVr, hmem⟩ := hD hαm μ ν hμ hν hμic hνic hμc hνc 0 (ψf 0) (hψf 0) (hψc 0) (hψflev 0)
      (hψKu0 0) (hψfty 0)
    rw [hψfflat _ ⟨k, hk⟩]
    exact (sq_le_of_mem V hVfd hVD hVc hVr _ hmem hψfn ⟨k, hk⟩).trans hsD
  ·
    set M : AdelicGL2 (𝓞 K) K → ℂ := fun g => ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) g
      with hM
    obtain ⟨hMind, hMcont, hMlev, hMKu⟩ :=
      AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_axis_continuation_weylIntertwiningIntegral_of_forall_mem_principalLevel
        K hαm μ ν hμ hν hμic hνic hμc hνc N ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflev Oψ Eψ Nψ hEψ t
    have hNty : Nψ ((t : ℂ) * Complex.I) ∈ archCutSubmodule K tysK :=
      AutomorphicForm.axis_continuation_weylIntertwiningIntegral_mem_archCutSubmodule_of_forall_mem_archCutSubmodule
        K tysK hαm μ ν hμ hν hμic hνic hμc hνc ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfty Oψ Eψ Nψ hEψ t
    have hMty : M ∈ archCutSubmodule K tysK := by
      have : M = ((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ • Nψ ((t : ℂ) * Complex.I) := by
        funext g; rfl
      rw [this]; exact Submodule.smul_mem _ _ hNty
    have hMlev' : ∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, M (g * u) = M g := by
      intro g u hu; show _ * _ = _ * _; rw [hMlev g u hu]
    obtain ⟨V, hVfd, hVD, hVc, hVr, hmem⟩ := hD hαm ν μ hν hμ hνic hμic hνc hμc (-((t : ℂ) * Complex.I)) M hMind hMcont hMlev'
      hMKu hMty

    have hiso := AutomorphicForm.integral_axis_continuation_weylIntertwiningIntegral_mul_conj_eq_integral_mul_conj_of_isUnitaryChar
      K hαm μ ν hμ hν hμic hνic hμc hνc ψf hψf hψfK hψff hψfjc hψfhol hψfKu ψf hψf hψfK hψff hψfjc hψfhol hψfKu
      Oψ Eψ Nψ hEψ Oψ Eψ Nψ hEψ t
    have hM1 : ∫ y, ‖M (y : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1 := by
      have h1 : ((∫ y, ‖M (y : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) : ℝ) : ℂ) =
          ((∫ y, ‖ψf 0 (y : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) : ℝ) : ℂ) := by
        rw [← integral_mul_conj_eq_ofReal, ← integral_mul_conj_eq_ofReal]
        refine hiso.trans ?_
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show ψf _ _ * conj (ψf _ _) = ψf 0 _ * conj (ψf 0 _)
        rw [hψfflat]
      rw [Complex.ofReal_inj.mp h1]; exact hψfn
    exact (sq_le_of_mem V hVfd hVD hVc hVr _ hmem hM1 ⟨k, hk⟩).trans hsD

end KSUP

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ))
        :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∃ (C : ℝ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
      (τμ τν : InfinitePlace K → ℝ)
      (_hτμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ v : ℝ) : ℂ) * Complex.I))
      (_hτν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν v : ℝ) : ℂ) * Complex.I))
      (mμ mν : InfinitePlace K → ℤ)
      (_hmμ : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar μ v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ v))
      (_hmν : ∀ (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar ν v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν v))
      (ψf : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite K (ψf s))
      (_hψff : ∀ s, IsKfSmooth K (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => ψf s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact K),
        ψf s (k : AdelicGL2 (𝓞 K) K) = ψf 0 (k : AdelicGL2 (𝓞 K) K))
      (_hψflev : ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf s (g * u) = ψf s g)
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK)
      (_hψfn : ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) ≤ 1)
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 K) K => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Eψ s g = ψf s g + ∑' ξ : K, ψf s (adelicWeyl (𝓞 K) K
          * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 K) K,
        Nψ s g = weylIntertwiningIntegral (𝓞 K) K (adelicAddHaar (𝓞 K) K) (ψf s) g))
      (t : ℝ) (k : AdelicGL2 (𝓞 K) K), k ∈ adelicMaximalCompact K →
      ‖ψf ((t : ℂ) * Complex.I) k‖ ≤ C ∧
        ‖((((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ))⁻¹ * Nψ ((t : ℂ) * Complex.I) k‖ ≤ C :=
  KSUP.main K SK ξK hξc hξt N hN tysK w hξw

end

end S_AutomorphicForm_exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat
end P2MW
export P2MW.S_AutomorphicForm_exists_forall_norm_apply_le_and_norm_axis_intertwining_apply_le_of_mem_adelicMaximalCompact_of_flat (solution)
