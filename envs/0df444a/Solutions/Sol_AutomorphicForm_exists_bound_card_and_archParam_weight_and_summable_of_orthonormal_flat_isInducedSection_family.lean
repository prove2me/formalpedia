-- Prove2me | solution 1 for AutomorphicForm.exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/e92afd4b-dbb1-5d02-a24d-39e0e983724b

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
import Theorems.Thm_NumberField_TateGlobal_exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar
import Theorems.Thm_AutomorphicForm_exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot
import Theorems.Thm_AutomorphicForm_exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
import Theorems.Thm_AutomorphicForm_exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent NumberField.SIdele.fibre_inr NumberField.SIdele.toFinite_hom_apply NumberField.SIdele.fibre_inl NumberField.SIdele.toArch_hom_apply GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply NumberField.SUnits.coe_unitOfValuedEqOne NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl NumberField.SUnits.val_zsmul NumberField.SUnits.val_add"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

namespace Ws31
namespace C0Asm

theorem infinite_heightOneSpectrum (K : Type) [Field K] [NumberField K] :
    Infinite (HeightOneSpectrum (𝓞 K)) := by
  classical
  have key : ∀ p : Nat.Primes, ∃ v : HeightOneSpectrum (𝓞 K),
      Ideal.comap (algebraMap ℤ (𝓞 K)) v.asIdeal = Ideal.span {((p : ℕ) : ℤ)} := by
    intro p
    have hp0 : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast p.2.ne_zero
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hp0).mpr (Nat.prime_iff_prime_int.mp p.2)
    have hinj : Function.Injective (algebraMap ℤ (𝓞 K)) := RingHom.injective_int _
    obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {((p : ℕ) : ℤ)})
      (⊥ : Ideal (𝓞 K)) (by rw [Ideal.comap_bot_of_injective _ hinj]; exact bot_le)
    refine ⟨⟨Q, hQ, ?_⟩, hQc⟩
    rintro rfl
    rw [Ideal.comap_bot_of_injective _ hinj] at hQc
    exact hp0 (Ideal.span_singleton_eq_bot.mp hQc.symm)
  choose f hf using key
  haveI : Infinite Nat.Primes := Set.infinite_coe_iff.mpr Nat.infinite_setOf_prime
  refine Infinite.of_injective f fun p q h => ?_
  have h1 : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, h]
  have h2 := Int.associated_iff_natAbs.mp (Ideal.span_singleton_eq_span_singleton.mp h1)
  exact Subtype.ext (by simpa using h2)

theorem ne_bot_of_forall_dvd_mem_finset (K : Type) [Field K] [NumberField K]
    (SK : Finset (HeightOneSpectrum (𝓞 K))) (N : Ideal (𝓞 K))
    (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK) : N ≠ ⊥ := by
  intro h
  subst h
  have hall : ∀ v : HeightOneSpectrum (𝓞 K), v ∈ SK := fun v => hN v (dvd_zero _)
  haveI := infinite_heightOneSpectrum K
  have hfin : Finite (HeightOneSpectrum (𝓞 K)) :=
    Finite.of_injective (fun v => (⟨v, hall v⟩ : SK)) (fun a b h => by simpa using h)
  exact not_finite (HeightOneSpectrum (𝓞 K))

theorem localChar_mul_inv_apply (K : Type) [Field K] [NumberField K]
    (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) (t : (v.adicCompletion K)ˣ) :
    NumberField.TateGlobal.localChar (μ * ν⁻¹) v t =
      NumberField.TateGlobal.localChar μ v t * (NumberField.TateGlobal.localChar ν v t)⁻¹ := rfl

theorem main
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
        ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
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
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
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
      (_hdiag : ∀ e : ιE, μ e = ν e ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z ≠ ν e z)
      ,
    ∃ (D : ℕ) (τμ τν : ιE → InfinitePlace K → ℝ) (mμ mν : ιE → InfinitePlace K → ℤ) (M₀ : ℕ) (nρ : ℕ)
      (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (B₀ : ℕ),
      (∀ e, nE e ≤ D) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ e v : ℝ) : ℂ) * Complex.I) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν e v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν e v)) ∧
      (∀ e, 0 < nE e → ∀ v : InfinitePlace K, |mμ e v| ≤ (M₀ : ℤ) ∧ |mν e v| ≤ (M₀ : ℤ)) ∧
      (∀ e, 0 < nE e →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → NumberField.TateGlobal.IsUnramifiedCharAt (μ e * (ν e)⁻¹) v) ∧
        ∃ r : Fin nρ, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            NumberField.TateGlobal.localChar (μ e * (ν e)⁻¹) v u = ρs r v u) ∧
      (∀ B : ℕ, B₀ ≤ B →
        (∀ e : ιE, MeasureTheory.Integrable
          (fun t : ℝ => (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)))) ∧
        Summable (fun e : ιE => if 0 < nE e then
          ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)) else 0) ∧
        Summable (fun e : ιE => if 0 < nE e then
          (1 + ∑ v : InfinitePlace K, (|τμ e v| + |τν e v|)) ^ (-(B : ℝ)) else 0)) := by
  intro αm hαm ιE _inst μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu
    _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE _hdiag

  have hAμ := fun e => NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (μ e) (_hμ e) (_hμc e)
  have hAν := fun e => NumberField.TateGlobal.exists_archParam_weight_archLocalChar_eq_of_isUnitaryChar K (ν e) (_hν e) (_hνc e)
  choose τμ mμ hτμ hmμ hrμ using hAμ
  choose τν mν hτν hmν hrν using hAν

  have hφc0 : ∀ (e : ιE) (j : Fin (nE e)), Continuous (φE e j 0) := fun e j =>
    (_hφEjc e j).comp (continuous_const.prodMk continuous_id)
  have hφKu0 : ∀ (e : ιE) (j : Fin (nE e)) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ g : AdelicGL2 (𝓞 K) K,
        (fun k : ↥(archRowIsometrySubgroup K w) => φE e j 0 (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W := fun e j w => by
    obtain ⟨W, hW, h⟩ := _hφEKu e j w
    exact ⟨W, hW, fun g => h 0 g⟩
  have hne : ∀ (e : ιE) (j : Fin (nE e)), φE e j 0 ≠ 0 := by
    intro e j h
    have h1 := _hφEon e j j
    rw [if_pos rfl] at h1
    have h2 : (fun k : ↥(adelicMaximalCompact K) => φE e j 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE e j 0 (k : AdelicGL2 (𝓞 K) K)))
        = fun _ => 0 := by
      funext k; rw [h]; simp
    rw [h2, integral_zero] at h1
    exact zero_ne_one h1

  obtain ⟨D, hD⟩ := AutomorphicForm.exists_forall_le_of_orthonormal_isInducedSection_principalLevel_archCutSubmodule_of_ne_bot K N
    (ne_bot_of_forall_dvd_mem_finset K SK N hN) tysK
  have hDim : ∀ e, nE e ≤ D := fun e =>
    hD hαm (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e) (nE e) (fun j => φE e j 0)
      (fun j => _hφE e j 0) (fun j => _hφEK e j 0) (fun j => _hφEf e j 0) (fun j => hφc0 e j) (fun j w => hφKu0 e j w)
      (fun j g => _hφElev e j 0 g) (fun j => _hφEty e j 0) (fun i j => _hφEon e i j)

  obtain ⟨M₀, hM₀⟩ := AutomorphicForm.exists_forall_abs_weight_le_of_isInducedSection_ne_zero_archCutSubmodule
    K ξK hξc hξt N tysK w hξw
  have hW : ∀ e, 0 < nE e → ∀ v : InfinitePlace K, |mμ e v| ≤ (M₀ : ℤ) ∧ |mν e v| ≤ (M₀ : ℤ) := fun e he v =>
    hM₀ hαm (μ e) (ν e) (_hμ e) (_hν e) (_hμic e) (_hνic e) (_hμc e) (_hνc e) (_hμν e)
      (φE e ⟨0, he⟩ 0) (_hφE e _ 0) (_hφEK e _ 0) (_hφEf e _ 0) (hφc0 e _) (hφKu0 e _)
      (fun g => _hφElev e _ 0 g) (_hφEty e _ 0) (hne e _) (mμ e) (mν e) (hmμ e) (hmν e)
      (fun v hv => ⟨hrμ e v hv, hrν e v hv⟩) v

  obtain ⟨nρ, ρs, hρ⟩ :=
    AutomorphicForm.exists_finite_forall_isUnramifiedCharAt_and_localChar_eq_of_isInducedSection_etaFst_etaSnd_of_ne_zero_of_principalLevel
      K SK N hN
  let ρs' : Fin (nρ * nρ) → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ :=
    fun r v => ρs (finProdFinEquiv.symm r).1 v * (ρs (finProdFinEquiv.symm r).2 v)⁻¹
  have hρe := fun e (he : 0 < nE e) =>
    hρ hαm (μ e) (ν e) 0 (φE e ⟨0, he⟩ 0) (_hφE e _ 0) (hne e _) (fun g => _hφElev e _ 0 g)
  have hR : ∀ e, 0 < nE e →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → NumberField.TateGlobal.IsUnramifiedCharAt (μ e * (ν e)⁻¹) v) ∧
      ∃ r : Fin (nρ * nρ), ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
        ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          NumberField.TateGlobal.localChar (μ e * (ν e)⁻¹) v u = ρs' r v u := by
    intro e he
    obtain ⟨hunr, r, r', hrr⟩ := hρe e he
    refine ⟨fun v hv t ht ht' => ?_, ⟨finProdFinEquiv (r, r'), fun v hv u hu hu' => ?_⟩⟩
    · rw [localChar_mul_inv_apply, (hunr v hv).1 t ht ht', (hunr v hv).2 t ht ht', inv_one, mul_one]
    · obtain ⟨h1, h2⟩ := hrr v hv u hu hu'
      show _ = (ρs (finProdFinEquiv.symm (finProdFinEquiv (r, r'))).1 v * (ρs (finProdFinEquiv.symm (finProdFinEquiv (r, r'))).2 v)⁻¹) u
      rw [Equiv.symm_apply_apply, localChar_mul_inv_apply, h1, h2]
      rfl

  obtain ⟨B₀, hB₀'⟩ :=
    AutomorphicForm.exists_forall_integrable_and_summable_rpow_neg_archParam_of_isUnitaryChar_of_pairwise_ne
      K SK ξK hξc hξt w hξw M₀ nρ ρs
  have hB₀ := hB₀' ιE μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE τμ τν
    (fun e v x h1 h2 => ⟨hτμ e v x h1 h2, hτν e v x h1 h2⟩) mμ mν (fun e v x h => ⟨hmμ e v x h, hmν e v x h⟩) hW hρe
  exact ⟨D, τμ, τν, mμ, mν, M₀, nρ * nρ, ρs', B₀, hDim,
    fun e v x h1 h2 => ⟨hτμ e v x h1 h2, hτν e v x h1 h2⟩,
    fun e v x h => ⟨hmμ e v x h, hmν e v x h⟩, hW, hR, hB₀⟩

end Ws31.C0Asm

theorem solution
    (K : Type) [Field K] [NumberField K] [DecidableEq (HeightOneSpectrum (𝓞 K))]
    (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (ΦK : Set (AdelicGL2 (𝓞 K) K))
    (cK uK d₁K d₂K : ℝ) (TK : Finset (AdelicGL2 (𝓞 K) K))
    (hcK : 0 < cK) (hd₁K : 0 < d₁K) (hdK : d₁K < d₂K)
    (hcovK : CoversModCentre K (⋃ x ∈ TK, (· * x) '' centreCutSiegelSet K cK uK d₁K d₂K))
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure] (ΩK : Set (AdeleRing (𝓞 K) K)ˣ)
    (hΩK : IsFundamentalDomain
      (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range ΩK νZK)
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξK : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (hξt : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
        ξK ⟨z, Subgroup.mem_top z⟩ = 1)
    (N : Ideal (𝓞 K)) (hN : ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ N → v ∈ SK)
    (tysK : ArchTypeFamily K)
    (faK : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (fSK : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ)
    (w : ℝ) (hξw : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = ((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ)) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (ιE : Type) [Countable ιE]
      (μ ν : ιE → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ : ∀ e, IsUnitaryChar (𝓞 K) K (μ e)) (_hν : ∀ e, IsUnitaryChar (𝓞 K) K (ν e))
      (_hμic : ∀ e, IsIdeleClassChar (𝓞 K) K (μ e)) (_hνic : ∀ e, IsIdeleClassChar (𝓞 K) K (ν e))
      (_hμc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ e z : ℂˣ) : ℂ))
      (_hνc : ∀ e, Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν e z : ℂˣ) : ℂ))
      (_hμν : ∀ (e : ιE) (z : (AdeleRing (𝓞 K) K)ˣ),
        ((μ e z : ℂˣ) : ℂ) * ((ν e z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
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
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          ((μ' z : ℂˣ) : ℂ) * ((ν' z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) →
        ∀ (t : ℝ) (φ₀ : AdelicGL2 (𝓞 K) K → ℂ),
        IsInducedSection (𝓞 K) K (etaFst μ' αm hαm ((t : ℂ) * Complex.I)) (etaSnd ν' αm hαm ((t : ℂ) * Complex.I)) φ₀ →
        Continuous φ₀ → IsArchKFinite K φ₀ →
        (∀ (g : AdelicGL2 (𝓞 K) K), ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ₀ (g * u) = φ₀ g) →
        φ₀ ∈ archCutSubmodule K tysK → φ₀ ≠ 0 →
        ∃ e : ιE, ∀ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z = μ' z ∧ ν e z = ν' z)
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
      (_hdiag : ∀ e : ιE, μ e = ν e ∨ ∃ z ∈ NumberField.TateGlobal.normOneIdeles K, μ e z ≠ ν e z)
      ,
    ∃ (D : ℕ) (τμ τν : ιE → InfinitePlace K → ℝ) (mμ mν : ιE → InfinitePlace K → ℤ) (M₀ : ℕ) (nρ : ℕ)
      (ρs : Fin nρ → ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ) (B₀ : ℕ),
      (∀ e, nE e ≤ D) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        0 < (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).re →
        (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)).im = 0 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τμ e v : ℝ) : ℂ) * Complex.I) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (((NumberField.TateGlobal.ideleNorm K (NumberField.TateGlobal.archUnitHom v x)) : ℝ) : ℂ) ^
            (((τν e v : ℝ) : ℂ) * Complex.I)) ∧
      (∀ (e : ιE) (v : InfinitePlace K) (x : (v.Completion)ˣ),
        ‖InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)‖ = 1 →
        ((NumberField.TateGlobal.archLocalChar (μ e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mμ e v) ∧
        ((NumberField.TateGlobal.archLocalChar (ν e) v x : ℂˣ) : ℂ) =
          (InfinitePlace.Completion.extensionEmbedding v (x : v.Completion)) ^ (mν e v)) ∧
      (∀ e, 0 < nE e → ∀ v : InfinitePlace K, |mμ e v| ≤ (M₀ : ℤ) ∧ |mν e v| ≤ (M₀ : ℤ)) ∧
      (∀ e, 0 < nE e →
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ SK → NumberField.TateGlobal.IsUnramifiedCharAt (μ e * (ν e)⁻¹) v) ∧
        ∃ r : Fin nρ, ∀ v ∈ SK, ∀ u : (v.adicCompletion K)ˣ, (u : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
          ((u⁻¹ : (v.adicCompletion K)ˣ) : v.adicCompletion K) ∈ v.adicCompletionIntegers K →
            NumberField.TateGlobal.localChar (μ e * (ν e)⁻¹) v u = ρs r v u) ∧
      (∀ B : ℕ, B₀ ≤ B →
        (∀ e : ιE, MeasureTheory.Integrable
          (fun t : ℝ => (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)))) ∧
        Summable (fun e : ιE => if 0 < nE e then
          ∫ t : ℝ, (1 + ∑ v : InfinitePlace K, (|t + τμ e v| + |t - τν e v|)) ^ (-(B : ℝ)) else 0) ∧
        Summable (fun e : ιE => if 0 < nE e then
          (1 + ∑ v : InfinitePlace K, (|τμ e v| + |τν e v|)) ^ (-(B : ℝ)) else 0)) :=
  Ws31.C0Asm.main K α β hα hαβ ΦK cK uK d₁K d₂K TK hcK hd₁K hdK hcovK νZK ΩK hΩK SK ξK hξc hξt N hN tysK faK fSK w hξw

end S_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family
end P2MW
export P2MW.S_AutomorphicForm_exists_bound_card_and_archParam_weight_and_summable_of_orthonormal_flat_isInducedSection_family (solution)
