-- Prove2me | solution 1 for AutomorphicForm.exists_basis_forall_flat_isInducedSection_family_eq_sum_and_norm_sq_le_lintegral_of_principalLevel_archCutSubmodule
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/84bd97f6-0c86-5a7c-afab-6332ac807a69

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_NumberField_NormPowChar
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

import Theorems.Thm_AutomorphicForm_exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule
import Theorems.Thm_AutomorphicForm_exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
import Theorems.Thm_AutomorphicForm_eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq
import Theorems.Thm_MeasureTheory_exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_basis_forall_flat_isInducedSection_family_eq_sum_and_norm_sq_le_lintegral_of_principalLevel_archCutSubmodule
p2m_attr_erase "instance" "instCountableOfNumberField_definitions instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions"
p2m_attr_erase "simp" "NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent AutomorphicForm.ArchDirComplex.iH.sizeOf_spec AutomorphicForm.ArchDirComplex.H.sizeOf_spec AutomorphicForm.ArchDirComplex.Fm.sizeOf_spec AutomorphicForm.ArchDirComplex.iFm.sizeOf_spec AutomorphicForm.ArchDirComplex.iE.sizeOf_spec AutomorphicForm.ArchDirComplex.E.sizeOf_spec AutomorphicForm.ArchDir.E.sizeOf_spec AutomorphicForm.ArchDir.H.sizeOf_spec AutomorphicForm.ArchDir.Fm.sizeOf_spec AutomorphicForm.CuspidalConstituent.rightRegular_apply AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed AutomorphicForm.fnTwist_zero AutomorphicForm.fnTwist_apply"

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

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
    ∃ (n : ℕ) (b : Fin n → AdelicGL2 (𝓞 K) K → ℂ) (C : ℝ), 0 < C ∧
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 K) K μ) (_hν : IsUnitaryChar (𝓞 K) K ν)
      (_hμic : IsIdeleClassChar (𝓞 K) K μ) (_hνic : IsIdeleClassChar (𝓞 K) K ν)
      (_hμc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ))
      (_hνc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ))
      (_hμν : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) = ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
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
      (_hψfty : ∀ s : ℂ, ψf s ∈ archCutSubmodule K tysK),
    ∃ (a : Fin n → ℂ) (φ : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ),
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K), ψf s g = ∑ i, a i * φ i s g) ∧
      (∀ i, ‖a i‖ ^ 2 ≤ C * ∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) ∧
      ∀ i, a i ≠ 0 →
        (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ i s)) ∧
        (∀ s, IsArchKFinite K (φ i s)) ∧
        (∀ s, IsKfSmooth K (φ i s)) ∧
        Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ i p.1 p.2) ∧
        (∀ g, Differentiable ℂ (fun s => φ i s g)) ∧
        (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
          FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
            (fun k : ↥(archRowIsometrySubgroup K v) => φ i s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
        (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ i s (g * u) = φ i s g) ∧
        (∀ s : ℂ, φ i s ∈ archCutSubmodule K tysK) ∧
        (∀ (s : ℂ) (k : adelicMaximalCompact K), φ i s (k : AdelicGL2 (𝓞 K) K) = b i (k : AdelicGL2 (𝓞 K) K)) := by
  intro αm
  classical
  obtain ⟨n, μs, νs, ψs, hadm, hint, hdef, hspan⟩ :=
    AutomorphicForm.exists_fin_admissible_forall_flat_restrict_eq_sum_sameClass_of_principalLevel_archCutSubmodule
      K SK ξK hξc hξt N hN tysK w hξw
  obtain ⟨C, hC, hdom⟩ := MeasureTheory.exists_forall_norm_sq_le_mul_integral_norm_sq_sum_of_definite (maximalCompactHaar K)
    (fun i (k : adelicMaximalCompact K) => ψs i 0 (k : AdelicGL2 (𝓞 K) K)) hint hdef
  refine ⟨n, fun i => ψs i 0, C, hC, ?_⟩
  intro hαm μ ν hμ hν hμic hνic hμc hνc hμν ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψfflat hψflev hψfty
  obtain ⟨a, ha, hclass⟩ := hspan hαm μ ν ψf
    ⟨hμ, hν, hμic, hνic, hμc, hνc, hμν, hψf, hψfK, hψff, hψfjc, hψfhol, hψfKu, hψfflat, hψflev, hψfty⟩
  have hext : ∀ i, a i ≠ 0 → ∃ φ : ℂ → AdelicGL2 (𝓞 K) K → ℂ,
      ((IsUnitaryChar (𝓞 K) K μ ∧ IsUnitaryChar (𝓞 K) K ν ∧
      IsIdeleClassChar (𝓞 K) K μ ∧ IsIdeleClassChar (𝓞 K) K ν ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ z : ℂˣ) : ℂ)) ∧
      (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν z : ℂˣ) : ℂ)) ∧
      (∀ z : (AdeleRing (𝓞 K) K)ˣ,
        ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * (((NumberField.TateGlobal.ideleNorm K z) ^ (w) : ℝ) : ℂ) =
          ((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
      (∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φ s)) ∧
      (∀ s, IsArchKFinite K (φ s)) ∧
      (∀ s, IsKfSmooth K (φ s)) ∧
      Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φ p.1 p.2) ∧
      (∀ g, Differentiable ℂ (fun s => φ s g)) ∧
      (∀ v : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K v) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K v) => φ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
      (∀ (s : ℂ) (k : adelicMaximalCompact K),
        φ s (k : AdelicGL2 (𝓞 K) K) = φ 0 (k : AdelicGL2 (𝓞 K) K)) ∧
      (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φ s (g * u) = φ s g) ∧
      (∀ s : ℂ, φ s ∈ archCutSubmodule K tysK)) ∧
      ∀ (s : ℂ) (k : adelicMaximalCompact K), φ s (k : AdelicGL2 (𝓞 K) K) = ψs i 0 (k : AdelicGL2 (𝓞 K) K)) :=
    fun i hi =>
      AutomorphicForm.exists_admissible_flat_family_restrict_eq_of_sameClass_of_principalLevel_archCutSubmodule
        K SK ξK hξc hξt N hN tysK w hξw hαm (μs i) (νs i) (ψs i) (hadm hαm i) μ ν hμ hν hμic hνic hμc hνc hμν (hclass i hi)

  let φ : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun i => if hi : a i ≠ 0 then (hext i hi).choose else fun _ _ => 0
  have hφ : ∀ i (hi : a i ≠ 0), φ i = (hext i hi).choose := fun i hi => by simp only [φ, dif_pos hi]
  have hφK : ∀ i (s : ℂ) (k : adelicMaximalCompact K), a i * φ i s (k : AdelicGL2 (𝓞 K) K) = a i * ψs i 0 (k : AdelicGL2 (𝓞 K) K) := by
    intro i s k
    by_cases hi : a i ≠ 0
    · rw [hφ i hi, (hext i hi).choose_spec.2 s k]
    · push_neg at hi; rw [hi, zero_mul, zero_mul]
  have hsec : ∀ s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (fun g => ∑ i, a i * φ i s g) := by
    intro s b hb g
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : a i ≠ 0
    · rw [hφ i hi, ((hext i hi).choose_spec.1).2.2.2.2.2.2.2.1 s b hb g]; ring
    · push_neg at hi; rw [hi, zero_mul, zero_mul, mul_zero]
  refine ⟨a, φ, ?_, ?_, ?_⟩
  · intro s g
    have hK : ∀ k : adelicMaximalCompact K, ψf s (k : AdelicGL2 (𝓞 K) K) = (fun g => ∑ i, a i * φ i s g) (k : AdelicGL2 (𝓞 K) K) := by
      intro k
      show ψf s (k : AdelicGL2 (𝓞 K) K) = ∑ i, a i * φ i s (k : AdelicGL2 (𝓞 K) K)
      rw [hψfflat s k, ha k]
      exact Finset.sum_congr rfl fun i _ => (hφK i s k).symm
    exact congrFun (AutomorphicForm.eq_of_isInducedSection_of_forall_adelicMaximalCompact_eq K _ _ (ψf s) _ (hψf s) (hsec s) hK) g
  · intro i
    have h1 := hdom a i
    have h2 : (∫ k, ‖∑ j, a j * ψs j 0 ((k : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K)) =
        ∫ k, ‖ψf 0 ((k : adelicMaximalCompact K) : AdelicGL2 (𝓞 K) K)‖ ^ 2 ∂(maximalCompactHaar K) := by
      congr 1; funext k; rw [ha k]
    rw [h2] at h1; exact h1
  · intro i hi
    obtain ⟨⟨-, -, -, -, -, -, -, h8, h9, h10, h11, h12, h13, -, h15, h16⟩, hb⟩ := (hext i hi).choose_spec
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try simp only [hφ i hi])
    · exact h8
    · exact h9
    · exact h10
    · exact h11
    · exact h12
    · exact h13
    · exact h15
    · exact h16
    · exact hb

end S_AutomorphicForm_exists_basis_forall_flat_isInducedSection_family_eq_sum_and_norm_sq_le_lintegral_of_principalLevel_archCutSubmodule
end P2MW
export P2MW.S_AutomorphicForm_exists_basis_forall_flat_isInducedSection_family_eq_sum_and_norm_sq_le_lintegral_of_principalLevel_archCutSubmodule (solution)
