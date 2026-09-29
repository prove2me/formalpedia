-- Prove2me | solution 1 for AutomorphicForm.isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/f662adfa-6951-513c-9f81-831f1d016cab

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
import Theorems.Thm_AutomorphicForm_etaFst_etaSnd_mul_normPowChar_eq_shift
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

open AutomorphicForm

open FLT.SmoothVectors

theorem solution
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (tysK : ArchTypeFamily K) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
      (n : ℕ)
      (φE : Fin n → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hφE : ∀ j s, IsInducedSection (𝓞 K) K (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φE j s))
      (_hφEK : ∀ j s, IsArchKFinite K (φE j s))
      (_hφEf : ∀ j s, IsKfSmooth K (φE j s))
      (_hφEjc : ∀ j, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => φE j p.1 p.2))
      (_hφEhol : ∀ j (g : AdelicGL2 (𝓞 K) K), Differentiable ℂ (fun s => φE j s g))
      (_hφEKu : ∀ j (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φE j s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφEflat : ∀ j (s : ℂ) (k : adelicMaximalCompact K),
        φE j s (k : AdelicGL2 (𝓞 K) K) = φE j 0 (k : AdelicGL2 (𝓞 K) K))
      (_hφElev : ∀ j (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φE j s (g * u) = φE j s g)
      (_hφEty : ∀ j (s : ℂ), φE j s ∈ archCutSubmodule K tysK)
      (τ : ℝ) (c : Fin n → ℂ → ℂ) (_hc : ∀ j, Differentiable ℂ (c j)),
    let ψ : ℂ → AdelicGL2 (𝓞 K) K → ℂ := fun s g => ∑ j, c j s * φE j (s + (τ : ℂ) * Complex.I) g
    (∀ s, IsInducedSection (𝓞 K) K (etaFst (μ * NumberField.TateGlobal.normPowChar K τ) αm hαm s)
        (etaSnd (ν * (NumberField.TateGlobal.normPowChar K τ)⁻¹) αm hαm s) (ψ s)) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψ p.1 p.2) ∧
    (∀ g : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => ψ s g)) ∧
    (∀ s, IsArchKFinite K (ψ s)) ∧
    (∀ s, IsKfSmooth K (ψ s)) ∧
    (∀ w : InfinitePlace K, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψ s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W) ∧
    (∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψ s (g * u) = ψ s g) ∧
    (∀ s, ψ s ∈ archCutSubmodule K tysK) := by
  classical
  intro αm hαm μ ν n φE hφE hφEK hφEf hφEjc hφEhol hφEKu hφEflat hφElev hφEty τ c hc ψ
  have hψ : ∀ s g, ψ s g = ∑ j, c j s * φE j (s + (τ : ℂ) * Complex.I) g := fun s g => rfl
  have hψfun : ∀ s, ψ s = ∑ j, c j s • φE j (s + (τ : ℂ) * Complex.I) := fun s => by
    funext g; rw [hψ, Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]
  have hαI : ∀ x : (AdeleRing (𝓞 K) K)ˣ, ((αm x : ℝˣ) : ℝ) = NumberField.TateGlobal.ideleNorm K x := fun x => rfl
  refine ⟨fun s => ?_, ?_, fun g => ?_, fun s => ?_, fun s => ?_, fun w => ?_, fun s g u hu => ?_, fun s => ?_⟩
  ·
    obtain ⟨h1, -, -, -⟩ := AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift K _ hαm hαI μ τ s
    obtain ⟨-, -, -, h4⟩ := AutomorphicForm.etaFst_etaSnd_mul_normPowChar_eq_shift K _ hαm hαI ν τ s
    rw [h1, h4]
    intro b hb g
    rw [hψ, hψ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hφE j _ b hb g]
    ring
  ·
    have : (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψ p.1 p.2) = fun p => ∑ j, c j p.1 * φE j (p.1 + (τ : ℂ) * Complex.I) p.2 := by
      funext p; exact hψ p.1 p.2
    rw [this]
    refine continuous_finset_sum _ fun j _ => ?_
    exact ((hc j).continuous.comp continuous_fst).mul
      ((hφEjc j).comp ((continuous_fst.add continuous_const).prodMk continuous_snd))
  ·
    have : (fun s => ψ s g) = fun s => ∑ j, c j s * φE j (s + (τ : ℂ) * Complex.I) g := by funext s; exact hψ s g
    rw [this]
    refine Differentiable.fun_sum fun j _ => ?_
    exact (hc j).mul ((hφEhol j g).comp (differentiable_id.add_const _))
  ·
    intro w
    choose S hS using fun j => hφEK j (s + (τ : ℂ) * Complex.I) w
    refine ⟨Finset.univ.biUnion S, fun k hk => ?_⟩
    have h1 : (fun x => ψ s (x * k)) = ∑ j, c j s • fun x => φE j (s + (τ : ℂ) * Complex.I) (x * k) := by
      funext x; rw [hψ, Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    refine Submodule.span_mono ?_ (hS j k hk)
    intro f hf
    exact Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hf⟩)
  ·
    let St : Fin n → Subgroup (finiteAdelicGL2Subgroup K) := fun j =>
      MulAction.stabilizer (finiteAdelicGL2Subgroup K)
        (RightTranslationFn.mk (φE j (s + (τ : ℂ) * Complex.I)) : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ)
    have hopen : IsOpen ((⨅ j, St j : Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K)) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun j => hφEf j (s + (τ : ℂ) * Complex.I)
    show IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup K)
      (RightTranslationFn.mk (ψ s) : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K))
    refine Subgroup.isOpen_mono ?_ hopen
    intro k hk
    rw [Subgroup.mem_iInf] at hk
    have hkj : ∀ j (x : AdelicGL2 (𝓞 K) K), φE j (s + (τ : ℂ) * Complex.I) (x * (k : AdelicGL2 (𝓞 K) K)) = φE j (s + (τ : ℂ) * Complex.I) x := by
      intro j x
      have h2 := MulAction.mem_stabilizer_iff.mp (hk j)
      have h3 := congrArg (fun F : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ => F.toFun x) h2
      simp only [Subgroup.smul_def, RightTranslationFn.toFun_smul] at h3
      exact h3
    rw [MulAction.mem_stabilizer_iff]
    refine RightTranslationFn.ext fun x => ?_
    rw [Subgroup.smul_def, RightTranslationFn.toFun_smul]
    show ψ s (x * (k : AdelicGL2 (𝓞 K) K)) = ψ s x
    rw [hψ, hψ]
    exact Finset.sum_congr rfl fun j _ => by rw [hkj j x]
  ·
    choose W hWfd hW using fun j => hφEKu j w
    haveI : ∀ j, FiniteDimensional ℂ (W j) := hWfd
    refine ⟨⨆ j, W j, inferInstance, fun s g => ?_⟩
    have h1 : (fun k : ↥(archRowIsometrySubgroup K w) => ψ s (g * (k : AdelicGL2 (𝓞 K) K))) =
        ∑ j, c j s • fun k : ↥(archRowIsometrySubgroup K w) => φE j (s + (τ : ℂ) * Complex.I) (g * (k : AdelicGL2 (𝓞 K) K)) := by
      funext k; rw [hψ, Finset.sum_apply]; simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (le_iSup W j (hW j _ g))
  ·
    rw [hψ, hψ]
    exact Finset.sum_congr rfl fun j _ => by rw [hφElev j _ g u hu]
  ·
    rw [hψfun]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hφEty j _)

end S_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family
end P2MW
export P2MW.S_AutomorphicForm_isInducedSection_and_continuous_and_isArchKFinite_and_isKfSmooth_sum_mul_shift_of_flat_family (solution)
