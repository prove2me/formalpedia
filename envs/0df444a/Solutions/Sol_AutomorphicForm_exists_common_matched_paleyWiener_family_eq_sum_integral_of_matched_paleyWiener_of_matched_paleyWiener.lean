-- Prove2me | solution 1 for AutomorphicForm.exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/99ec3437-9bdc-52a3-965c-0727f5ab507f

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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace Ws31
namespace Merge

open AutomorphicForm NumberField.TateGlobal

variable {K : Type} [Field K] [NumberField K]

section EtaShift

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

end EtaShift

theorem mul_normPowChar_apply_of_mem (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ)
    {z : (AdeleRing (𝓞 K) K)ˣ} (hz : z ∈ normOneIdeles K) : (χ * normPowChar K τ) z = χ z := by
  rw [MonoidHom.mul_apply, normPowChar_eq_one_of_ideleNorm_eq_one τ ((mem_normOneIdeles_iff z).1 hz), mul_one]

theorem mul_normPowChar_inv_apply_of_mem (χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ)
    {z : (AdeleRing (𝓞 K) K)ˣ} (hz : z ∈ normOneIdeles K) : (χ * (normPowChar K τ)⁻¹) z = χ z := by
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply,
    normPowChar_eq_one_of_ideleNorm_eq_one τ ((mem_normOneIdeles_iff z).1 hz), inv_one, mul_one]

theorem one_add_abs_le (t Δ : ℝ) : 1 + |t| ≤ (1 + |Δ|) * (1 + |t + Δ|) := by
  have h : |t| ≤ |t + Δ| + |Δ| := by
    have := abs_sub (t + Δ) Δ
    rwa [add_sub_cancel_right] at this
  nlinarith [abs_nonneg Δ, abs_nonneg (t + Δ)]

end Ws31.Merge

end

open Ws31.Merge AutomorphicForm NumberField.TateGlobal in
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
    (hξu : ∀ z : (AdeleRing (𝓞 K) K)ˣ, ‖((ξK ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = 1) :
    let αm : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits
    letI := adeleBorel (𝓞 K) K
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ)),
    ∀
      (ι : Type) (b : ι → AdelicGL2 (𝓞 K) K → ℂ) (cls : ι → HeckeEigensystem K ℂ)
      (hb : ∀ i, cls i ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK ∧
          b i ∈ isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK (cls i) ⊓ archCutSubmodule K tysK)
      (hbn : ∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 1)
      (hbo : ∀ i j, i ≠ j → ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
          b i g * conj (b j g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0)
      (hbs : ∀ π ∈ cuspClasses K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK,
          {i | cls i = π}.Finite ∧
          Submodule.span ℂ (b '' {i | cls i = π}) = isotypicCuspSubmodule K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK N SK π ⊓ archCutSubmodule K tysK)
      (hbc : ∀ φ : AdelicGL2 (𝓞 K) K → ℂ,
          IsSmoothCuspAutomorphicFnAt K
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)) ξK φ →
          Continuous φ →
          (∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈
            (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).U N, φ (g * u) = φ g) →
          φ ∈ archCutSubmodule K tysK →
          (∀ i, ∫ g in AutomorphicForm.canonicalTruncationDomain K α β,
              φ g * conj (b i g) ∂(adelicGLHaar (Fin 2) (𝓞 K) K) = 0) →
          φ =ᵐ[(adelicGLHaar (Fin 2) (𝓞 K) K).restrict (AutomorphicForm.canonicalTruncationDomain K α β)] 0)
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
      (_hpairs : ∀ (μ' ν' : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ),
        IsUnitaryChar (𝓞 K) K μ' → IsUnitaryChar (𝓞 K) K ν' →
        IsIdeleClassChar (𝓞 K) K μ' → IsIdeleClassChar (𝓞 K) K ν' →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((μ' z : ℂˣ) : ℂ)) →
        (Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ν' z : ℂˣ) : ℂ)) →
        (∀ z : (AdeleRing (𝓞 K) K)ˣ, μ' z * ν' z = ξK ⟨z, Subgroup.mem_top z⟩) →
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
      (ιP₁ : Type) [Fintype ιP₁]
      (μP₁ νP₁ : ιP₁ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₁ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₁ e)) (_hν₁ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₁ e))
      (_hμic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₁ e)) (_hνic₁ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₁ e))
      (_hμc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₁ e x : ℂˣ) : ℂ))
      (_hμν₁ : ∀ (e : ιP₁)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₁ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₁ : ιP₁ → ιP₁) (_hr₁ : ∀ e, μP₁ (rP₁ e) = νP₁ e ∧ νP₁ (rP₁ e) = μP₁ e)
      (_hdist₁ : ∀ e e' : ιP₁, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₁ e x ≠ μP₁ e' x ∨ νP₁ e x ≠ νP₁ e' x)
      (ψf₁ : ιP₁ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₁ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₁ e) αm hαm s) (etaSnd (νP₁ e) αm hαm s) (ψf₁ e s))
      (_hψjc₁ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₁ e p.1 p.2))
      (_hψhol₁ : ∀ e g, Differentiable ℂ (fun s => ψf₁ e s g))
      (_hψK₁ : ∀ e s, IsArchKFinite K (ψf₁ e s)) (_hψsm₁ : ∀ e s, IsKfSmooth K (ψf₁ e s))
      (_hψKu₁ : ∀ (e : ιP₁) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₁ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₁ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₁ e x : ℂˣ) : ℂ))
      (_hψdec₁ : ∀ (e : ιP₁) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₁ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₁ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₁)
      (_hψrep₁ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₁ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₁ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₁ : ιP₁ → ιE) (τ₁ : ιP₁ → ℝ)
      (_hem₁ : ∀ i : ιP₁, μP₁ i = μ (em₁ i) * NumberField.TateGlobal.normPowChar K (τ₁ i) ∧
        νP₁ i = ν (em₁ i) * (NumberField.TateGlobal.normPowChar K (τ₁ i))⁻¹)
      (_hψlev₁ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₁ i s (g * u) = ψf₁ i s g)
      (_hψty₁ : ∀ i (s : ℂ), ψf₁ i s ∈ archCutSubmodule K tysK)
      (ιP₂ : Type) [Fintype ιP₂]
      (μP₂ νP₂ : ιP₂ → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ))
      (_hμ₂ : ∀ e, IsUnitaryChar (𝓞 K) K (μP₂ e)) (_hν₂ : ∀ e, IsUnitaryChar (𝓞 K) K (νP₂ e))
      (_hμic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (μP₂ e)) (_hνic₂ : ∀ e, IsIdeleClassChar (𝓞 K) K (νP₂ e))
      (_hμc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((μP₂ e x : ℂˣ) : ℂ))
      (_hμν₂ : ∀ (e : ιP₂)
        (z : (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z),
        μP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) * νP₂ e (z : (AdeleRing (𝓞 K) K)ˣ) = ξK z)
      (rP₂ : ιP₂ → ιP₂) (_hr₂ : ∀ e, μP₂ (rP₂ e) = νP₂ e ∧ νP₂ (rP₂ e) = μP₂ e)
      (_hdist₂ : ∀ e e' : ιP₂, e ≠ e' → ∃ x ∈ NumberField.TateGlobal.normOneIdeles K,
        μP₂ e x ≠ μP₂ e' x ∨ νP₂ e x ≠ νP₂ e' x)
      (ψf₂ : ιP₂ → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf₂ : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP₂ e) αm hαm s) (etaSnd (νP₂ e) αm hαm s) (ψf₂ e s))
      (_hψjc₂ : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf₂ e p.1 p.2))
      (_hψhol₂ : ∀ e g, Differentiable ℂ (fun s => ψf₂ e s g))
      (_hψK₂ : ∀ e s, IsArchKFinite K (ψf₂ e s)) (_hψsm₂ : ∀ e s, IsKfSmooth K (ψf₂ e s))
      (_hψKu₂ : ∀ (e : ιP₂) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf₂ e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc₂ : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP₂ e x : ℂˣ) : ℂ))
      (_hψdec₂ : ∀ (e : ιP₂) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ₂ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ₂ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ₂)
      (_hψrep₂ : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf₂ e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em₂ : ιP₂ → ιE) (τ₂ : ιP₂ → ℝ)
      (_hem₂ : ∀ i : ιP₂, μP₂ i = μ (em₂ i) * NumberField.TateGlobal.normPowChar K (τ₂ i) ∧
        νP₂ i = ν (em₂ i) * (NumberField.TateGlobal.normPowChar K (τ₂ i))⁻¹)
      (_hψlev₂ : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf₂ i s (g * u) = ψf₂ i s g)
      (_hψty₂ : ∀ i (s : ℂ), ψf₂ i s ∈ archCutSubmodule K tysK),
    ∃ (ιP : Type) (_instP : Fintype ιP)
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
      (_hφK : ∀ e s, IsArchKFinite K (φf e s)) (_hφsm : ∀ e s, IsKfSmooth K (φf e s))
      (_hφKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => φf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hφlev : ∀ e (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, φf e s (g * u) = φf e s g)
      (_hφty : ∀ e (s : ℂ), φf e s ∈ archCutSubmodule K tysK)
      (_hψlev : ∀ e (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf e s (g * u) = ψf e s g)
      (_hψty : ∀ e (s : ℂ), ψf e s ∈ archCutSubmodule K tysK)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹),
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₁ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, φf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) ∧
    (∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ₂ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g) := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμ _hν _hμic _hνic _hμc _hνc _hμν _hdist nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP₁ _ μP₁ νP₁ _hμ₁ _hν₁ _hμic₁ _hνic₁ _hμc₁ _hμν₁ rP₁ _hr₁ _hdist₁ ψf₁ _hψf₁ _hψjc₁ _hψhol₁ _hψK₁ _hψsm₁ _hψKu₁ _hνc₁ _hψdec₁ ψ₁ _hψ₁ _hψrep₁ em₁ τ₁ _hem₁ _hψlev₁ _hψty₁ ιP₂ _ μP₂ νP₂ _hμ₂ _hν₂ _hμic₂ _hνic₂ _hμc₂ _hμν₂ rP₂ _hr₂ _hdist₂ ψf₂ _hψf₂ _hψjc₂ _hψhol₂ _hψK₂ _hψsm₂ _hψKu₂ _hνc₂ _hψdec₂ ψ₂ _hψ₂ _hψrep₂ em₂ τ₂ _hem₂ _hψlev₂ _hψty₂
  classical
  have hαI : ∀ x, ((αm x : ℝˣ) : ℝ) = ideleNorm K x := fun _ => rfl

  have h1μ : ∀ i, ∀ z ∈ normOneIdeles K, μP₁ i z = μ (em₁ i) z := fun i z hz => by
    rw [(_hem₁ i).1]; exact mul_normPowChar_apply_of_mem _ _ hz
  have h1ν : ∀ i, ∀ z ∈ normOneIdeles K, νP₁ i z = ν (em₁ i) z := fun i z hz => by
    rw [(_hem₁ i).2]; exact mul_normPowChar_inv_apply_of_mem _ _ hz
  have h2μ : ∀ i, ∀ z ∈ normOneIdeles K, μP₂ i z = μ (em₂ i) z := fun i z hz => by
    rw [(_hem₂ i).1]; exact mul_normPowChar_apply_of_mem _ _ hz
  have h2ν : ∀ i, ∀ z ∈ normOneIdeles K, νP₂ i z = ν (em₂ i) z := fun i z hz => by
    rw [(_hem₂ i).2]; exact mul_normPowChar_inv_apply_of_mem _ _ hz

  have hsepE : ∀ e e' : ιE, (∀ z ∈ normOneIdeles K, μ e z = μ e' z ∧ ν e z = ν e' z) → e = e' := by
    intro e e' h
    by_contra hne
    obtain ⟨z, hz, hz'⟩ := _hdist e e' hne
    rcases hz' with h' | h'
    · exact h' (h z hz).1
    · exact h' (h z hz).2
  have hinj₁ : Function.Injective em₁ := by
    intro i j hij
    by_contra hne
    obtain ⟨z, hz, h⟩ := _hdist₁ i j hne
    rcases h with h | h
    · exact h (by rw [h1μ i z hz, h1μ j z hz, hij])
    · exact h (by rw [h1ν i z hz, h1ν j z hz, hij])
  have hinj₂ : Function.Injective em₂ := by
    intro i j hij
    by_contra hne
    obtain ⟨z, hz, h⟩ := _hdist₂ i j hne
    rcases h with h | h
    · exact h (by rw [h2μ i z hz, h2μ j z hz, hij])
    · exact h (by rw [h2ν i z hz, h2ν j z hz, hij])

  have hrr₂ : ∀ i', rP₂ (rP₂ i') = i' := by
    intro i'
    by_contra hne
    obtain ⟨z, -, h⟩ := _hdist₂ (rP₂ (rP₂ i')) i' hne
    rcases h with h | h
    · exact h (by rw [(_hr₂ (rP₂ i')).1, (_hr₂ i').2])
    · exact h (by rw [(_hr₂ (rP₂ i')).2, (_hr₂ i').1])

  have hswap : ∀ i i', em₂ i' = em₁ i → em₂ (rP₂ i') = em₁ (rP₁ i) := by
    intro i i' h
    apply hsepE
    intro z hz
    refine ⟨?_, ?_⟩
    · rw [← h2μ (rP₂ i') z hz, ← h1μ (rP₁ i) z hz, (_hr₂ i').1, (_hr₁ i).1, h2ν i' z hz, h1ν i z hz, h]
    · rw [← h2ν (rP₂ i') z hz, ← h1ν (rP₁ i) z hz, (_hr₂ i').2, (_hr₁ i).2, h2μ i' z hz, h1μ i z hz, h]
  have hout : ∀ i', (¬ ∃ i, em₁ i = em₂ i') → ¬ ∃ i, em₁ i = em₂ (rP₂ i') := by
    intro i' h' ⟨j, hj⟩
    have := hswap j (rP₂ i') hj.symm
    rw [hrr₂] at this
    exact h' ⟨rP₁ j, this.symm⟩

  let T := {i' : ιP₂ // ¬ ∃ i, em₁ i = em₂ i'}
  let μP : ιP₁ ⊕ T → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := Sum.elim μP₁ (fun t => μP₂ t.1)
  let νP : ιP₁ ⊕ T → ((AdeleRing (𝓞 K) K)ˣ →* ℂˣ) := Sum.elim νP₁ (fun t => νP₂ t.1)
  let rP : ιP₁ ⊕ T → ιP₁ ⊕ T := Sum.elim (fun i => Sum.inl (rP₁ i)) (fun t => Sum.inr ⟨rP₂ t.1, hout t.1 t.2⟩)
  let em : ιP₁ ⊕ T → ιE := Sum.elim em₁ (fun t => em₂ t.1)
  let τ : ιP₁ ⊕ T → ℝ := Sum.elim τ₁ (fun t => τ₂ t.1)
  let φf : ιP₁ ⊕ T → ℂ → AdelicGL2 (𝓞 K) K → ℂ := Sum.elim ψf₁ (fun _ => fun _ _ => 0)
  let ψf : ιP₁ ⊕ T → ℂ → AdelicGL2 (𝓞 K) K → ℂ :=
    Sum.elim (fun i => if h : ∃ i', em₂ i' = em₁ i then
        fun s g => ψf₂ h.choose (s + ((τ₁ i - τ₂ h.choose : ℝ) : ℂ) * Complex.I) g
      else fun _ _ => 0)
      (fun t => ψf₂ t.1)

  have hshiftF : ∀ (i : ιP₁) (i' : ιP₂), em₂ i' = em₁ i → ∀ s : ℂ,
      etaFst (μP₁ i) αm hαm s = etaFst (μP₂ i') αm hαm (s + ((τ₁ i - τ₂ i' : ℝ) : ℂ) * Complex.I) := by
    intro i i' h s
    rw [(_hem₁ i).1, (_hem₂ i').1, h, etaFst_mul_normPowChar' _ _ _ hαI, etaFst_mul_normPowChar' _ _ _ hαI]
    congr 1
    push_cast
    ring
  have hshiftS : ∀ (i : ιP₁) (i' : ιP₂), em₂ i' = em₁ i → ∀ s : ℂ,
      etaSnd (νP₁ i) αm hαm s = etaSnd (νP₂ i') αm hαm (s + ((τ₁ i - τ₂ i' : ℝ) : ℂ) * Complex.I) := by
    intro i i' h s
    rw [(_hem₁ i).2, (_hem₂ i').2, h, etaSnd_mul_normPowChar_inv' _ _ _ hαI, etaSnd_mul_normPowChar_inv' _ _ _ hαI]
    congr 1
    push_cast
    ring
  have hline : ∀ (σ' t Δ : ℝ),
      (σ' : ℂ) + (t : ℂ) * Complex.I + ((Δ : ℝ) : ℂ) * Complex.I = (σ' : ℂ) + ((t + Δ : ℝ) : ℂ) * Complex.I := by
    intro σ' t Δ
    push_cast
    ring
  refine ⟨ιP₁ ⊕ T, inferInstance, μP, νP, ?_, ?_, ?_, ?_, ?_, ?_, rP, ?_, ?_, φf, ψf,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, em, τ, ?_, ?_, ?_⟩

  · rintro (i | t)
    · exact _hμ₁ i
    · exact _hμ₂ t.1

  · rintro (i | t)
    · exact _hν₁ i
    · exact _hν₂ t.1

  · rintro (i | t)
    · exact _hμic₁ i
    · exact _hμic₂ t.1

  · rintro (i | t)
    · exact _hνic₁ i
    · exact _hνic₂ t.1

  · rintro (i | t)
    · exact _hμc₁ i
    · exact _hμc₂ t.1

  · rintro (i | t) z
    · exact _hμν₁ i z
    · exact _hμν₂ t.1 z

  · rintro (i | t)
    · exact _hr₁ i
    · exact _hr₂ t.1

  · rintro (i | ⟨i', hi'⟩) (j | ⟨j', hj'⟩) hne
    · have hij : i ≠ j := fun h => hne (by rw [h])
      exact _hdist₁ i j hij
    · have hcl : em₁ i ≠ em₂ j' := fun h => hj' ⟨i, h⟩
      obtain ⟨z, hz, h⟩ := _hdist (em₁ i) (em₂ j') hcl
      refine ⟨z, hz, ?_⟩
      show μP₁ i z ≠ μP₂ j' z ∨ νP₁ i z ≠ νP₂ j' z
      rw [h1μ i z hz, h2μ j' z hz, h1ν i z hz, h2ν j' z hz]
      exact h
    · have hcl : em₂ i' ≠ em₁ j := fun h => hi' ⟨j, h.symm⟩
      obtain ⟨z, hz, h⟩ := _hdist (em₂ i') (em₁ j) hcl
      refine ⟨z, hz, ?_⟩
      show μP₂ i' z ≠ μP₁ j z ∨ νP₂ i' z ≠ νP₁ j z
      rw [h2μ i' z hz, h1μ j z hz, h2ν i' z hz, h1ν j z hz]
      exact h
    · have hij : i' ≠ j' := fun h => hne (by subst h; rfl)
      exact _hdist₂ i' j' hij

  · rintro (i | t) s
    · exact _hψf₁ i s
    · exact isInducedSection_zero _ _

  · rintro (i | t) s
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · simp only [ψf, Sum.elim_inl, dif_pos h]
        show IsInducedSection (𝓞 K) K (etaFst (μP₁ i) αm hαm s) (etaSnd (νP₁ i) αm hαm s) _
        rw [hshiftF i h.choose h.choose_spec s, hshiftS i h.choose h.choose_spec s]
        exact _hψf₂ h.choose _
      · simp only [ψf, Sum.elim_inl, dif_neg h]
        exact isInducedSection_zero _ _
    · exact _hψf₂ t.1 s

  · rintro (i | t)
    · exact _hψjc₁ i
    · exact continuous_const

  · rintro (i | t)
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · simp only [ψf, Sum.elim_inl, dif_pos h]
        exact (_hψjc₂ h.choose).comp ((continuous_fst.add continuous_const).prodMk continuous_snd)
      · simp only [ψf, Sum.elim_inl, dif_neg h]
        exact continuous_const
    · exact _hψjc₂ t.1

  · rintro (i | t) g
    · exact _hψhol₁ i g
    · exact differentiable_const _

  · rintro (i | t) g
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · simp only [ψf, Sum.elim_inl, dif_pos h]
        exact (_hψhol₂ h.choose g).comp (differentiable_id.add_const _)
      · simp only [ψf, Sum.elim_inl, dif_neg h]
        exact differentiable_const _
    · exact _hψhol₂ t.1 g

  · rintro (i | t) s
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · simp only [ψf, Sum.elim_inl, dif_pos h]
        exact _hψK₂ h.choose _
      · simp only [ψf, Sum.elim_inl, dif_neg h]
        exact isArchKFinite_zero K
    · exact _hψK₂ t.1 s

  · rintro (i | t) s
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · simp only [ψf, Sum.elim_inl, dif_pos h]
        exact _hψsm₂ h.choose _
      · simp only [ψf, Sum.elim_inl, dif_neg h]
        exact isKfSmooth_zero K
    · exact _hψsm₂ t.1 s

  · rintro (i | t) w
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · obtain ⟨W, hW, hmem⟩ := _hψKu₂ h.choose w
        refine ⟨W, hW, fun s g => ?_⟩
        simp only [ψf, Sum.elim_inl, dif_pos h]
        exact hmem _ g
      · refine ⟨⊥, inferInstance, fun s g => ?_⟩
        simp only [ψf, Sum.elim_inl, dif_neg h, Submodule.mem_bot]
        rfl
    · exact _hψKu₂ t.1 w

  · rintro (i | t)
    · exact _hνc₁ i
    · exact _hνc₂ t.1

  · rintro (i | t) n σ₀ C hC
    · exact _hψdec₁ i n σ₀ C hC
    · refine ⟨0, integrable_zero _ _ _, ⟨0, fun _ => le_rfl⟩, fun σ' _ t g _ => ?_⟩
      simp [φf]

  · rintro (i | t) n σ₀ C hC
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · obtain ⟨m, hmi, ⟨B, hB⟩, hm⟩ := _hψdec₂ h.choose n σ₀ C hC
        have hD : (0 : ℝ) < (1 + |τ₁ i - τ₂ h.choose|) ^ n := by positivity
        refine ⟨fun t => (1 + |τ₁ i - τ₂ h.choose|) ^ n * m (t + (τ₁ i - τ₂ h.choose)),
          (hmi.comp_add_right _).const_mul _, ⟨(1 + |τ₁ i - τ₂ h.choose|) ^ n * B, fun t =>
            mul_le_mul_of_nonneg_left (hB _) hD.le⟩, fun σ' hσ' t g hg => ?_⟩
        simp only [ψf, Sum.elim_inl, dif_pos h]
        rw [hline]
        have hmt := hm σ' hσ' (t + (τ₁ i - τ₂ h.choose)) g hg
        calc (1 + |t|) ^ n * ‖ψf₂ h.choose ((σ' : ℂ) + ((t + (τ₁ i - τ₂ h.choose) : ℝ) : ℂ) * Complex.I) g‖
            ≤ ((1 + |τ₁ i - τ₂ h.choose|) * (1 + |t + (τ₁ i - τ₂ h.choose)|)) ^ n *
                ‖ψf₂ h.choose ((σ' : ℂ) + ((t + (τ₁ i - τ₂ h.choose) : ℝ) : ℂ) * Complex.I) g‖ :=
              mul_le_mul_of_nonneg_right (by gcongr; exact one_add_abs_le _ _) (norm_nonneg _)
          _ = (1 + |τ₁ i - τ₂ h.choose|) ^ n * ((1 + |t + (τ₁ i - τ₂ h.choose)|) ^ n *
                ‖ψf₂ h.choose ((σ' : ℂ) + ((t + (τ₁ i - τ₂ h.choose) : ℝ) : ℂ) * Complex.I) g‖) := by
              rw [mul_pow, mul_assoc]
          _ ≤ (1 + |τ₁ i - τ₂ h.choose|) ^ n * m (t + (τ₁ i - τ₂ h.choose)) :=
              mul_le_mul_of_nonneg_left hmt hD.le
      · refine ⟨0, integrable_zero _ _ _, ⟨0, fun _ => le_rfl⟩, fun σ' _ t g _ => ?_⟩
        simp [ψf, dif_neg h]
    · exact _hψdec₂ t.1 n σ₀ C hC

  · rintro (i | t) s
    · exact _hψK₁ i s
    · exact isArchKFinite_zero K

  · rintro (i | t) s
    · exact _hψsm₁ i s
    · exact isKfSmooth_zero K

  · rintro (i | t) w
    · exact _hψKu₁ i w
    · refine ⟨⊥, inferInstance, fun s g => ?_⟩
      simp only [φf, Sum.elim_inr, Submodule.mem_bot]
      rfl

  · rintro (i | t) s g u hu
    · exact _hψlev₁ i s g u hu
    · rfl

  · rintro (i | t) s
    · exact _hψty₁ i s
    · exact Submodule.zero_mem _

  · rintro (i | t) s g u hu
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · simp only [ψf, Sum.elim_inl, dif_pos h]
        exact _hψlev₂ h.choose _ g u hu
      · simp only [ψf, Sum.elim_inl, dif_neg h]
    · exact _hψlev₂ t.1 s g u hu

  · rintro (i | t) s
    · by_cases h : ∃ i', em₂ i' = em₁ i
      · simp only [ψf, Sum.elim_inl, dif_pos h]
        exact _hψty₂ h.choose _
      · simp only [ψf, Sum.elim_inl, dif_neg h]
        exact Submodule.zero_mem _
    · exact _hψty₂ t.1 s

  · rintro (i | t)
    · exact _hem₁ i
    · exact _hem₂ t.1

  · intro σ' g
    rw [Fintype.sum_sum_type]
    simp only [φf, Sum.elim_inl, Sum.elim_inr, integral_zero, mul_zero, Finset.sum_const_zero, add_zero]
    exact _hψrep₁ σ' g

  · intro σ' g
    rw [Fintype.sum_sum_type, _hψrep₂ σ' g]

    rw [← Fintype.sum_subtype_add_sum_subtype (fun i' : ιP₂ => ∃ i, em₁ i = em₂ i')
      (fun i' => (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₂ i' ((σ' : ℂ) + (t : ℂ) * Complex.I) g)]
    congr 1

    rw [← Fintype.sum_subtype_add_sum_subtype (fun i : ιP₁ => ∃ i', em₂ i' = em₁ i)
      (fun i => (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf (Sum.inl i) ((σ' : ℂ) + (t : ℂ) * Complex.I) g)]
    have hzero : ∑ i : {i : ιP₁ // ¬ ∃ i', em₂ i' = em₁ i},
        (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf (Sum.inl i.1) ((σ' : ℂ) + (t : ℂ) * Complex.I) g = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      simp only [ψf, Sum.elim_inl, dif_neg i.2, integral_zero, mul_zero]
    rw [hzero, add_zero]

    let E : {i : ιP₁ // ∃ i', em₂ i' = em₁ i} ≃ {i' : ιP₂ // ∃ i, em₁ i = em₂ i'} :=
      { toFun := fun x => ⟨x.2.choose, ⟨x.1, x.2.choose_spec.symm⟩⟩
        invFun := fun y => ⟨y.2.choose, ⟨y.1, y.2.choose_spec.symm⟩⟩
        left_inv := fun x => by
          apply Subtype.ext
          apply hinj₁

          have h1 : em₂ x.2.choose = em₁ x.1 := x.2.choose_spec
          have h2 := (⟨x.1, x.2.choose_spec.symm⟩ : ∃ i, em₁ i = em₂ x.2.choose).choose_spec
          exact h2.trans h1
        right_inv := fun y => by
          apply Subtype.ext
          apply hinj₂
          have h1 : em₁ y.2.choose = em₂ y.1 := y.2.choose_spec
          have h2 := (⟨y.1, y.2.choose_spec.symm⟩ : ∃ i', em₂ i' = em₁ y.2.choose).choose_spec
          exact h2.trans h1 }
    refine Fintype.sum_equiv E.symm _ _ fun y => ?_

    obtain ⟨i', hi'⟩ := y
    have hx : ∃ j, em₂ j = em₁ hi'.choose := ⟨i', hi'.choose_spec.symm⟩
    have hch : hx.choose = i' := hinj₂ (hx.choose_spec.trans hi'.choose_spec)
    show (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf₂ i' ((σ' : ℂ) + (t : ℂ) * Complex.I) g =
      (((4 * Real.pi)⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, ψf (Sum.inl hi'.choose) ((σ' : ℂ) + (t : ℂ) * Complex.I) g
    simp only [ψf, Sum.elim_inl, dif_pos hx]
    congr 1
    simp_rw [hline]
    rw [integral_add_right_eq_self (fun t : ℝ => ψf₂ hx.choose ((σ' : ℂ) + (t : ℂ) * Complex.I) g)]
    rw [hch]

end S_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_exists_common_matched_paleyWiener_family_eq_sum_integral_of_matched_paleyWiener_of_matched_paleyWiener (solution)
