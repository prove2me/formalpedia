-- Prove2me | solution 1 for AutomorphicForm.differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/d20a4d94-54ba-5a1f-a518-c0efcadda99a

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal

attribute [local instance] NumberField.AdelicHaar.glBorel

set_option maxHeartbeats 4000000

open scoped Topology

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

noncomputable section

namespace Ws48
namespace Axis
open Filter

theorem integral_mul_conj_of_orthonormal {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (e : Fin n → X → ℂ) (hint : ∀ i j, Integrable (fun x => e i x * conj (e j x)) μ)
    (hon : ∀ i j, ∫ x, e i x * conj (e j x) ∂μ = if i = j then 1 else 0)
    (c : Fin n → ℂ) (w : X → ℂ) (hw : ∀ x, w x = ∑ j, c j * e j x) :
    (∀ j, ∫ x, w x * conj (e j x) ∂μ = c j) ∧
    ∫ x, w x * conj (w x) ∂μ = ∑ j, (∫ x, w x * conj (e j x) ∂μ) * conj (∫ x, w x * conj (e j x) ∂μ) := by
  have hwj : ∀ j, (fun x => w x * conj (e j x)) = fun x => ∑ i, c i * (e i x * conj (e j x)) := by
    intro j; funext x
    rw [hw x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hintj : ∀ j, Integrable (fun x => w x * conj (e j x)) μ := by
    intro j; rw [hwj j]
    exact integrable_finsetSum _ fun i _ => (hint i j).const_mul (c i)
  have hcoef : ∀ j, ∫ x, w x * conj (e j x) ∂μ = c j := by
    intro j
    rw [hwj j, integral_finsetSum _ (fun i _ => (hint i j).const_mul (c i))]
    simp_rw [integral_const_mul, hon]
    simp
  refine ⟨hcoef, ?_⟩
  have hww : (fun x => w x * conj (w x)) = fun x => ∑ j, conj (c j) * (w x * conj (e j x)) := by
    funext x
    have : conj (w x) = ∑ j, conj (c j) * conj (e j x) := by
      rw [hw x, map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_mul]
    rw [this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hww, integral_finsetSum _ (fun j _ => (hintj j).const_mul (conj (c j)))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hcoef j, mul_comm]

section Eta
open AutomorphicForm NumberField.TateGlobal
variable (K : Type) [Field K] [NumberField K]

theorem cpowChar_mul_cpowChar (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (a b : ℂ) :
    cpowChar α hα a * cpowChar α hα b = cpowChar α hα (a + b) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.mul_apply, Units.val_mul, cpowChar_apply_val, cpowChar_apply_val, cpowChar_apply_val,
    ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hα x).ne')]

theorem cpowChar_inv (α : (AdeleRing (𝓞 K) K)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ)) (a : ℂ) :
    (cpowChar α hα a)⁻¹ = cpowChar α hα (-a) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, cpowChar_apply_val, cpowChar_apply_val, Complex.cpow_neg]

theorem normPowChar_eq_cpowChar (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ))) (τ : ℝ) :
    normPowChar K τ = cpowChar (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (Complex.I * τ) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [coe_normPowChar_apply, cpowChar_apply_val]
  rfl

theorem etaFst_mul_normPowChar (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)))
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaFst (μ * normPowChar K τ) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα s =
    etaFst μ (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [etaFst_apply, MonoidHom.mul_apply, Units.val_mul, coe_normPowChar_apply, cpowChar_apply_val]
  have hx : ((((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hα x).ne'
  have hI : ((ideleNorm K x : ℝ) : ℂ) = (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ) := rfl
  rw [hI, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; ring

theorem etaSnd_mul_normPowChar_inv (hα : ∀ x, 0 < (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ)))
    (ν : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (τ : ℝ) (s : ℂ) :
    etaSnd (ν * (normPowChar K τ)⁻¹) (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα s =
    etaSnd ν (((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits) hα (s + (τ : ℂ) * Complex.I) := by
  refine MonoidHom.ext fun x => Units.ext ?_
  simp only [etaSnd_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
    coe_normPowChar_apply, cpowChar_apply_val]
  have hx : ((((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hα x).ne'
  have hI : ((ideleNorm K x : ℝ) : ℂ) = (((((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K))).toHomUnits x : ℝˣ) : ℝ) : ℂ) := rfl
  rw [hI, ← Complex.cpow_neg, mul_assoc, ← Complex.cpow_add _ _ hx]
  congr 2; ring

end Eta

end Ws48.Axis

open AutomorphicForm

namespace W2

theorem differentiable_integral_mul
    (K : Type) [Field K] [NumberField K]
    (F : ℂ → AdelicGL2 (𝓞 K) K → ℂ) (hFjc : Continuous fun p : ℂ × AdelicGL2 (𝓞 K) K => F p.1 p.2)
    (hFhol : ∀ g : AdelicGL2 (𝓞 K) K, Differentiable ℂ (fun s => F s g))
    (w : adelicMaximalCompact K → ℂ) (hw : Continuous w) :
    Differentiable ℂ (fun s => ∫ k, F s (k : AdelicGL2 (𝓞 K) K) * w k ∂(maximalCompactHaar K)) := by
  have hcont : ∀ s, Continuous (F s) := fun s => hFjc.comp (continuous_const.prodMk continuous_id)
  intro s₀
  have hcont2 : Continuous (fun p : ℂ × adelicMaximalCompact K => F p.1 (p.2 : AdelicGL2 (𝓞 K) K)) :=
    hFjc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  obtain ⟨M, hM⟩ := ((isCompact_closedBall s₀ 2).prod isCompact_univ).bddAbove_image hcont2.norm.continuousOn
  have hMb : ∀ (z : ℂ), z ∈ Metric.closedBall s₀ 2 → ∀ k : adelicMaximalCompact K, ‖F z (k : AdelicGL2 (𝓞 K) K)‖ ≤ M :=
    fun z hz k => hM (Set.mem_image_of_mem _ (Set.mk_mem_prod hz (Set.mem_univ k)))
  set F' : ℂ → adelicMaximalCompact K → ℂ := fun s k => deriv (fun z => F z (k : AdelicGL2 (𝓞 K) K)) s * w k with hF'
  have hderiv : ∀ (k : adelicMaximalCompact K) (s : ℂ),
      HasDerivAt (fun z => F z (k : AdelicGL2 (𝓞 K) K) * w k) (F' s k) s := fun k s =>
    ((hFhol (k : AdelicGL2 (𝓞 K) K)).differentiableAt.hasDerivAt).mul_const (w k)
  have hbound : ∀ (k : adelicMaximalCompact K), ∀ s ∈ Metric.ball s₀ 1, ‖F' s k‖ ≤ M * ‖w k‖ := by
    intro k s hs
    have hd : ‖deriv (fun z => F z (k : AdelicGL2 (𝓞 K) K)) s‖ ≤ M / 1 := by
      refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le zero_lt_one
        (hFhol (k : AdelicGL2 (𝓞 K) K)).diffContOnCl (fun z hz => hMb z ?_ k)
      rw [Metric.mem_closedBall]
      have h1 : dist z s = 1 := hz
      have h2 : dist s s₀ < 1 := hs
      linarith [dist_triangle z s s₀]
    rw [div_one] at hd
    show ‖deriv (fun z => F z (k : AdelicGL2 (𝓞 K) K)) s * w k‖ ≤ M * ‖w k‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  have hF'm : AEStronglyMeasurable (F' s₀) (maximalCompactHaar K) := by
    refine (stronglyMeasurable_of_tendsto (u := Filter.atTop)
      (f := fun (n : ℕ) (k : adelicMaximalCompact K) =>
        slope (fun z => F z (k : AdelicGL2 (𝓞 K) K) * w k) s₀ (s₀ + ((n : ℂ) + 1)⁻¹))
      (fun n => ?_) ?_).aestronglyMeasurable
    · refine Continuous.stronglyMeasurable ?_
      simp only [slope, vsub_eq_sub]
      refine continuous_const.fun_smul ((((hcont _).comp continuous_subtype_val).fun_mul hw).fun_sub
        (((hcont _).comp continuous_subtype_val).fun_mul hw))
    · rw [tendsto_pi_nhds]
      intro k
      have ht : Filter.Tendsto (fun n : ℕ => s₀ + ((n : ℂ) + 1)⁻¹) Filter.atTop (nhdsWithin s₀ {s₀}ᶜ) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall fun n => ?_⟩
        · have h0 : Filter.Tendsto (fun n : ℕ => ((n : ℂ) + 1)⁻¹) Filter.atTop (nhds 0) := by
            have h := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
            rw [Complex.ofReal_zero] at h
            refine (Filter.tendsto_congr (fun n => ?_)).mp h
            simp only [Function.comp_apply, one_div, Complex.ofReal_inv, Complex.ofReal_add,
              Complex.ofReal_natCast, Complex.ofReal_one]
          simpa using tendsto_const_nhds.add h0
        · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, add_eq_left, inv_eq_zero]
          exact Nat.cast_add_one_ne_zero n
      exact ((hasDerivAt_iff_tendsto_slope.mp (hderiv k s₀)).comp ht)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := maximalCompactHaar K)
    (F := fun s k => F s (k : AdelicGL2 (𝓞 K) K) * w k) (x₀ := s₀)
    (bound := fun k => M * ‖w k‖) (Metric.ball_mem_nhds s₀ zero_lt_one)
    (Filter.Eventually.of_forall fun s =>
      ((((hcont s).comp continuous_subtype_val).mul hw).aestronglyMeasurable))
    ((((hcont s₀).comp continuous_subtype_val).mul hw).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    hF'm (Filter.Eventually.of_forall hbound)
    ((continuous_const.mul hw.norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (Filter.Eventually.of_forall fun k s _ => hderiv k s)
  exact key.2.differentiableAt

end W2

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
      (ψf : ιP → ℂ → AdelicGL2 (𝓞 K) K → ℂ)
      (_hψf : ∀ e s, IsInducedSection (𝓞 K) K (etaFst (μP e) αm hαm s) (etaSnd (νP e) αm hαm s) (ψf e s))
      (_hψjc : ∀ e, Continuous (fun p : ℂ × AdelicGL2 (𝓞 K) K => ψf e p.1 p.2))
      (_hψhol : ∀ e g, Differentiable ℂ (fun s => ψf e s g))
      (_hψK : ∀ e s, IsArchKFinite K (ψf e s)) (_hψsm : ∀ e s, IsKfSmooth K (ψf e s))
      (_hψKu : ∀ (e : ιP) (w : InfinitePlace K), ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup K w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
          (fun k : ↥(archRowIsometrySubgroup K w) => ψf e s (g * (k : AdelicGL2 (𝓞 K) K))) ∈ W)
      (_hνc : ∀ e, Continuous fun x : (AdeleRing (𝓞 K) K)ˣ => ((νP e x : ℂˣ) : ℂ))
      (_hψdec : ∀ (e : ιP) (n : ℕ) (σ₀ : ℝ) (C : Set (AdelicGL2 (𝓞 K) K)), IsCompact C →
        ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧ ∀ σ' : ℝ, |σ'| ≤ σ₀ →
          ∀ (t : ℝ), ∀ g ∈ C, (1 + |t|) ^ n * ‖ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g‖ ≤ m t)
      (ψ : AdelicGL2 (𝓞 K) K → ℂ)
      (_hψ : AutomorphicForm.IsSlabProfile K
        (productionPinsOf K (AutomorphicForm.canonicalTruncationDomain K α β)
            (fun M => principalLevel (𝓞 K) K M ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
            (adelicBox K)).Z ξK ψ)
      (_hψrep : ∀ (σ' : ℝ) (g : AdelicGL2 (𝓞 K) K),
        ψ g = ∑ e, (((4 * Real.pi)⁻¹ : ℝ) : ℂ) *
          ∫ t : ℝ, ψf e ((σ' : ℂ) + (t : ℂ) * Complex.I) g)
      (em : ιP → ιE) (τ : ιP → ℝ)
      (_hem : ∀ i : ιP, μP i = μ (em i) * NumberField.TateGlobal.normPowChar K (τ i) ∧
        νP i = ν (em i) * (NumberField.TateGlobal.normPowChar K (τ i))⁻¹)
      (_hψlev : ∀ i (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
        ∀ u ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ψf i s (g * u) = ψf i s g)
      (_hψty : ∀ i (s : ℂ), ψf i s ∈ archCutSubmodule K tysK)
      (i : ιP),
    (∀ j : Fin (nE (em i)), Differentiable ℂ (fun s : ℂ =>
        ∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K))) ∧
    (∀ (j : Fin (nE (em i))) (n : ℕ) (σ₀ : ℝ), ∃ m : ℝ → ℝ, Integrable m ∧ (∃ B : ℝ, ∀ t, m t ≤ B) ∧
        ∀ σ' : ℝ, |σ'| ≤ σ₀ → ∀ t : ℝ,
          (1 + |t|) ^ n * ‖∫ k, ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) *
              conj (φE (em i) j ((σ' : ℂ) + (t : ℂ) * Complex.I + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖ ≤ m t) ∧
    ∀ (s : ℂ) (g : AdelicGL2 (𝓞 K) K),
      ψf i s g = ∑ j : Fin (nE (em i)),
        (∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) *
          φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) g := by
  intro αm hαm ι b cls hb hbn hbo hbs hbc ιE _ μ ν _hμE _hνE _hμicE _hνicE _hμcE _hνcE _hμν _hdistE nE φE _hφE _hφEK _hφEf _hφEjc _hφEhol _hφEKu _hφEflat _hφElev _hφEty _hφEon _hφEspan _hpairs OE EE NE _hEE ιP _ μP νP _hμP _hνP _hμicP _hνicP _hμcP _hμνP rP _hr _hdistP ψf _hψf _hψjc _hψhol _hψK _hψsm _hψKu _hνcP _hψdec ψ _hψ _hψrep em τ _hem _hψlev _hψty i
  letI := adeleBorel (𝓞 K) K
  haveI := NumberField.AdelicHaar.borelSpace_adeleBorel (𝓞 K) K
  have hφc : ∀ (e₀ : ιE) (j' : Fin (nE e₀)) (s : ℂ), Continuous fun k : adelicMaximalCompact K => φE e₀ j' s (k : AdelicGL2 (𝓞 K) K) :=
    fun e₀ j' s => ((_hφEjc e₀ j').comp (Continuous.prodMk continuous_const continuous_id)).comp continuous_subtype_val
  have hψcont : ∀ s, Continuous (ψf i s) := fun s => (_hψjc i).comp (Continuous.prodMk continuous_const continuous_id)

  set c : Fin (nE (em i)) → ℂ → ℂ := fun j s =>
    ∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) with hcdef
  have hc0' : ∀ j s, (∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)) =
      ∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) := by
    intro j s
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j (s + ((τ i : ℝ) : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)) =
      ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))
    rw [_hφEflat (em i) j _ k]
  have hc0 : ∀ j s, c j s = ∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
    fun j s => hc0' j s

  have ha : ∀ j, Differentiable ℂ (c j) := by
    intro j
    have : c j = fun s => ∫ k, ψf i s (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K) :=
      funext (hc0 j)
    rw [this]
    exact W2.differentiable_integral_mul K (ψf i) (_hψjc i) (_hψhol i)
      (fun k => conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))) (Complex.continuous_conj.comp (hφc (em i) j 0))
  refine ⟨ha, fun j n σ₀ => ?_, fun s g => ?_⟩
  ·
    obtain ⟨m, hmi, ⟨B, hB⟩, hm⟩ := _hψdec i n σ₀ (adelicMaximalCompact K : Set (AdelicGL2 (𝓞 K) K)) (isCompact_adelicMaximalCompact K)
    set A : ℝ := ∫ k, ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) with hA
    have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
    refine ⟨fun t => m t * A, hmi.mul_const A, ⟨B * A, fun t => mul_le_mul_of_nonneg_right (hB t) hA0⟩, ?_⟩
    intro σ' hσ' t
    have hmt : 0 ≤ m t := by
      obtain ⟨k₀⟩ := (inferInstance : Nonempty (adelicMaximalCompact K))
      have := hm σ' hσ' t (k₀ : AdelicGL2 (𝓞 K) K) k₀.2
      exact le_trans (by positivity) this
    rw [hc0' j]
    have hint : Integrable (fun k : adelicMaximalCompact K => m t * ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖) (maximalCompactHaar K) :=
      (continuous_const.mul (hφc (em i) j 0).norm).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc (1 + |t|) ^ n * ‖∫ k, ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)) ∂(maximalCompactHaar K)‖
        ≤ (1 + |t|) ^ n * ∫ k, ‖ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))‖ ∂(maximalCompactHaar K) :=
          mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
      _ = ∫ k, (1 + |t|) ^ n * ‖ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ * ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          show (1 + |t|) ^ n * ‖ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K))‖ =
            (1 + |t|) ^ n * ‖ψf i ((σ' : ℂ) + (t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K)‖ * ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖
          rw [norm_mul, RCLike.norm_conj, mul_assoc]
      _ ≤ ∫ k, m t * ‖φE (em i) j 0 (k : AdelicGL2 (𝓞 K) K)‖ ∂(maximalCompactHaar K) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => by positivity) hint
            (Filter.Eventually.of_forall fun k => ?_)
          exact mul_le_mul_of_nonneg_right (hm σ' hσ' t (k : AdelicGL2 (𝓞 K) K) k.2) (norm_nonneg _)
      _ = m t * A := integral_const_mul _ _
  ·
    have haxis : ∀ (t : ℝ) (g : AdelicGL2 (𝓞 K) K), ψf i ((t : ℂ) * Complex.I) g =
        ∑ j : Fin (nE (em i)), c j ((t : ℂ) * Complex.I) * φE (em i) j ((t : ℂ) * Complex.I + ((τ i : ℝ) : ℂ) * Complex.I) g := by
      intro t g
      have e3 : (t : ℂ) * Complex.I + ((τ i : ℝ) : ℂ) * Complex.I = (((t + τ i : ℝ) : ℂ)) * Complex.I := by push_cast; ring
      have hψind : IsInducedSection (𝓞 K) K (etaFst (μ (em i)) αm hαm ((((t + τ i : ℝ) : ℂ)) * Complex.I))
          (etaSnd (ν (em i)) αm hαm ((((t + τ i : ℝ) : ℂ)) * Complex.I)) (ψf i ((t : ℂ) * Complex.I)) := by
        have h := _hψf i ((t : ℂ) * Complex.I)
        rw [(_hem i).1, (_hem i).2, Ws48.Axis.etaFst_mul_normPowChar K hαm,
          Ws48.Axis.etaSnd_mul_normPowChar_inv K hαm] at h
        rwa [e3] at h
      have hspan := _hφEspan (em i) (t + τ i) _ hψind (hψcont _) (_hψK i _) (fun g u hu => _hψlev i _ g u hu) (_hψty i _)
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hspan
      have hψs : ∀ x : AdelicGL2 (𝓞 K) K, ψf i ((t : ℂ) * Complex.I) x = ∑ j', d j' * φE (em i) j' ((((t + τ i : ℝ) : ℂ)) * Complex.I) x := by
        intro x
        have := congrFun hd x
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
        exact this.symm
      have hψ0 : ∀ k : adelicMaximalCompact K, ψf i ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 K) K) = ∑ j', d j' * φE (em i) j' 0 (k : AdelicGL2 (𝓞 K) K) := by
        intro k
        rw [hψs k]
        exact Finset.sum_congr rfl fun j' _ => by rw [_hφEflat (em i) j' _ k]
      have hint0 : ∀ i' j', Integrable (fun k : adelicMaximalCompact K => φE (em i) i' 0 (k : AdelicGL2 (𝓞 K) K) * conj (φE (em i) j' 0 (k : AdelicGL2 (𝓞 K) K))) (maximalCompactHaar K) :=
        fun i' j' => ((hφc (em i) i' 0).mul (Complex.continuous_conj.comp (hφc (em i) j' 0))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      obtain ⟨hcoef, -⟩ := Ws48.Axis.integral_mul_conj_of_orthonormal (maximalCompactHaar K)
        (fun j' (k : adelicMaximalCompact K) => φE (em i) j' 0 (k : AdelicGL2 (𝓞 K) K)) hint0 (_hφEon (em i)) d _ hψ0
      have hcd : ∀ j', c j' ((t : ℂ) * Complex.I) = d j' := fun j' => by rw [hc0 j', hcoef j']
      rw [hψs g]
      refine Finset.sum_congr rfl fun j' _ => ?_
      rw [hcd j', e3]

    set D : ℂ → ℂ := fun z => ψf i z g - ∑ j : Fin (nE (em i)), c j z * φE (em i) j (z + ((τ i : ℝ) : ℂ) * Complex.I) g with hD
    have hDd : Differentiable ℂ D :=
      (_hψhol i g).sub (Differentiable.fun_sum fun j _ => (ha j).mul ((_hφEhol (em i) j g).comp (differentiable_id.add_const _)))
    have hDan : AnalyticOnNhd ℂ D Set.univ := hDd.differentiableOn.analyticOnNhd isOpen_univ
    have hDaxis : ∀ t : ℝ, D ((t : ℂ) * Complex.I) = 0 := fun t => by
      show ψf i ((t : ℂ) * Complex.I) g - ∑ j : Fin (nE (em i)), c j ((t : ℂ) * Complex.I) * φE (em i) j ((t : ℂ) * Complex.I + ((τ i : ℝ) : ℂ) * Complex.I) g = 0
      rw [haxis t g, sub_self]
    have hfreq : ∃ᶠ z in 𝓝[≠] (0:ℂ), D z = 0 := by
      rw [Filter.frequently_iff]
      intro U hU
      obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hU
      refine ⟨(((ε / 2 : ℝ)) : ℂ) * Complex.I, hsub ⟨?_, ?_⟩, hDaxis (ε / 2)⟩
      · rw [Metric.mem_ball, dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hε)]
        exact half_lt_self hε
      · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (half_pos hε).ne') Complex.I_ne_zero
    have hzero := hDan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ (0:ℂ)) hfreq
    have hs := hzero (Set.mem_univ s)
    simp only [hD, Pi.zero_apply, sub_eq_zero] at hs
    simpa only [hcdef] using hs

end
end S_AutomorphicForm_differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener
end P2MW
export P2MW.S_AutomorphicForm_differentiable_inner_and_decay_and_eq_sum_inner_mul_flat_orthonormal_of_matched_paleyWiener (solution)
