-- Prove2me | solution 1 for AutomorphicForm.continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/b5c22585-7f20-53a8-ab14-4f1e87c286d3

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
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain
open scoped ComplexConjugate NNReal Classical

attribute [local instance] NumberField.AdelicHaar.glBorel

attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Ws31
namespace AxisReg

open MeasureTheory Filter Topology Complex Metric
open scoped ComplexConjugate

section Generic

variable {𝕂 : Type*} [TopologicalSpace 𝕂] [MeasurableSpace 𝕂] [OpensMeasurableSpace 𝕂] [CompactSpace 𝕂]
  (μ : Measure 𝕂) [IsFiniteMeasure μ]

theorem dist_mul_I (t t₀ : ℝ) : dist ((t : ℂ) * I) ((t₀ : ℂ) * I) = |t - t₀| := by
  rw [dist_eq_norm, ← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

omit μ in

theorem exists_local_bound (O : Set ℂ) (hO : IsOpen O) (haxis : {s : ℂ | s.re = 0} ⊆ O)
    (N : ℂ → 𝕂 → ℂ) (hNa : ∀ k, AnalyticOnNhd ℂ (fun s => N s k) O)
    (hNc : ContinuousOn (fun p : ℂ × 𝕂 => N p.1 p.2) (O ×ˢ Set.univ)) (t₀ : ℝ) :
    ∃ M ε : ℝ, 0 < ε ∧ 0 ≤ M ∧ ∀ t : ℝ, |t - t₀| < ε → ∀ k : 𝕂,
      ‖N ((t : ℂ) * I) k‖ ≤ M ∧ ‖deriv (fun s => N s k) ((t : ℂ) * I)‖ ≤ M := by
  have hz₀ : ((t₀ : ℂ) * I) ∈ O := haxis (by simp)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO _ hz₀
  set C : Set (ℂ × 𝕂) := Metric.closedBall ((t₀ : ℂ) * I) (r / 2) ×ˢ Set.univ with hC
  have hCc : IsCompact C := (isCompact_closedBall _ _).prod isCompact_univ
  have hcb : Metric.closedBall ((t₀ : ℂ) * I) (r / 2) ⊆ O :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hCsub : C ⊆ O ×ˢ Set.univ := Set.prod_mono hcb le_rfl
  obtain ⟨M₀, hM₀⟩ := hCc.exists_bound_of_continuousOn (hNc.mono hCsub)
  have hM₀' : ∀ z, z ∈ Metric.closedBall ((t₀ : ℂ) * I) (r / 2) → ∀ k, ‖N z k‖ ≤ max M₀ 0 :=
    fun z hz k => (hM₀ (z, k) ⟨hz, Set.mem_univ _⟩).trans (le_max_left _ _)
  refine ⟨max M₀ 0 * (1 + (r / 4)⁻¹), r / 4, by positivity, by positivity, ?_⟩
  intro t ht k
  have hzt : dist ((t : ℂ) * I) ((t₀ : ℂ) * I) < r / 4 := by rw [dist_mul_I]; exact ht
  have hM0 : 0 ≤ max M₀ 0 := le_max_right _ _
  have hge : max M₀ 0 ≤ max M₀ 0 * (1 + (r / 4)⁻¹) :=
    le_mul_of_one_le_right hM0 (le_add_of_nonneg_right (by positivity))
  constructor
  · exact (hM₀' _ (Metric.mem_closedBall.mpr (by linarith [hzt.le])) k).trans hge
  ·
    have hsub : Metric.closedBall ((t : ℂ) * I) (r / 4) ⊆ Metric.closedBall ((t₀ : ℂ) * I) (r / 2) := by
      intro z hz
      rw [Metric.mem_closedBall] at hz ⊢
      linarith [dist_triangle z ((t : ℂ) * I) ((t₀ : ℂ) * I), hzt.le]
    have hd : DiffContOnCl ℂ (fun s => N s k) (Metric.ball ((t : ℂ) * I) (r / 4)) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball _ (by positivity)]
      exact (hNa k).differentiableOn.mono (hsub.trans hcb)
    have hC : ∀ z ∈ Metric.sphere ((t : ℂ) * I) (r / 4), ‖N z k‖ ≤ max M₀ 0 :=
      fun z hz => hM₀' z (hsub (Metric.sphere_subset_closedBall hz)) k
    have h := norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity) hd hC
    calc ‖deriv (fun s => N s k) ((t : ℂ) * I)‖ ≤ max M₀ 0 / (r / 4) := h
      _ = max M₀ 0 * (r / 4)⁻¹ := div_eq_mul_inv _ _
      _ ≤ max M₀ 0 * (1 + (r / 4)⁻¹) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) hM0

omit μ in

theorem continuous_slice (O : Set ℂ) (N : ℂ → 𝕂 → ℂ)
    (hNc : ContinuousOn (fun p : ℂ × 𝕂 => N p.1 p.2) (O ×ˢ Set.univ)) (w : ℂ) (hw : w ∈ O) :
    Continuous (fun k : 𝕂 => N w k) :=
  hNc.comp_continuous (continuous_const.prodMk continuous_id) (fun k => ⟨hw, Set.mem_univ _⟩)

omit μ in

theorem continuous_axis (O : Set ℂ) (haxis : {s : ℂ | s.re = 0} ⊆ O)
    (N : ℂ → 𝕂 → ℂ) (hNa : ∀ k, AnalyticOnNhd ℂ (fun s => N s k) O) (k : 𝕂) :
    Continuous (fun t : ℝ => N ((t : ℂ) * I) k) ∧
    Continuous (fun t : ℝ => deriv (fun s => N s k) ((t : ℂ) * I)) := by
  have hm : ∀ t : ℝ, ((t : ℂ) * I) ∈ O := fun t => haxis (by simp)
  have hc : Continuous (fun t : ℝ => (t : ℂ) * I) := by fun_prop
  exact ⟨(hNa k).continuousOn.comp_continuous hc hm, (hNa k).deriv.continuousOn.comp_continuous hc hm⟩

omit μ in

theorem measurable_deriv_slice (O : Set ℂ) (hO : IsOpen O) (N : ℂ → 𝕂 → ℂ)
    (hNa : ∀ k, AnalyticOnNhd ℂ (fun s => N s k) O)
    (hNc : ContinuousOn (fun p : ℂ × 𝕂 => N p.1 p.2) (O ×ˢ Set.univ)) (w : ℂ) (hw : w ∈ O) :
    Measurable (fun k : 𝕂 => deriv (fun s => N s k) w) := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hO w hw

  set h : ℕ → ℝ := fun n => ρ / ((n : ℝ) + 2) with hh
  have hpos : ∀ n, 0 < h n := fun n => by simp only [hh]; positivity
  have hlt : ∀ n, h n < ρ := fun n => by
    simp only [hh]; rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hmem : ∀ n, w + (h n : ℂ) ∈ O := fun n => hball (by
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos n)]
    exact hlt n)
  have hten : Tendsto (fun n => ((h n : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto h atTop (𝓝 0) := by
        simp only [hh]
        refine Tendsto.div_atTop tendsto_const_nhds ?_
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp this
      rw [Complex.ofReal_zero] at h2
      exact h2
    · exact Eventually.of_forall fun n => by
        rw [Set.mem_compl_singleton_iff]; exact Complex.ofReal_ne_zero.mpr (hpos n).ne'
  have hlim : ∀ k, Tendsto (fun n : ℕ => ((h n : ℝ) : ℂ)⁻¹ • (N (w + (h n : ℝ)) k - N w k)) atTop
      (𝓝 (deriv (fun s => N s k) w)) := by
    intro k
    have hd : HasDerivAt (fun s => N s k) (deriv (fun s => N s k) w) w :=
      (((hNa k).differentiableOn.differentiableAt (hO.mem_nhds hw))).hasDerivAt
    exact hd.tendsto_slope_zero.comp hten
  refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.mpr hlim)
  exact (((continuous_slice O N hNc _ (hmem n)).sub (continuous_slice O N hNc w hw)).const_smul
    (((h n : ℝ) : ℂ)⁻¹)).measurable

theorem continuous_integral_of_locBdd (f : ℝ → 𝕂 → ℂ) (hm : ∀ t, AEStronglyMeasurable (f t) μ)
    (hc : ∀ k, Continuous (fun t => f t k))
    (hb : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖f t k‖ ≤ M) :
    Continuous (fun t => ∫ k, f t k ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  obtain ⟨M, ε, hε, hM⟩ := hb t₀
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall hm
  · have : Metric.ball t₀ ε ∈ 𝓝 t₀ := Metric.ball_mem_nhds _ hε
    filter_upwards [this] with t ht
    exact Eventually.of_forall (hM t (by rwa [Metric.mem_ball, Real.dist_eq] at ht))
  · exact integrable_const M
  · exact Eventually.of_forall (fun k => (hc k).continuousAt)

theorem hasDerivAt_integral_of_locBdd (f f' : ℝ → 𝕂 → ℂ) (hm : ∀ t, AEStronglyMeasurable (f t) μ)
    (hm' : ∀ t, AEStronglyMeasurable (f' t) μ)
    (hbf : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖f t k‖ ≤ M)
    (hb : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖f' t k‖ ≤ M)
    (hd : ∀ t k, HasDerivAt (fun x => f x k) (f' t k) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ k, f t k ∂μ) (∫ k, f' t₀ k ∂μ) t₀ := by
  obtain ⟨M, ε, hε, hM⟩ := hb t₀
  obtain ⟨M₁, ε₁, hε₁, hM₁⟩ := hbf t₀
  have hint : Integrable (f t₀) μ :=
    (integrable_const M₁).mono' (hm t₀) (Eventually.of_forall fun k => hM₁ t₀ (by simp [hε₁]) k)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds t₀ hε) (Eventually.of_forall hm) hint
    (hm' t₀) (Eventually.of_forall fun k t ht => hM t (by rwa [Metric.mem_ball, Real.dist_eq] at ht) k)
    (integrable_const M) (Eventually.of_forall fun k t _ => hd t k)).2

theorem norm_integral_mul_conj_le (f g : 𝕂 → ℂ) (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (Cf Cg : ℝ) (hbf : ∀ k, ‖f k‖ ≤ Cf) (hbg : ∀ k, ‖g k‖ ≤ Cg) :
    ‖∫ k, f k * conj (g k) ∂μ‖ ≤ Real.sqrt (∫ k, ‖f k‖ ^ 2 ∂μ) * Real.sqrt (∫ k, ‖g k‖ ^ 2 ∂μ) := by
  have h1 : ‖∫ k, f k * conj (g k) ∂μ‖ ≤ ∫ k, ‖f k‖ * ‖g k‖ ∂μ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1; funext k; rw [norm_mul, Complex.norm_conj]
  have hF : MemLp (fun k => ‖f k‖) (ENNReal.ofReal 2) μ :=
    (memLp_top_of_bound hf.norm Cf (Eventually.of_forall fun k => by rw [norm_norm]; exact hbf k)).mono_exponent le_top
  have hG : MemLp (fun k => ‖g k‖) (ENNReal.ofReal 2) μ :=
    (memLp_top_of_bound hg.norm Cg (Eventually.of_forall fun k => by rw [norm_norm]; exact hbg k)).mono_exponent le_top
  have h2 := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall fun k => norm_nonneg (f k)) (Eventually.of_forall fun k => norm_nonneg (g k)) hF hG
  simp only [Real.rpow_two] at h2
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h1.trans h2

theorem exists_bound_of_continuous (f : 𝕂 → ℂ) (hf : Continuous f) : ∃ C : ℝ, ∀ k, ‖f k‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun k => hC k (Set.mem_univ k)⟩

omit μ in

theorem hasDerivAt_conj_mul_axis (O : Set ℂ) (hO : IsOpen O) (haxis : {s : ℂ | s.re = 0} ⊆ O)
    (N : ℂ → 𝕂 → ℂ) (hNa : ∀ k, AnalyticOnNhd ℂ (fun s => N s k) O) (c : ℂ) (k : 𝕂) (t : ℝ) :
    HasDerivAt (fun x : ℝ => c * N ((x : ℂ) * I) k) (c * (I * deriv (fun s => N s k) ((t : ℂ) * I))) t ∧
    HasDerivAt (fun x : ℝ => conj (c * N ((x : ℂ) * I) k))
      (conj (c * (I * deriv (fun s => N s k) ((t : ℂ) * I)))) t := by
  have hm : ((t : ℂ) * I) ∈ O := haxis (by simp)
  have hg : HasDerivAt (fun s => N s k) (deriv (fun s => N s k) ((t : ℂ) * I)) ((t : ℂ) * I) :=
    ((hNa k).differentiableOn.differentiableAt (hO.mem_nhds hm)).hasDerivAt
  have h2 : HasDerivAt (fun z : ℂ => N (z * I) k) (deriv (fun s => N s k) ((t : ℂ) * I) * I) (t : ℂ) :=
    HasDerivAt.comp (h₂ := fun s => N s k) (h := fun z : ℂ => z * I) (t : ℂ) hg (hasDerivAt_mul_const I)
  have h3 : HasDerivAt (fun x : ℝ => N ((x : ℂ) * I) k) (deriv (fun s => N s k) ((t : ℂ) * I) * I) t :=
    h2.comp_ofReal
  have h4 : HasDerivAt (fun x : ℝ => c * N ((x : ℂ) * I) k) (c * (I * deriv (fun s => N s k) ((t : ℂ) * I))) t := by
    rw [mul_comm I]; exact h3.const_mul c
  refine ⟨h4, ?_⟩
  have h5 := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t h4
  have e : ((Complex.conjCLE.toContinuousLinearMap : ℂ → ℂ) ∘ fun x : ℝ => c * N ((x : ℂ) * I) k)
      = fun x : ℝ => conj (c * N ((x : ℂ) * I) k) := by
    funext x; simp
  rw [e] at h5
  simpa using h5

end Generic

end Ws31.AxisReg

end

namespace Ws31
namespace AxisReg

open MeasureTheory Filter Topology Complex Metric AutomorphicForm
open scoped ComplexConjugate

theorem main
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        φf s (k : AdelicGL2 (𝓞 F) F) = φf 0 (k : AdelicGL2 (𝓞 F) F))
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        ψf s (k : AdelicGL2 (𝓞 F) F) = ψf 0 (k : AdelicGL2 (𝓞 F) F))
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      ,
    let c : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹
    let nφ : ℝ := Real.sqrt (∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nψ : ℝ := Real.sqrt (∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nNφ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * Nφ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nNψ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * Nψ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nDφ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ^ 2
      ∂(AutomorphicForm.maximalCompactHaar F))
    let nDψ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ^ 2
      ∂(AutomorphicForm.maximalCompactHaar F))
    let U : ℝ → ℂ := fun t =>
      ∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => c * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    let V : ℝ → ℂ := fun t =>
      ∫ k, (fun g => c * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    let Q : ℝ → ℂ := fun t =>
      ∫ k, (fun g => c * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => c * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
          ∂(AutomorphicForm.maximalCompactHaar F)
    let U' : ℝ → ℂ := fun t =>
      ∫ k, φf 0 (k : AdelicGL2 (𝓞 F) F) *
        conj (c * (Complex.I * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)))
          ∂(AutomorphicForm.maximalCompactHaar F)
    let V' : ℝ → ℂ := fun t =>
      ∫ k, c * (Complex.I * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)) *
        conj (ψf 0 (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    Continuous U ∧ Continuous V ∧ Continuous Q ∧ Continuous U' ∧ Continuous V' ∧
    (∀ t : ℝ, HasDerivAt U (U' t) t) ∧ (∀ t : ℝ, HasDerivAt V (V' t) t) ∧
    (∀ t : ℝ, ‖U t‖ ≤ nφ * nNψ t ∧ ‖V t‖ ≤ nNφ t * nψ ∧ ‖Q t‖ ≤ nNφ t * nDψ t ∧
      ‖U' t‖ ≤ nφ * nDψ t ∧ ‖V' t‖ ≤ nDφ t * nψ) := by
  intro αm hαm μ ν _hμ _hν _hμF _hνF _hμk _hνk φf hφf hφfK hφff hφfjc hφfhol hφfKu hφflat
    ψf hψf hψfK hψff hψfjc hψfhol hψfKu hψflat Oφ Eφ Nφ hEφ Oψ Eψ Nψ hEψ
  intro c nφ nψ nNφ nNψ nDφ nDψ U V Q U' V'
  obtain ⟨hOφ, -, haxφ, -, -, hNφa, -, hNφc, -, -⟩ := hEφ
  obtain ⟨hOψ, -, haxψ, -, -, hNψa, -, hNψc, -, -⟩ := hEψ

  set μK : Measure (adelicMaximalCompact F) := maximalCompactHaar F with hμK

  set NφK : ℂ → (adelicMaximalCompact F) → ℂ := fun s k => Nφ s (k : AdelicGL2 (𝓞 F) F) with hNφK
  set NψK : ℂ → (adelicMaximalCompact F) → ℂ := fun s k => Nψ s (k : AdelicGL2 (𝓞 F) F) with hNψK
  have hNφaK : ∀ k, AnalyticOnNhd ℂ (fun s => NφK s k) Oφ := fun k => hNφa k
  have hNψaK : ∀ k, AnalyticOnNhd ℂ (fun s => NψK s k) Oψ := fun k => hNψa k
  have hincl : Continuous (fun p : ℂ × (adelicMaximalCompact F) => (p.1, (p.2 : AdelicGL2 (𝓞 F) F))) := by fun_prop
  have hNφcK : ContinuousOn (fun p : ℂ × (adelicMaximalCompact F) => NφK p.1 p.2) (Oφ ×ˢ Set.univ) :=
    hNφc.comp hincl.continuousOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩)
  have hNψcK : ContinuousOn (fun p : ℂ × (adelicMaximalCompact F) => NψK p.1 p.2) (Oψ ×ˢ Set.univ) :=
    hNψc.comp hincl.continuousOn (fun p hp => ⟨hp.1, Set.mem_univ _⟩)

  set φ0 : (adelicMaximalCompact F) → ℂ := fun k => φf 0 (k : AdelicGL2 (𝓞 F) F) with hφ0
  set ψ0 : (adelicMaximalCompact F) → ℂ := fun k => ψf 0 (k : AdelicGL2 (𝓞 F) F) with hψ0
  have hφ0c : Continuous φ0 := hφfjc.comp (continuous_const.prodMk continuous_subtype_val)
  have hψ0c : Continuous ψ0 := hψfjc.comp (continuous_const.prodMk continuous_subtype_val)
  obtain ⟨Cφ, hCφ⟩ := exists_bound_of_continuous φ0 hφ0c
  obtain ⟨Cψ, hCψ⟩ := exists_bound_of_continuous ψ0 hψ0c
  have hCφ0 : 0 ≤ Cφ := (norm_nonneg _).trans (hCφ 1)
  have hCψ0 : 0 ≤ Cψ := (norm_nonneg _).trans (hCψ 1)

  have haxφ' : ∀ t : ℝ, ((t : ℂ) * I) ∈ Oφ := fun t => haxφ (by simp)
  have haxψ' : ∀ t : ℝ, ((t : ℂ) * I) ∈ Oψ := fun t => haxψ (by simp)
  set Dφ : ℝ → (adelicMaximalCompact F) → ℂ := fun t k => deriv (fun s => NφK s k) ((t : ℂ) * I) with hDφ
  set Dψ : ℝ → (adelicMaximalCompact F) → ℂ := fun t k => deriv (fun s => NψK s k) ((t : ℂ) * I) with hDψ
  have mNφ : ∀ t : ℝ, Continuous (fun k => NφK ((t : ℂ) * I) k) := fun t => continuous_slice Oφ NφK hNφcK _ (haxφ' t)
  have mNψ : ∀ t : ℝ, Continuous (fun k => NψK ((t : ℂ) * I) k) := fun t => continuous_slice Oψ NψK hNψcK _ (haxψ' t)
  have mDφ : ∀ t : ℝ, Measurable (Dφ t) := fun t => measurable_deriv_slice Oφ hOφ NφK hNφaK hNφcK _ (haxφ' t)
  have mDψ : ∀ t : ℝ, Measurable (Dψ t) := fun t => measurable_deriv_slice Oψ hOψ NψK hNψaK hNψcK _ (haxψ' t)
  have cNφ : ∀ k, Continuous (fun t : ℝ => NφK ((t : ℂ) * I) k) := fun k => (continuous_axis Oφ haxφ NφK hNφaK k).1
  have cNψ : ∀ k, Continuous (fun t : ℝ => NψK ((t : ℂ) * I) k) := fun k => (continuous_axis Oψ haxψ NψK hNψaK k).1
  have cDφ : ∀ k, Continuous (fun t : ℝ => Dφ t k) := fun k => (continuous_axis Oφ haxφ NφK hNφaK k).2
  have cDψ : ∀ k, Continuous (fun t : ℝ => Dψ t k) := fun k => (continuous_axis Oψ haxψ NψK hNψaK k).2

  have bφ := exists_local_bound Oφ hOφ haxφ NφK hNφaK hNφcK
  have bψ := exists_local_bound Oψ hOψ haxψ NψK hNψaK hNψcK

  set fU : ℝ → (adelicMaximalCompact F) → ℂ := fun t k => φ0 k * conj (c * NψK ((t : ℂ) * I) k) with hfU
  set fU' : ℝ → (adelicMaximalCompact F) → ℂ := fun t k => φ0 k * conj (c * (I * Dψ t k)) with hfU'
  set fV : ℝ → (adelicMaximalCompact F) → ℂ := fun t k => c * NφK ((t : ℂ) * I) k * conj (ψ0 k) with hfV
  set fV' : ℝ → (adelicMaximalCompact F) → ℂ := fun t k => c * (I * Dφ t k) * conj (ψ0 k) with hfV'
  set fQ : ℝ → (adelicMaximalCompact F) → ℂ := fun t k => c * NφK ((t : ℂ) * I) k * conj (c * Dψ t k) with hfQ
  have hUe : U = fun t => ∫ k, fU t k ∂μK := by
    funext t
    show (∫ k, φf ((t : ℂ) * I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => c * Nψ ((t : ℂ) * I) g) (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) = _
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [hfU, hφ0, hNψK, hφflat]
  have hVe : V = fun t => ∫ k, fV t k ∂μK := by
    funext t
    show (∫ k, (fun g => c * Nφ ((t : ℂ) * I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj (ψf ((t : ℂ) * I) (k : AdelicGL2 (𝓞 F) F)) ∂(maximalCompactHaar F)) = _
    refine integral_congr_ae (Eventually.of_forall fun k => ?_)
    simp only [hfV, hψ0, hNφK, hψflat]
  have hQe : Q = fun t => ∫ k, fQ t k ∂μK := rfl
  have hU'e : U' = fun t => ∫ k, fU' t k ∂μK := rfl
  have hV'e : V' = fun t => ∫ k, fV' t k ∂μK := rfl

  have hconj : Continuous (fun z : ℂ => conj z) := Complex.continuous_conj
  have mfU : ∀ t, AEStronglyMeasurable (fU t) μK := fun t =>
    (hφ0c.mul (hconj.comp (continuous_const.mul (mNψ t)))).aestronglyMeasurable
  have mfU' : ∀ t, AEStronglyMeasurable (fU' t) μK := fun t =>
    (hφ0c.measurable.mul (hconj.measurable.comp ((mDψ t).const_mul I |>.const_mul c))).aestronglyMeasurable
  have mfV : ∀ t, AEStronglyMeasurable (fV t) μK := fun t =>
    ((continuous_const.mul (mNφ t)).mul (hconj.comp hψ0c)).aestronglyMeasurable
  have mfV' : ∀ t, AEStronglyMeasurable (fV' t) μK := fun t =>
    ((((mDφ t).const_mul I).const_mul c).mul (hconj.measurable.comp hψ0c.measurable)).aestronglyMeasurable
  have mfQ : ∀ t, AEStronglyMeasurable (fQ t) μK := fun t =>
    ((continuous_const.mul (mNφ t)).measurable.mul (hconj.measurable.comp ((mDψ t).const_mul c))).aestronglyMeasurable

  have cfU : ∀ k, Continuous (fun t => fU t k) := fun k =>
    continuous_const.mul (hconj.comp (continuous_const.mul (cNψ k)))
  have cfU' : ∀ k, Continuous (fun t => fU' t k) := fun k =>
    continuous_const.mul (hconj.comp (continuous_const.mul (continuous_const.mul (cDψ k))))
  have cfV : ∀ k, Continuous (fun t => fV t k) := fun k =>
    (continuous_const.mul (cNφ k)).mul continuous_const
  have cfV' : ∀ k, Continuous (fun t => fV' t k) := fun k =>
    (continuous_const.mul (continuous_const.mul (cDφ k))).mul continuous_const
  have cfQ : ∀ k, Continuous (fun t => fQ t k) := fun k =>
    (continuous_const.mul (cNφ k)).mul (hconj.comp (continuous_const.mul (cDψ k)))

  have nconj : ∀ z : ℂ, ‖conj z‖ = ‖z‖ := Complex.norm_conj
  have bfU : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖fU t k‖ ≤ M := by
    intro t₀; obtain ⟨M, ε, hε, hM0, hM⟩ := bψ t₀
    refine ⟨Cφ * (‖c‖ * M), ε, hε, fun t ht k => ?_⟩
    simp only [hfU]; rw [norm_mul, nconj, norm_mul]
    exact mul_le_mul (hCφ k) (mul_le_mul_of_nonneg_left (hM t ht k).1 (norm_nonneg _)) (by positivity) hCφ0
  have bfU' : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖fU' t k‖ ≤ M := by
    intro t₀; obtain ⟨M, ε, hε, hM0, hM⟩ := bψ t₀
    refine ⟨Cφ * (‖c‖ * M), ε, hε, fun t ht k => ?_⟩
    simp only [hfU']; rw [norm_mul, nconj, norm_mul, norm_mul, Complex.norm_I, one_mul]
    exact mul_le_mul (hCφ k) (mul_le_mul_of_nonneg_left (hM t ht k).2 (norm_nonneg _)) (by positivity) hCφ0
  have bfV : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖fV t k‖ ≤ M := by
    intro t₀; obtain ⟨M, ε, hε, hM0, hM⟩ := bφ t₀
    refine ⟨‖c‖ * M * Cψ, ε, hε, fun t ht k => ?_⟩
    simp only [hfV]; rw [norm_mul, norm_mul, nconj]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hM t ht k).1 (norm_nonneg _)) (hCψ k) (norm_nonneg _) (by positivity)
  have bfV' : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖fV' t k‖ ≤ M := by
    intro t₀; obtain ⟨M, ε, hε, hM0, hM⟩ := bφ t₀
    refine ⟨‖c‖ * M * Cψ, ε, hε, fun t ht k => ?_⟩
    simp only [hfV']; rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, one_mul, nconj]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hM t ht k).2 (norm_nonneg _)) (hCψ k) (norm_nonneg _) (by positivity)
  have bfQ : ∀ t₀ : ℝ, ∃ M ε : ℝ, 0 < ε ∧ ∀ t, |t - t₀| < ε → ∀ k, ‖fQ t k‖ ≤ M := by
    intro t₀; obtain ⟨M₁, ε₁, hε₁, hM10, hM₁⟩ := bφ t₀; obtain ⟨M₂, ε₂, hε₂, hM20, hM₂⟩ := bψ t₀
    refine ⟨‖c‖ * M₁ * (‖c‖ * M₂), min ε₁ ε₂, lt_min hε₁ hε₂, fun t ht k => ?_⟩
    have ht1 : |t - t₀| < ε₁ := lt_of_lt_of_le ht (min_le_left _ _)
    have ht2 : |t - t₀| < ε₂ := lt_of_lt_of_le ht (min_le_right _ _)
    simp only [hfQ]; rw [norm_mul, norm_mul, nconj, norm_mul]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hM₁ t ht1 k).1 (norm_nonneg _))
      (mul_le_mul_of_nonneg_left (hM₂ t ht2 k).2 (norm_nonneg _)) (by positivity) (by positivity)

  have dU : ∀ t k, HasDerivAt (fun x => fU x k) (fU' t k) t := by
    intro t k
    have h := (hasDerivAt_conj_mul_axis Oψ hOψ haxψ NψK hNψaK c k t).2
    simp only [hfU, hfU', hDψ]
    exact h.const_mul (φ0 k)
  have dV : ∀ t k, HasDerivAt (fun x => fV x k) (fV' t k) t := by
    intro t k
    have h := (hasDerivAt_conj_mul_axis Oφ hOφ haxφ NφK hNφaK c k t).1
    simp only [hfV, hfV', hDφ]
    exact h.mul_const (conj (ψ0 k))

  rw [hUe, hVe, hQe, hU'e, hV'e]
  refine ⟨continuous_integral_of_locBdd μK fU mfU cfU bfU, continuous_integral_of_locBdd μK fV mfV cfV bfV,
    continuous_integral_of_locBdd μK fQ mfQ cfQ bfQ, continuous_integral_of_locBdd μK fU' mfU' cfU' bfU',
    continuous_integral_of_locBdd μK fV' mfV' cfV' bfV',
    fun t => hasDerivAt_integral_of_locBdd μK fU fU' mfU mfU' bfU bfU' dU t,
    fun t => hasDerivAt_integral_of_locBdd μK fV fV' mfV mfV' bfV bfV' dV t, fun t => ?_⟩

  obtain ⟨Mφ, εφ, hεφ, -, hMφ⟩ := bφ t
  obtain ⟨Mψ, εψ, hεψ, -, hMψ⟩ := bψ t
  have ht0φ : |t - t| < εφ := by simp [hεφ]
  have ht0ψ : |t - t| < εψ := by simp [hεψ]
  have eI : ∀ (z : ℂ), ‖c * (I * z)‖ = ‖c * z‖ := fun z => by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, norm_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    have h := norm_integral_mul_conj_le μK φ0 (fun k => c * NψK ((t : ℂ) * I) k) hφ0c.aestronglyMeasurable
      (continuous_const.mul (mNψ t)).aestronglyMeasurable Cφ (‖c‖ * Mψ) hCφ
      (fun k => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMψ t ht0ψ k).1 (norm_nonneg _))
    exact h
  ·
    have h := norm_integral_mul_conj_le μK (fun k => c * NφK ((t : ℂ) * I) k) ψ0
      (continuous_const.mul (mNφ t)).aestronglyMeasurable hψ0c.aestronglyMeasurable (‖c‖ * Mφ) Cψ
      (fun k => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMφ t ht0φ k).1 (norm_nonneg _)) hCψ
    exact h
  ·
    have h := norm_integral_mul_conj_le μK (fun k => c * NφK ((t : ℂ) * I) k) (fun k => c * Dψ t k)
      (continuous_const.mul (mNφ t)).aestronglyMeasurable (((mDψ t).const_mul c)).aestronglyMeasurable
      (‖c‖ * Mφ) (‖c‖ * Mψ)
      (fun k => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMφ t ht0φ k).1 (norm_nonneg _))
      (fun k => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMψ t ht0ψ k).2 (norm_nonneg _))
    exact h
  ·
    have h := norm_integral_mul_conj_le μK φ0 (fun k => c * (I * Dψ t k)) hφ0c.aestronglyMeasurable
      ((((mDψ t).const_mul I).const_mul c)).aestronglyMeasurable Cφ (‖c‖ * Mψ) hCφ
      (fun k => by rw [eI]; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMψ t ht0ψ k).2 (norm_nonneg _))
    have e : (∫ k, ‖c * (I * Dψ t k)‖ ^ 2 ∂μK) = ∫ k, ‖c * Dψ t k‖ ^ 2 ∂μK :=
      integral_congr_ae (Eventually.of_forall fun k => by simp only [eI])
    rw [e] at h
    exact h
  ·
    have h := norm_integral_mul_conj_le μK (fun k => c * (I * Dφ t k)) ψ0
      ((((mDφ t).const_mul I).const_mul c)).aestronglyMeasurable hψ0c.aestronglyMeasurable (‖c‖ * Mφ) Cψ
      (fun k => by rw [eI]; rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hMφ t ht0φ k).2 (norm_nonneg _)) hCψ
    have e : (∫ k, ‖c * (I * Dφ t k)‖ ^ 2 ∂μK) = ∫ k, ‖c * Dφ t k‖ ^ 2 ∂μK :=
      integral_congr_ae (Eventually.of_forall fun k => by simp only [eI])
    rw [e] at h
    exact h

end Ws31.AxisReg

open AutomorphicForm in
theorem solution
    (F : Type) [Field F] [NumberField F] :
    let αm : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    letI := adeleBorel (𝓞 F) F
    ∀ (hαm : ∀ x, 0 < ((αm x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : AutomorphicForm.IsUnitaryChar (𝓞 F) F μ) (_hν : AutomorphicForm.IsUnitaryChar (𝓞 F) F ν)
      (_hμF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F μ) (_hνF : AutomorphicForm.IsIdeleClassChar (𝓞 F) F ν)
      (_hμk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((μ x : ℂˣ) : ℂ))
      (_hνk : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((ν x : ℂˣ) : ℂ))
      (φf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (φf s))
      (_hφfK : ∀ s, IsArchKFinite F (φf s))
      (_hφff : ∀ s, IsKfSmooth F (φf s))
      (_hφfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φf p.1 p.2))
      (_hφfhol : ∀ g, Differentiable ℂ (fun s => φf s g))
      (_hφfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => φf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hφfflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        φf s (k : AdelicGL2 (𝓞 F) F) = φf 0 (k : AdelicGL2 (𝓞 F) F))
      (ψf : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hψf : ∀ s, IsInducedSection (𝓞 F) F (etaFst μ αm hαm s) (etaSnd ν αm hαm s) (ψf s))
      (_hψfK : ∀ s, IsArchKFinite F (ψf s))
      (_hψff : ∀ s, IsKfSmooth F (ψf s))
      (_hψfjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψf p.1 p.2))
      (_hψfhol : ∀ g, Differentiable ℂ (fun s => ψf s g))
      (_hψfKu : ∀ w : InfinitePlace F, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup F w) → ℂ),
        FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 F) F),
          (fun k : ↥(archRowIsometrySubgroup F w) => ψf s (g * (k : AdelicGL2 (𝓞 F) F))) ∈ W)
      (_hψfflat : ∀ (s : ℂ) (k : adelicMaximalCompact F),
        ψf s (k : AdelicGL2 (𝓞 F) F) = ψf 0 (k : AdelicGL2 (𝓞 F) F))
      (Oφ : Set ℂ) (Eφ Nφ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEφ :
      IsOpen Oφ ∧ IsPreconnected Oφ ∧ {s : ℂ | s.re = 0} ⊆ Oφ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oφ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eφ s g) Oφ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nφ s g) Oφ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nφ p.1 p.2) (Oφ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eφ s g = φf s g + ∑' ξ : F, φf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nφ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φf s) g))
      (Oψ : Set ℂ) (Eψ Nψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hEψ :
      IsOpen Oψ ∧ IsPreconnected Oψ ∧ {s : ℂ | s.re = 0} ⊆ Oψ ∧ {s : ℂ | 1 / 2 < s.re} ⊆ Oψ ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Eψ s g) Oψ) ∧
      (∀ g : AdelicGL2 (𝓞 F) F, AnalyticOnNhd ℂ (fun s => Nψ s g) Oψ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Eψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 F) F => Nψ p.1 p.2) (Oψ ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Eψ s g = ψf s g + ∑' ξ : F, ψf s (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 F) F,
        Nψ s g = weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (ψf s) g))
      ,
    let c : ℂ := ((((adelicAddHaar (𝓞 F) F) (adelicBox F)).toReal : ℂ))⁻¹
    let nφ : ℝ := Real.sqrt (∫ k, ‖φf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nψ : ℝ := Real.sqrt (∫ k, ‖ψf 0 (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nNφ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * Nφ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nNψ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * Nψ ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)‖ ^ 2 ∂(AutomorphicForm.maximalCompactHaar F))
    let nDφ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ^ 2
      ∂(AutomorphicForm.maximalCompactHaar F))
    let nDψ : ℝ → ℝ := fun t => Real.sqrt (∫ k, ‖c * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)‖ ^ 2
      ∂(AutomorphicForm.maximalCompactHaar F))
    let U : ℝ → ℂ := fun t =>
      ∫ k, φf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => c * Nψ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    let V : ℝ → ℂ := fun t =>
      ∫ k, (fun g => c * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj (ψf ((t : ℂ) * Complex.I) (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    let Q : ℝ → ℂ := fun t =>
      ∫ k, (fun g => c * Nφ ((t : ℂ) * Complex.I) g) (k : AdelicGL2 (𝓞 F) F) *
        conj ((fun g => c * deriv (fun s : ℂ => Nψ s g) ((t : ℂ) * Complex.I)) (k : AdelicGL2 (𝓞 F) F))
          ∂(AutomorphicForm.maximalCompactHaar F)
    let U' : ℝ → ℂ := fun t =>
      ∫ k, φf 0 (k : AdelicGL2 (𝓞 F) F) *
        conj (c * (Complex.I * deriv (fun s : ℂ => Nψ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)))
          ∂(AutomorphicForm.maximalCompactHaar F)
    let V' : ℝ → ℂ := fun t =>
      ∫ k, c * (Complex.I * deriv (fun s : ℂ => Nφ s (k : AdelicGL2 (𝓞 F) F)) ((t : ℂ) * Complex.I)) *
        conj (ψf 0 (k : AdelicGL2 (𝓞 F) F)) ∂(AutomorphicForm.maximalCompactHaar F)
    Continuous U ∧ Continuous V ∧ Continuous Q ∧ Continuous U' ∧ Continuous V' ∧
    (∀ t : ℝ, HasDerivAt U (U' t) t) ∧ (∀ t : ℝ, HasDerivAt V (V' t) t) ∧
    (∀ t : ℝ, ‖U t‖ ≤ nφ * nNψ t ∧ ‖V t‖ ≤ nNφ t * nψ ∧ ‖Q t‖ ≤ nNφ t * nDψ t ∧
      ‖U' t‖ ≤ nφ * nDψ t ∧ ‖V' t‖ ≤ nDφ t * nψ) :=
  Ws31.AxisReg.main F

end S_AutomorphicForm_continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat
end P2MW
export P2MW.S_AutomorphicForm_continuous_and_hasDerivAt_axis_continuation_weylIntertwiningIntegral_pairings_of_flat (solution)
