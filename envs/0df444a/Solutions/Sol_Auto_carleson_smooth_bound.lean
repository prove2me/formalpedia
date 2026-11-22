-- Prove2me | solution 1 for Auto.carleson_smooth_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:07:41.89859+00:00
-- url     : https://prove2.me/submissions/f00e31b8-e005-4e78-ae5c-1de3f3b118fb

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_hasCompactSupport_of_vanish
public import Theorems.Thm_P2M_Auto_contDiff_carlesonF__1828f049e6a4
public import Theorems.Thm_P2M_Auto_contDiff_carlesonF__cb1ce9767a4b
public import Theorems.Thm_P2M_Auto_contDiff_carlesonF__9fa96f04780b
public import Theorems.Thm_P2M_Auto_hasCompactSupport_carlesonF__75709faac171
public import Theorems.Thm_P2M_Auto_hasCompactSupport_carlesonF__649599a31480
public import Theorems.Thm_P2M_Auto_hasCompactSupport_carlesonF__af972bad9b1b
public import Theorems.Thm_Auto_carleson_trunc_eq
public import Theorems.Thm_P2M_Auto_eLpNorm_carlesonF__a061cbc0b55c
public import Theorems.Thm_P2M_Auto_eLpNorm_carlesonF__9f0cd1d3a307
public import Theorems.Thm_Auto_integrable_carlesonForm
public import Theorems.Thm_Auto_exp_sub_exp_neg
public import Theorems.Thm_Auto_ae_snd_ne_zero
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
public import Theorems.Thm_Auto_triangularHilbertTruncation_integrable
public import Theorems.Thm_Auto_triangularHilbert_main
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
namespace Auto
theorem _root_.solution : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a ν : ℝ → ℝ) (g : ℝ → ℂ) (A L : ℝ),
    ContDiff ℝ ∞ a → ContDiff ℝ ∞ ν → ContDiff ℝ ∞ g →
    (∀ x, A < |x| → a x = 0) → (∀ x, L < |x| → g x = 0) →
    ‖carlesonForm a ν g‖ ≤ C * (eLpNorm (carlesonF₀ a ν 1) 3 volume).toReal *
      (eLpNorm (carlesonF₁ g) 3 volume).toReal * (eLpNorm (carlesonF₂ a ν 1) 3 volume).toReal := by
  obtain ⟨C, hC, hmain⟩ := triangularHilbert_main
  refine ⟨C, hC, fun a ν g A L ha hν hg haA hgL => ?_⟩
  set e := C * (eLpNorm (carlesonF₀ a ν 1) 3 volume).toReal *
    (eLpNorm (carlesonF₁ g) 3 volume).toReal * (eLpNorm (carlesonF₂ a ν 1) 3 volume).toReal
  set w : ℝ × ℝ → ℂ := fun p => (carlesonWeight p.2 : ℂ)
  have hlim : ∀ σ : ℝ, ∃ l : ℂ, Tendsto (fun ε => ∫ p : ℝ × ℝ, carlesonH a ν g σ ε p * w p)
      (𝓝[>] 0) (𝓝 l) ∧ ‖l‖ ≤ e ∧
      ∀ ε > 0, Integrable fun p : ℝ × ℝ => carlesonH a ν g σ ε p * w p := by
    intro σ
    let S₀ := (hasCompactSupport_carlesonF₀ haA ν σ).toSchwartzMap (contDiff_carlesonF₀ ha hν σ)
    let S₁ := (hasCompactSupport_carlesonF₁ hgL).toSchwartzMap (contDiff_carlesonF₁ hg)
    let S₂ := (hasCompactSupport_carlesonF₂ haA ν σ).toSchwartzMap (contDiff_carlesonF₂ ha hν σ)
    have hint : ∀ ε > 0, Integrable (carlesonTrunc a ν g σ ε) := fun ε hε =>
      triangularHilbertTruncation_integrable S₀ S₁ S₂ hε
    obtain ⟨l, hl, hb⟩ := hmain S₀ S₁ S₂
    refine ⟨l, ?_, ?_, fun ε hε => (carleson_trunc_eq a ν g σ ε (hint ε hε)).1⟩
    · refine hl.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (carleson_trunc_eq a ν g σ ε (hint ε hε)).2
    · have hb' : ‖l‖ ≤ C * (eLpNorm (carlesonF₀ a ν σ) 3 volume).toReal *
          (eLpNorm (carlesonF₁ g) 3 volume).toReal *
          (eLpNorm (carlesonF₂ a ν σ) 3 volume).toReal := hb
      rwa [eLpNorm_carlesonF₀ ha.continuous.measurable hν.continuous.measurable,
        eLpNorm_carlesonF₂ ha.continuous.measurable hν.continuous.measurable] at hb'
  obtain ⟨l₁, h₁, hb₁, hi₁⟩ := hlim 1
  obtain ⟨l₂, h₂, hb₂, hi₂⟩ := hlim (-1)
  set f : ℝ × ℝ → ℂ := fun p => (a p.1 : ℂ) ^ 2 * g (p.1 - p.2) *
    ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ)
  obtain ⟨B, hB⟩ : ∃ B, ∀ x, ‖g x‖ ≤ B :=
    (hg.continuous.norm.bddAbove_range_of_hasCompactSupport
      (hasCompactSupport_of_vanish hgL).norm).imp fun B hB x => hB ⟨x, rfl⟩
  have hf : Integrable f := by
    refine integrable_carlesonForm ha.continuous.measurable hν.continuous.measurable
      hg.continuous.measurable hB ?_
    refine (by fun_prop : Continuous fun x => a x ^ 2 * |ν x|).integrable_of_hasCompactSupport
      (hasCompactSupport_of_vanish (A := A) fun x hx => ?_)
    simp [haA x hx]
  have hdiff : ∀ ε > 0, (∫ p, carlesonH a ν g 1 ε p * w p) - ∫ p, carlesonH a ν g (-1) ε p * w p =
      ∫ p, {p : ℝ × ℝ | ε < |p.2|}.indicator (fun p => 2 * Complex.I * f p) p := by
    intro ε hε
    rw [← integral_sub (hi₁ ε hε) (hi₂ ε hε)]
    congr 1
    ext p
    simp only [carlesonH, indicator, mem_ofPred_eq, f, w, one_mul, neg_mul]
    split_ifs with h
    · rw [show ((carlesonWeight p.2 * Real.sin (ν p.1 * p.2) / p.2 : ℝ) : ℂ) =
          (carlesonWeight p.2 : ℂ) * (Real.sin (ν p.1 * p.2) : ℂ) / (p.2 : ℂ) by push_cast; ring]
      linear_combination ((a p.1 : ℂ) ^ 2 * g (p.1 - p.2) / (p.2 : ℂ) *
        (carlesonWeight p.2 : ℂ)) * exp_sub_exp_neg (ν p.1 * p.2)
    · simp
  have hlim₂ : Tendsto (fun ε => ∫ p, {p : ℝ × ℝ | ε < |p.2|}.indicator
      (fun p => 2 * Complex.I * f p) p) (𝓝[>] 0) (𝓝 (∫ p, 2 * Complex.I * f p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => ‖2 * Complex.I * f p‖)
      (Eventually.of_forall fun ε => (hf.const_mul _).aestronglyMeasurable.indicator
        (measurableSet_lt measurable_const (by fun_prop)))
      (Eventually.of_forall fun ε => ae_of_all _ fun p => norm_indicator_le_norm_self _ _)
      (hf.const_mul _).norm ?_
    filter_upwards [ae_snd_ne_zero] with p hp
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (abs_pos.mpr hp))] with ε hε
    rw [indicator_of_mem (show p ∈ {p : ℝ × ℝ | ε < |p.2|} from hε)]
  have heq : 2 * Complex.I * carlesonForm a ν g = l₁ - l₂ := by
    rw [carlesonForm, ← integral_const_mul]
    refine tendsto_nhds_unique hlim₂ ((h₁.sub h₂).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hdiff ε hε
  have hn : ‖2 * Complex.I * carlesonForm a ν g‖ = 2 * ‖carlesonForm a ν g‖ := by simp
  have := norm_sub_le l₁ l₂
  rw [← heq, hn] at this
  linarith
end Auto
