-- Prove2me | solution 1 for Auto.carleson
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:21:24.632191+00:00
-- url     : https://prove2.me/submissions/862e75d3-5c08-4ad4-997a-516b705321fe

module
public import Definitions.Def_Triangular_Auto_TriangularHT
public import Definitions.Def_Triangular_Auto_Carleson
public import Theorems.Thm_Auto_carlesonMass_pos
public import Theorems.Thm_Auto_exists_trig_approx
public import Theorems.Thm_Auto_fourierPartialSum_sub_carlesonOp
public import Theorems.Thm_Auto_carleson_maximal
public import Theorems.Thm_Auto_triangularHilbertLinear_apply
attribute [local simp] Auto.triangularHilbertLinear_apply



set_option autoImplicit true
@[expose] public section
public section
open Auto
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal Convolution
noncomputable section
open Real
namespace Auto
theorem _root_.solution {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1) :
    ∀ᵐ x, Tendsto (fun N => fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  have hm := carlesonMass_pos
  have hπ := Real.pi_pos
  have key : ∀ R j : ℕ, volume {x | x ∈ Icc (-(R : ℝ)) R ∧
      ∃ᶠ N in atTop, 1 / ((j : ℝ) + 1) < ‖fourierPartialSum f N x - f x‖} = 0 := by
    intro R j
    set lam : ℝ := 1 / ((j : ℝ) + 1)
    have hlam : 0 < lam := by positivity
    set lam₀ := π * carlesonMass * (lam / 2)
    have hlam₀ : 0 < lam₀ := by positivity
    obtain ⟨K, -, hK⟩ := carleson_maximal R
    set S := {x | x ∈ Icc (-(R : ℝ)) R ∧
      ∃ᶠ N in atTop, lam < ‖fourierPartialSum f N x - f x‖}
    have hbound : ∀ δ ∈ Ioo (0 : ℝ) (lam / 46),
        volume S ≤ ENNReal.ofReal (4 * (2 * K * δ / lam₀) ^ 3) := by
      rintro δ ⟨hδ, hδ'⟩
      obtain ⟨P, hPc, hPp, ⟨K₀, hK₀⟩, hfP⟩ := exists_trig_approx hf hp hδ
      set g := fun x => f x - P x
      have hgc : Continuous g := hf.sub hPc
      have hgp : Function.Periodic g 1 := fun x => by simp only [g, hp x, hPp x]
      have hgδ : ∀ x, ‖g x‖ ≤ δ := fun x => (hfP x).le
      set g' := (Icc (-((R : ℝ) + 11)) ((R : ℝ) + 11)).indicator g
      have hg'm : Measurable g' := hgc.measurable.indicator measurableSet_Icc
      have hg'B : ∀ x, ‖g' x‖ ≤ δ := fun x => by
        by_cases hx : x ∈ Icc (-((R : ℝ) + 11)) ((R : ℝ) + 11)
        · rw [show g' x = g x from indicator_of_mem hx _]; exact hgδ x
        · rw [show g' x = 0 from indicator_of_notMem hx _, norm_zero]; exact hδ.le
      have hg'z : ∀ x, (R : ℝ) + 11 < |x| → g' x = 0 := fun x hx =>
        indicator_of_notMem (show x ∉ Icc (-((R : ℝ) + 11)) ((R : ℝ) + 11) from
          fun h => (not_le.mpr hx) (abs_le.mpr h)) _
      refine le_trans (measure_mono ?_) (hK g' δ lam₀ hg'm hg'B hg'z hlam₀)
      rintro x ⟨hx, hfr⟩
      refine ⟨hx, ?_⟩
      obtain ⟨N, hN, hNK⟩ := (hfr.and_eventually (eventually_ge_atTop K₀)).exists
      refine ⟨N, ?_⟩
      have hsplit : fourierPartialSum f N x - f x = fourierPartialSum g N x - g x := by
        have : fourierPartialSum f N x = fourierPartialSum g N x + fourierPartialSum P N x := by
          rw [← fourierPartialSum_add hgc hPc]
          simp [g]
        rw [this, hK₀ N hNK x]
        simp only [g]
        ring
      rw [hsplit] at hN
      have hd : ‖fourierPartialSum g N x - ((1 / (π * carlesonMass) : ℝ) : ℂ) *
          carlesonOp g' (fun _ => (2 * N + 1) * π) x‖ ≤ 22 * δ :=
        fourierPartialSum_sub_carlesonOp hgc hgp hgδ (abs_le.mpr hx) N
      have h₁ := norm_sub_le (fourierPartialSum g N x) (g x)
      have h₂ := norm_le_insert' (fourierPartialSum g N x) (((1 / (π * carlesonMass) : ℝ) : ℂ) *
        carlesonOp g' (fun _ => (2 * N + 1) * π) x)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at h₂
      have h₃ : lam / 2 < 1 / (π * carlesonMass) * ‖carlesonOp g' (fun _ => (2 * N + 1) * π) x‖ := by
        linarith [hgδ x]
      rw [one_div, inv_mul_eq_div, lt_div_iff₀ (by positivity)] at h₃
      show π * carlesonMass * (lam / 2) < _
      linarith
    have hlim : Tendsto (fun δ => ENNReal.ofReal (4 * (2 * K * δ / lam₀) ^ 3)) (𝓝[>] 0) (𝓝 0) := by
      have h : Tendsto (fun δ : ℝ => 4 * (2 * K * δ / lam₀) ^ 3) (𝓝 0) (𝓝 0) := by
        have : Continuous fun δ : ℝ => 4 * (2 * K * δ / lam₀) ^ 3 := by fun_prop
        simpa using this.tendsto 0
      simpa using (ENNReal.tendsto_ofReal h).mono_left nhdsWithin_le_nhds
    refine nonpos_iff_eq_zero.mp (ge_of_tendsto hlim ?_)
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < lam / 46 by positivity)] with δ hδ
    exact hbound δ hδ
  rw [ae_iff]
  refine measure_mono_null ?_ (measure_iUnion_null fun R : ℕ =>
    measure_iUnion_null fun j : ℕ => key R j)
  intro x hx
  simp only [mem_ofPred_eq, Metric.tendsto_atTop, not_forall, not_exists, not_lt] at hx
  obtain ⟨ε, hε, hfreq⟩ := hx
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt hε
  simp only [mem_iUnion]
  refine ⟨⌈|x|⌉₊, j, ?_, ?_⟩
  · rw [mem_Icc, ← abs_le]
    exact Nat.le_ceil _
  · rw [Filter.frequently_atTop]
    intro N₀
    obtain ⟨N, hN, hd⟩ := hfreq N₀
    exact ⟨N, hN, by rw [← dist_eq_norm]; linarith⟩
end Auto
