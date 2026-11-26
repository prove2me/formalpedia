-- Prove2me | solution 1 for Arxiv2105_07250.random_phase_kernel_sinc
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T08:48:42.928356+00:00
-- url     : https://prove2.me/submissions/bd2c527a-ffe3-49db-9047-3c68ee6a863d

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section
namespace RP
open Arxiv2105_07250

lemma p3 (wmin wmax : ℝ) (hw : wmin < wmax) (τ : ℝ) :
    (∫ w in wmin..wmax, Real.cos (w * τ)) / (wmax - wmin) =
      Real.cos ((wmax + wmin) / 2 * τ) * Real.sinc ((wmax - wmin) / 2 * τ) := by
  have hne : wmax - wmin ≠ 0 := by linarith
  by_cases hτ : τ = 0
  · subst hτ; simp only [mul_zero, Real.cos_zero, intervalIntegral.integral_const, smul_eq_mul, mul_one, Real.sinc_zero]; field_simp
  · rw [intervalIntegral.integral_comp_mul_right (fun x => Real.cos x) hτ, integral_cos]
    have hx : (wmax - wmin) / 2 * τ ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hx]
    have : Real.sin (wmax * τ) - Real.sin (wmin * τ) =
        2 * Real.cos ((wmax + wmin) / 2 * τ) * Real.sin ((wmax - wmin) / 2 * τ) := by
      rw [show wmax * τ = (wmax + wmin) / 2 * τ + (wmax - wmin) / 2 * τ by ring,
        show wmin * τ = (wmax + wmin) / 2 * τ - (wmax - wmin) / 2 * τ by ring,
        Real.sin_add, Real.sin_sub]; ring
    rw [smul_eq_mul, this]
    field_simp

lemma p4 (wmin wmax vabs x' x'' : ℝ) :
    Real.cos ((wmax + wmin) / 2 * ((x'' - x') / vabs)) *
          Real.sinc ((wmax - wmin) / 2 * ((x'' - x') / vabs)) =
        Real.cos ((wmax + wmin) / 2 * (|x'' - x'| / vabs)) *
          Real.sinc ((wmax - wmin) / 2 * (|x'' - x'| / vabs)) := by
  rcases abs_choice (x'' - x') with h | h
  · rw [h]
  · rw [h, show (wmax + wmin) / 2 * (-(x'' - x') / vabs) = -((wmax + wmin) / 2 * ((x'' - x') / vabs)) by ring,
      show (wmax - wmin) / 2 * (-(x'' - x') / vabs) = -((wmax - wmin) / 2 * ((x'' - x') / vabs)) by ring,
      Real.cos_neg, Real.sinc_neg]

lemma p5 (w0 τ : ℝ) : Tendsto (fun D : ℝ => Real.cos (w0 * τ) * Real.sinc (D / 2 * τ)) (𝓝[>] 0)
      (𝓝 (Real.cos (w0 * τ))) := by
  have hc : Continuous (fun D : ℝ => Real.cos (w0 * τ) * Real.sinc (D / 2 * τ)) := by
    have := Real.continuous_sinc
    fun_prop
  have := hc.tendsto 0
  simp only [zero_div, zero_mul, Real.sinc_zero, mul_one] at this
  exact tendsto_nhdsWithin_of_tendsto_nhds this

lemma p2 (wmin wmax : ℝ) (hw : wmin < wmax) (τ : ℝ) :
    Tendsto (fun N : ℕ => (∑ j : Fin N, Real.cos (bandGrid wmin wmax N j * τ)) / N)
      atTop (𝓝 ((∫ w in wmin..wmax, Real.cos (w * τ)) / (wmax - wmin))) := by
  set L := wmax - wmin with hL
  have hLp : 0 < L := by linarith
  have key : ∀ N : ℕ, 1 ≤ N →
      |(∑ j : Fin N, Real.cos (bandGrid wmin wmax N j * τ)) / N -
        (∫ w in wmin..wmax, Real.cos (w * τ)) / L| ≤ |τ| * L / N := by
    intro N hN
    have hNp : (0 : ℝ) < N := by exact_mod_cast hN
    set Δ := L / N with hΔ
    have hΔp : 0 < Δ := by positivity
    set p : ℕ → ℝ := fun k => wmin + k * Δ with hp
    have hp0 : p 0 = wmin := by simp [p]
    have hpN : p N = wmax := by simp only [p, Δ]; field_simp; ring
    have hci : ∀ u v : ℝ, IntervalIntegrable (fun w => Real.cos (w * τ)) volume u v :=
      fun u v => (by fun_prop : Continuous (fun w : ℝ => Real.cos (w * τ))).intervalIntegrable u v
    have hsplit := intervalIntegral.sum_integral_adjacent_intervals (f := fun w => Real.cos (w * τ))
      (μ := volume) (a := p) (n := N) (fun k _ => hci _ _)
    rw [hp0, hpN] at hsplit
    have hpiece : ∀ k ∈ Finset.range N,
        |(∫ w in p k..p (k + 1), Real.cos (w * τ)) - Δ * Real.cos (p (k + 1) * τ)| ≤ |τ| * Δ * Δ := by
      intro k _
      have hlen : p (k + 1) - p k = Δ := by simp only [p]; push_cast; ring
      have e : (∫ w in p k..p (k + 1), Real.cos (w * τ)) - Δ * Real.cos (p (k + 1) * τ) =
          ∫ w in p k..p (k + 1), (Real.cos (w * τ) - Real.cos (p (k + 1) * τ)) := by
        rw [intervalIntegral.integral_sub (hci _ _) intervalIntegrable_const,
          intervalIntegral.integral_const, smul_eq_mul, hlen]
      rw [e]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := p k) (b := p (k + 1))
        (C := |τ| * Δ) (f := fun w => Real.cos (w * τ) - Real.cos (p (k + 1) * τ)) (by
          intro x hx
          rw [Set.uIoc_of_le (by linarith)] at hx
          rw [Real.norm_eq_abs]
          refine (Real.abs_cos_sub_cos_le _ _).trans ?_
          rw [← sub_mul, abs_mul, mul_comm]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2])
      rw [Real.norm_eq_abs, hlen, abs_of_pos hΔp] at this
      exact this
    have hgrid : ∀ j : Fin N, bandGrid wmin wmax N j = p ((j : ℕ) + 1) := by
      intro j; simp only [bandGrid, p, Δ, hL]; push_cast; ring
    have hsum : (∑ j : Fin N, Real.cos (bandGrid wmin wmax N j * τ)) =
        ∑ k ∈ Finset.range N, Real.cos (p (k + 1) * τ) := by
      rw [Finset.sum_congr rfl (fun j _ => by rw [hgrid j])]
      exact Fin.sum_univ_eq_sum_range (fun k => Real.cos (p (k + 1) * τ)) N
    rw [hsum, ← hsplit]
    have htot : |(∑ k ∈ Finset.range N, ∫ w in p k..p (k + 1), Real.cos (w * τ)) -
        Δ * ∑ k ∈ Finset.range N, Real.cos (p (k + 1) * τ)| ≤ N * (|τ| * Δ * Δ) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum hpiece).trans ?_
      simp
    have hLN : L = N * Δ := by simp only [Δ]; field_simp
    rw [show (∑ k ∈ Finset.range N, Real.cos (p (k + 1) * τ)) / N -
        (∑ k ∈ Finset.range N, ∫ w in p k..p (k + 1), Real.cos (w * τ)) / L =
        -((∑ k ∈ Finset.range N, ∫ w in p k..p (k + 1), Real.cos (w * τ)) -
          Δ * ∑ k ∈ Finset.range N, Real.cos (p (k + 1) * τ)) / L by
        generalize (∑ k ∈ Finset.range N, Real.cos (p (k + 1) * τ)) = S1
        generalize (∑ k ∈ Finset.range N, ∫ w in p k..p (k + 1), Real.cos (w * τ)) = S2
        rw [hLN]; field_simp; ring]
    rw [abs_div, abs_neg, abs_of_pos hLp, div_le_iff₀ hLp]
    calc _ ≤ N * (|τ| * Δ * Δ) := htot
      _ = |τ| * L / N * L := by rw [hLN]; field_simp
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_gt (|τ| * L / ε)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  rw [Real.dist_eq]
  refine lt_of_le_of_lt (key N hN1) ?_
  rw [div_lt_iff₀ hNp]
  have : (N0 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_left _ _) hN
  rw [div_lt_iff₀ hε] at hN0
  nlinarith

lemma unif_int (g : ℝ → ℝ) :
    ∫ θ, g θ ∂uniformPhase = (1 / (2 * Real.pi)) * ∫ θ in (0:ℝ)..(2 * Real.pi), g θ := by
  unfold uniformPhase
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul,
    intervalIntegral.integral_of_le (by positivity), integral_Ico_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]

lemma E1 (x : ℝ) : ∫ θ, Real.cos (x + θ) ∂uniformPhase = 0 := by
  rw [unif_int, intervalIntegral.integral_comp_add_left (fun u => Real.cos u), integral_cos]
  rw [show x + 2 * Real.pi = x + 2 * Real.pi by ring, Real.sin_add_two_pi]; simp

lemma E2 (x y : ℝ) : ∫ θ, Real.cos (x + θ) * Real.cos (y + θ) ∂uniformPhase = Real.cos (x - y) / 2 := by
  rw [unif_int]
  have e : (fun θ => Real.cos (x + θ) * Real.cos (y + θ)) =
      fun θ => Real.cos (x - y) / 2 + Real.cos ((x + y) + 2 * θ) / 2 := by
    funext θ
    rw [Real.cos_add (x + y), show 2 * θ = θ + θ by ring]
    rw [Real.cos_add, Real.cos_add, Real.cos_sub, Real.cos_add θ, Real.sin_add θ, Real.cos_add x y, Real.sin_add x y]
    linear_combination ((1:ℝ)/2 * Real.cos x * Real.cos y + 1/2 * Real.sin x * Real.sin y) * (Real.sin_sq_add_cos_sq θ)
  rw [e, intervalIntegral.integral_add intervalIntegrable_const
    ((by fun_prop : Continuous (fun θ : ℝ => Real.cos ((x + y) + 2 * θ) / 2)).intervalIntegrable _ _)]
  rw [intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_comp_add_mul (fun u => Real.cos u) (by norm_num : (2:ℝ) ≠ 0), integral_cos]
  rw [show x + y + 2 * (2 * Real.pi) = (x + y) + 2 * Real.pi + 2 * Real.pi by ring,
    Real.sin_add_two_pi, Real.sin_add_two_pi]
  simp only [mul_zero, add_zero, sub_self, smul_zero, zero_div, smul_eq_mul, sub_zero]
  field_simp

end RP

open Arxiv2105_07250 RP in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (wmin wmax : ℝ) (hw : wmin < wmax) (a : ℝ) :
    (∀ (N : ℕ) (θ : Fin N → Ω → ℝ), (∀ j, Measurable (θ j)) → (∀ j, P.map (θ j) = uniformPhase) →
      (∀ j k, j ≠ k → IndepFun (θ j) (θ k) P) → ∀ t' t'' : ℝ,
        ∫ r, sourceSignature (bandGrid wmin wmax N) (fun _ => a) (fun j => θ j r) t' *
            sourceSignature (bandGrid wmin wmax N) (fun _ => a) (fun j => θ j r) t'' ∂P =
          a ^ 2 / 2 * ∑ j, Real.cos (bandGrid wmin wmax N j * (t'' - t'))) ∧
    (∀ τ : ℝ, Tendsto (fun N : ℕ => (∑ j : Fin N, Real.cos (bandGrid wmin wmax N j * τ)) / N)
      atTop (𝓝 ((∫ w in wmin..wmax, Real.cos (w * τ)) / (wmax - wmin)))) ∧
    (∀ τ : ℝ, (∫ w in wmin..wmax, Real.cos (w * τ)) / (wmax - wmin) =
      Real.cos ((wmax + wmin) / 2 * τ) * Real.sinc ((wmax - wmin) / 2 * τ)) ∧
    (∀ vabs : ℝ, 0 < vabs → ∀ x' x'' : ℝ,
      Real.cos ((wmax + wmin) / 2 * ((x'' - x') / vabs)) *
          Real.sinc ((wmax - wmin) / 2 * ((x'' - x') / vabs)) =
        Real.cos ((wmax + wmin) / 2 * (|x'' - x'| / vabs)) *
          Real.sinc ((wmax - wmin) / 2 * (|x'' - x'| / vabs))) ∧
    (∀ w0 τ : ℝ, Tendsto (fun D : ℝ => Real.cos (w0 * τ) * Real.sinc (D / 2 * τ)) (𝓝[>] 0)
      (𝓝 (Real.cos (w0 * τ)))) := by
  refine ⟨?_, fun τ => p2 wmin wmax hw τ, fun τ => p3 wmin wmax hw τ,
    fun vabs _ x' x'' => p4 wmin wmax vabs x' x'', p5⟩
  intro N θ hθm hlaw hind t' t''
  set w := bandGrid wmin wmax N
  have hm : ∀ (i : Fin N) (x : ℝ), Measurable (fun r => Real.cos (x + θ i r)) :=
    fun i x => Real.continuous_cos.measurable.comp (measurable_const.add (hθm i))
  have hE : ∀ (i : Fin N) (g : ℝ → ℝ), Measurable g →
      ∫ r, g (θ i r) ∂P = ∫ u, g u ∂uniformPhase := by
    intro i g hg
    rw [← hlaw i, integral_map (hθm i).aemeasurable hg.aestronglyMeasurable]
  have hInt : ∀ i j : Fin N, Integrable (fun r => a * Real.cos (w i * t' + θ i r) *
      (a * Real.cos (w j * t'' + θ j r))) P := by
    intro i j
    refine Integrable.of_bound (by
      exact ((measurable_const.mul (hm i _)).mul (measurable_const.mul (hm j _))).aestronglyMeasurable)
      (|a| * |a|) (Filter.Eventually.of_forall (fun r => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have h1 := Real.abs_cos_le_one (w i * t' + θ i r)
    have h2 := Real.abs_cos_le_one (w j * t'' + θ j r)
    have := abs_nonneg a
    calc |a| * |Real.cos (w i * t' + θ i r)| * (|a| * |Real.cos (w j * t'' + θ j r)|)
        ≤ |a| * 1 * (|a| * 1) := by gcongr
      _ = |a| * |a| := by ring
  have hterm : ∀ i j : Fin N, ∫ r, a * Real.cos (w i * t' + θ i r) *
      (a * Real.cos (w j * t'' + θ j r)) ∂P =
        if i = j then a ^ 2 / 2 * Real.cos (w i * (t'' - t')) else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      have := hE i (fun u => a * Real.cos (w i * t' + u) * (a * Real.cos (w i * t'' + u)))
        (by fun_prop)
      rw [this]
      have e : (fun u => a * Real.cos (w i * t' + u) * (a * Real.cos (w i * t'' + u))) =
          fun u => a ^ 2 * (Real.cos (w i * t' + u) * Real.cos (w i * t'' + u)) := by
        funext u; ring
      rw [e, integral_const_mul, E2]
      rw [show w i * t' - w i * t'' = -(w i * (t'' - t')) by ring, Real.cos_neg]; ring
    · have hI := ((hind i j hij).comp (show Measurable (fun u : ℝ => Real.cos (w i * t' + u)) by fun_prop)
        (show Measurable (fun u : ℝ => Real.cos (w j * t'' + u)) by fun_prop))
      have e : (fun r => a * Real.cos (w i * t' + θ i r) * (a * Real.cos (w j * t'' + θ j r))) =
          fun r => a ^ 2 * (Real.cos (w i * t' + θ i r) * Real.cos (w j * t'' + θ j r)) := by
        funext r; ring
      rw [e, integral_const_mul]
      have := hI.integral_fun_mul_eq_mul_integral (hm i _).aestronglyMeasurable
        (hm j _).aestronglyMeasurable
      simp only [Function.comp_def] at this
      rw [this]
      have e1 : ∫ r, Real.cos (w i * t' + θ i r) ∂P = 0 := by
        rw [hE i (fun u => Real.cos (w i * t' + u)) (by fun_prop), E1]
      rw [e1]; simp
  unfold sourceSignature
  rw [show (fun r => (∑ i, a * Real.cos (w i * t' + θ i r)) * ∑ i, a * Real.cos (w i * t'' + θ i r)) =
      fun r => ∑ i, ∑ j, a * Real.cos (w i * t' + θ i r) * (a * Real.cos (w j * t'' + θ j r)) by
    funext r; rw [Finset.sum_mul_sum]]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hInt i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hInt _ j), hterm]
  simp [Finset.sum_ite_eq, Finset.mul_sum]
