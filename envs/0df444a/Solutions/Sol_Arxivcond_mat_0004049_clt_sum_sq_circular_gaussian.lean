-- Prove2me | solution 1 for Arxivcond_mat_0004049.clt_sum_sq_circular_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T15:36:25.682297+00:00
-- url     : https://prove2.me/submissions/a529f5a8-fba9-428d-bbd1-ee7d5c99495d

import Mathlib
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_gaussianReal_fourth_moment

open MeasureTheory ProbabilityTheory Filter Topology Complex

open scoped ComplexConjugate RealInnerProductSpace

/-- Characteristic function of the circular complex Gaussian with real and imaginary parts
i.i.d. `N(0, s)`. -/
lemma clt_sq_charFun_circ (s : NNReal) (w : ℂ) :
    charFun (((gaussianReal 0 s).prod (gaussianReal 0 s)).map
      Complex.measurableEquivRealProd.symm) w = cexp (-((s : ℝ) * ‖w‖ ^ 2 / 2 : ℝ)) := by
  rw [charFun_apply, integral_map_equiv]
  have hin : ∀ p : ℝ × ℝ, cexp (((⟪Complex.measurableEquivRealProd.symm p, w⟫ : ℝ) : ℂ) * I)
      = cexp ((w.re : ℂ) * p.1 * I) * cexp ((w.im : ℂ) * p.2 * I) := by
    intro p
    rw [← Complex.exp_add, Complex.inner]
    congr 1
    simp [Complex.measurableEquivRealProd]
    ring
  simp_rw [hin]
  rw [integral_prod_mul (fun x : ℝ => cexp ((w.re : ℂ) * x * I))
    (fun y : ℝ => cexp ((w.im : ℂ) * y * I))]
  rw [← charFun_apply_real, ← charFun_apply_real, charFun_gaussianReal, charFun_gaussianReal,
    ← Complex.exp_add]
  congr 1
  rw [Complex.sq_norm, Complex.normSq_apply]
  push_cast
  ring

/-- Mean and second moment of `a (x² - y²) + 2 b x y` for `x, y` i.i.d. `N(0, 1/2)`. -/
lemma clt_sq_moments (a b : ℝ) :
    (∫ p : ℝ × ℝ, a * (p.1 ^ 2 - p.2 ^ 2) + 2 * b * (p.1 * p.2)
      ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))) = 0 ∧
    (∫ p : ℝ × ℝ, (a * (p.1 ^ 2 - p.2 ^ 2) + 2 * b * (p.1 * p.2)) ^ 2
      ∂((gaussianReal 0 (1 / 2)).prod (gaussianReal 0 (1 / 2)))) = a ^ 2 + b ^ 2 := by
  set g : Measure ℝ := gaussianReal 0 (1 / 2) with hg
  have hI : ∀ k : ℕ, Integrable (fun x : ℝ => x ^ k) g := fun k => by
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1 / 2) (k : NNReal)).integrable_norm_pow'
      (p := k)
    exact h.mono' (by fun_prop) (ae_of_all _ fun x => by simp [norm_pow])
  have hT : ∀ i j : ℕ, Integrable (fun p : ℝ × ℝ => p.1 ^ i * p.2 ^ j) (g.prod g) :=
    fun i j => (hI i).mul_prod (hI j)
  have hTi : ∀ i j : ℕ, ∫ p : ℝ × ℝ, p.1 ^ i * p.2 ^ j ∂(g.prod g) =
      (∫ x, x ^ i ∂g) * ∫ x, x ^ j ∂g := fun i j => integral_prod_mul _ _
  have m0 : ∫ x, x ^ 0 ∂g = 1 := by simp
  have m1 : ∫ x, x ^ 1 ∂g = 0 := by simp [hg, integral_id_gaussianReal]
  have m2 : ∫ x, x ^ 2 ∂g = 1 / 2 := by
    have h := variance_eq_integral (μ := g) (X := id) measurable_id.aemeasurable
    simp only [id] at h
    rw [hg, variance_id_gaussianReal, integral_id_gaussianReal] at h
    simp only [sub_zero] at h
    rw [← h]
    norm_num
  have m4 : ∫ x, x ^ 4 ∂g = 3 / 4 := by
    rw [hg, LevyStochCalc.Brownian.Continuity.gaussianReal_fourth_moment]
    norm_num
  constructor
  · have e : (fun p : ℝ × ℝ => a * (p.1 ^ 2 - p.2 ^ 2) + 2 * b * (p.1 * p.2)) =
        fun p => a * (p.1 ^ 2 * p.2 ^ 0) - a * (p.1 ^ 0 * p.2 ^ 2) + 2 * b * (p.1 ^ 1 * p.2 ^ 1) := by
      funext p; ring
    rw [e, integral_add, integral_sub, integral_const_mul,
      integral_const_mul, integral_const_mul, hTi, hTi, hTi, m0, m1, m2]
    · ring
    all_goals
      repeat' first
        | exact (hT _ _).const_mul _
        | apply Integrable.add
        | apply Integrable.sub
        | apply Integrable.neg
  · have e : (fun p : ℝ × ℝ => (a * (p.1 ^ 2 - p.2 ^ 2) + 2 * b * (p.1 * p.2)) ^ 2) =
        fun p => a ^ 2 * (p.1 ^ 4 * p.2 ^ 0) + a ^ 2 * (p.1 ^ 0 * p.2 ^ 4)
          + (4 * b ^ 2 - 2 * a ^ 2) * (p.1 ^ 2 * p.2 ^ 2)
          + 4 * a * b * (p.1 ^ 3 * p.2 ^ 1) - 4 * a * b * (p.1 ^ 1 * p.2 ^ 3) := by
      funext p; ring
    rw [e, integral_sub, integral_add, integral_add, integral_add, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      hTi, hTi, hTi, hTi, hTi, m0, m1, m2, m4]
    · ring
    all_goals
      repeat' first
        | exact (hT _ _).const_mul _
        | apply Integrable.add

theorem solution (f : BoundedContinuousFunction ℂ ℝ) :
    Tendsto (fun n : ℕ => ∫ z, f (((Real.sqrt n)⁻¹ : ℂ) * ∑ k ∈ Finset.range n, z k ^ 2)
        ∂(Measure.infinitePi fun _ : ℕ => ((gaussianReal 0 (1 / 2)).prod
          (gaussianReal 0 (1 / 2))).map Complex.measurableEquivRealProd.symm))
      atTop (𝓝 (∫ w, f w ∂(((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        Complex.measurableEquivRealProd.symm))) := by
  set ν₁ : Measure ℂ := ((gaussianReal 0 (1 / 2)).prod
    (gaussianReal 0 (1 / 2))).map Complex.measurableEquivRealProd.symm with hν₁
  set ν₂ : Measure ℂ := ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
    Complex.measurableEquivRealProd.symm with hν₂
  have hν₁P : IsProbabilityMeasure ν₁ := Measure.isProbabilityMeasure_map (by fun_prop)
  have hν₂P : IsProbabilityMeasure ν₂ := Measure.isProbabilityMeasure_map (by fun_prop)
  set P : Measure (ℕ → ℂ) := Measure.infinitePi fun _ : ℕ => ν₁ with hP
  let W : ℕ → (ℕ → ℂ) → ℂ := fun n z => ((Real.sqrt n)⁻¹ : ℂ) * ∑ k ∈ Finset.range n, z k ^ 2
  have hW : ∀ n, Measurable (W n) := fun n => by fun_prop
  let μs : ℕ → ProbabilityMeasure ℂ := fun n =>
    ⟨P.map (W n), Measure.isProbabilityMeasure_map (hW n).aemeasurable⟩
  let μ₀ : ProbabilityMeasure ℂ := ⟨ν₂, hν₂P⟩
  have key : Tendsto μs atTop (𝓝 μ₀) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    simp only [μs, μ₀, ProbabilityMeasure.coe_mk]
    rw [hν₂, clt_sq_charFun_circ]
    rcases eq_or_ne t 0 with rfl | ht
    · have : ∀ n, IsProbabilityMeasure (P.map (W n)) := fun n =>
        Measure.isProbabilityMeasure_map (hW n).aemeasurable
      simp
    have htn : 0 < ‖t‖ := norm_pos_iff.2 ht
    let Y : ℂ → ℝ := fun z => ⟪z ^ 2, t⟫ / ‖t‖
    have hY : Measurable Y := by fun_prop
    let X : ℕ → (ℕ → ℂ) → ℝ := fun k ω => Y (ω k)
    have hindep : iIndepFun X P := iIndepFun_infinitePi (X := fun _ => Y) (fun _ => hY)
    have hlaw : ∀ i, P.map (X i) = ν₁.map Y := fun i => by
      rw [← (measurePreserving_eval_infinitePi (fun _ : ℕ => ν₁) i).map_eq,
        Measure.map_map hY (measurable_pi_apply i)]
      rfl
    have hident : ∀ i, IdentDistrib (X i) (X 0) P P := fun i =>
      ⟨(hY.comp (measurable_pi_apply i)).aemeasurable,
        (hY.comp (measurable_pi_apply 0)).aemeasurable, by rw [hlaw, hlaw]⟩
    have hYcoord : ∀ p : ℝ × ℝ, Y (Complex.measurableEquivRealProd.symm p) =
        t.re / ‖t‖ * (p.1 ^ 2 - p.2 ^ 2) + 2 * (t.im / ‖t‖) * (p.1 * p.2) := by
      intro p
      simp only [Y, Complex.inner]
      simp [Complex.measurableEquivRealProd, pow_two]
      ring
    have hmom := clt_sq_moments (t.re / ‖t‖) (t.im / ‖t‖)
    have h0 : ν₁[Y] = 0 := by
      rw [hν₁, integral_map_equiv]
      simp_rw [hYcoord]
      exact hmom.1
    have h1 : ν₁[Y ^ 2] = 1 := by
      rw [hν₁, integral_map_equiv]
      simp only [Pi.pow_apply]
      simp_rw [hYcoord]
      rw [hmom.2]
      have hn2 : ‖t‖ ^ 2 = t.re ^ 2 + t.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [div_pow, div_pow, ← add_div, ← hn2, div_self (by positivity)]
    have hcf : ∀ n : ℕ, charFun (P.map (W n)) t =
        charFun (P.map (fun ω => (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)) ‖t‖ := by
      intro n
      rw [charFun_apply, charFun_apply, integral_map (hW n).aemeasurable (by fun_prop),
        integral_map (by fun_prop) (by fun_prop)]
      congr 1
      ext ω
      congr 3
      have hs : W n ω = ((√n)⁻¹ : ℝ) • ∑ k ∈ Finset.range n, ω k ^ 2 := by
        simp [W, Complex.real_smul]
      rw [hs, real_inner_smul_left, sum_inner]
      simp only [X, Y]
      rw [real_inner_comm, RCLike.inner_apply, conj_trivial, ← Finset.sum_div]
      field_simp
    simp_rw [hcf, charFun_inv_sqrt_mul_sum hindep hident, hlaw]
    convert tendsto_charFun_inv_sqrt_mul_pow hY.aemeasurable h0 h1 ‖t‖ using 2
    push_cast
    ring_nf
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at key
  have := key f
  simp only [μs, μ₀, ProbabilityMeasure.coe_mk] at this
  refine this.congr fun n => ?_
  rw [integral_map (hW n).aemeasurable (by fun_prop)]
