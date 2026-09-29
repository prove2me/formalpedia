-- Prove2me | solution 1 for AutomorphicForm.ComplexIwasawa.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/6c118136-c4a9-5cf4-8be3-d1fbbf8c2229

import Mathlib
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
import Theorems.Thm_AutomorphicForm_ComplexIwasawa_contDiff_and_exists_bound_iteratedFDeriv_kC_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral

set_option autoImplicit false

open Set MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff FourierTransform ComplexConjugate Topology

noncomputable section

namespace HARCHC

private def G (a b : ℕ) (w ζ z : ℂ) : ℂ :=
  z ^ a * conj z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
    * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))

private theorem one_add_norm_sq_pos (z : ℂ) : 0 < 1 + ‖z‖ ^ 2 := by positivity

private theorem one_le_one_add_norm_sq (z : ℂ) : 1 ≤ 1 + ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]

private theorem norm_character (ζ z : ℂ) : ‖Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))‖ = 1 := by
  rw [← neg_mul, ← Complex.ofReal_neg]
  exact Complex.norm_exp_ofReal_mul_I _

private theorem norm_G (a b : ℕ) (w ζ z : ℂ) : ‖G a b w ζ z‖ = ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re) := by
  unfold G
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos (one_add_norm_sq_pos z), Complex.neg_re, norm_character, mul_one, pow_add]

private theorem norm_pow_le_bracket (m : ℕ) (z : ℂ) : ‖z‖ ^ m ≤ (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
  have hR0 : 0 < 1 + ‖z‖ ^ 2 := one_add_norm_sq_pos z
  have h1 : ‖z‖ ≤ (1 + ‖z‖ ^ 2) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.le_sqrt_of_sq_le ?_
    linarith
  calc ‖z‖ ^ m = ‖z‖ ^ (m : ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ ((1 + ‖z‖ ^ 2) ^ (1 / 2 : ℝ)) ^ (m : ℝ) := Real.rpow_le_rpow (norm_nonneg _) h1 (Nat.cast_nonneg _)
    _ = (1 + ‖z‖ ^ 2) ^ ((m : ℝ) / 2) := by
        rw [← Real.rpow_mul hR0.le]
        ring_nf

private theorem norm_G_le (a b : ℕ) {σ : ℝ} {w : ℂ} (hw : σ ≤ w.re) (ζ z : ℂ) :
    ‖G a b w ζ z‖ ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2) := by
  rw [norm_G]
  have hR0 : 0 < 1 + ‖z‖ ^ 2 := one_add_norm_sq_pos z
  have h2 : (1 + ‖z‖ ^ 2) ^ (-w.re) ≤ (1 + ‖z‖ ^ 2) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le (one_le_one_add_norm_sq z) (by linarith)
  calc ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re)
      ≤ (1 + ‖z‖ ^ 2) ^ (((a + b : ℕ) : ℝ) / 2) * (1 + ‖z‖ ^ 2) ^ (-σ) :=
        mul_le_mul (norm_pow_le_bracket (a + b) z) h2 (Real.rpow_nonneg hR0.le _) (Real.rpow_nonneg hR0.le _)
    _ = (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2) := by
        rw [← Real.rpow_add hR0]
        ring_nf

private theorem integrable_bracket (a b : ℕ) {σ : ℝ} (hσ : ((a + b : ℕ) : ℝ) / 2 + 1 < σ) :
    Integrable (fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2)) := by
  refine integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) ?_
  rw [Complex.finrank_real_complex]
  push_cast at hσ ⊢
  linarith

private theorem continuous_character : Continuous (fun q : ℂ × ℂ =>
    Complex.exp (-(((4 * Real.pi * (q.1 * q.2).re : ℝ) : ℂ) * Complex.I))) := by
  have h1 : Continuous (fun q : ℂ × ℂ => (4 * Real.pi * (q.1 * q.2).re : ℝ)) :=
    continuous_const.mul (Complex.continuous_re.comp (continuous_fst.mul continuous_snd))
  have h2 : Continuous (fun q : ℂ × ℂ => (((4 * Real.pi * (q.1 * q.2).re : ℝ) : ℂ))) :=
    Complex.continuous_ofReal.comp h1
  exact Complex.continuous_exp.comp ((h2.mul continuous_const).neg)

private theorem continuous_bracketC : Continuous (fun z : ℂ => (((1 + ‖z‖ ^ 2 : ℝ) : ℂ))) :=
  Complex.continuous_ofReal.comp (continuous_const.add (continuous_norm.pow 2))

private theorem bracketC_mem_slitPlane (z : ℂ) : (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ∈ Complex.slitPlane :=
  Complex.ofReal_mem_slitPlane.2 (one_add_norm_sq_pos z)

private theorem continuous_G (a b : ℕ) : Continuous (fun q : ℂ × ℂ × ℂ => G a b q.1 q.2.1 q.2.2) := by
  have h1 : Continuous (fun q : ℂ × ℂ × ℂ => q.2.2 ^ a * conj q.2.2 ^ b) :=
    (continuous_snd.snd.pow a).mul ((Complex.continuous_conj.comp continuous_snd.snd).pow b)
  have h2 : Continuous (fun q : ℂ × ℂ × ℂ => (((1 + ‖q.2.2‖ ^ 2 : ℝ) : ℂ)) ^ (-q.1)) :=
    Continuous.cpow (continuous_bracketC.comp continuous_snd.snd) continuous_fst.neg
      (fun q => bracketC_mem_slitPlane q.2.2)
  have h3 : Continuous (fun q : ℂ × ℂ × ℂ => Complex.exp (-(((4 * Real.pi * (q.2.1 * q.2.2).re : ℝ) : ℂ) * Complex.I))) :=
    continuous_character.comp continuous_snd
  exact (h1.mul h2).mul h3

private theorem continuous_G_z (a b : ℕ) (w ζ : ℂ) : Continuous (fun z => G a b w ζ z) := by
  have h1 : Continuous (fun z : ℂ => z ^ a * conj z ^ b) :=
    (continuous_id.pow a).mul (Complex.continuous_conj.pow b)
  have h2 : Continuous (fun z : ℂ => (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)) :=
    continuous_bracketC.cpow continuous_const bracketC_mem_slitPlane
  have h3 : Continuous (fun z : ℂ => Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) :=
    continuous_character.comp (Continuous.prodMk continuous_const continuous_id)
  exact (h1.mul h2).mul h3

private theorem continuous_G_wζ (a b : ℕ) (z : ℂ) : Continuous (fun p : ℂ × ℂ => G a b p.1 p.2 z) := by
  have h1 : Continuous (fun _ : ℂ × ℂ => z ^ a * conj z ^ b) := continuous_const
  have h2 : Continuous (fun p : ℂ × ℂ => (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-p.1)) :=
    Continuous.const_cpow continuous_fst.neg
      (Or.inl (Complex.ofReal_ne_zero.2 (one_add_norm_sq_pos z).ne'))
  have h3 : Continuous (fun p : ℂ × ℂ => Complex.exp (-(((4 * Real.pi * (p.2 * z).re : ℝ) : ℂ) * Complex.I))) :=
    continuous_character.comp (Continuous.prodMk continuous_snd continuous_const)
  exact (h1.mul h2).mul h3

private theorem integrable_G (a b : ℕ) {w : ℂ} (hw : ((a + b : ℕ) : ℝ) / 2 + 1 < w.re) (ζ : ℂ) :
    Integrable (fun z => G a b w ζ z) :=
  (integrable_bracket a b hw).mono' (continuous_G_z a b w ζ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => norm_G_le a b le_rfl ζ z)

private theorem isOpen_halfPlane (σ : ℝ) : IsOpen {w : ℂ | σ < w.re} := isOpen_lt continuous_const Complex.continuous_re

private theorem continuousOn_integral_G (a b : ℕ) :
    ContinuousOn (fun p : ℂ × ℂ => ∫ z, G a b p.1 p.2 z)
      ({w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ×ˢ Set.univ) := by
  intro p hp
  obtain ⟨hp1, -⟩ := hp
  simp only [Set.mem_setOf_eq] at hp1
  set σ : ℝ := (((a + b : ℕ) : ℝ) / 2 + 1 + p.1.re) / 2 with hσdef
  have hσ : ((a + b : ℕ) : ℝ) / 2 + 1 < σ := by rw [hσdef]; linarith
  have hσp : σ < p.1.re := by rw [hσdef]; linarith
  have hS : IsOpen ({w : ℂ | σ < w.re} ×ˢ (Set.univ : Set ℂ)) := (isOpen_halfPlane σ).prod isOpen_univ
  have hcont : ContinuousOn (fun p : ℂ × ℂ => ∫ z, G a b p.1 p.2 z) ({w : ℂ | σ < w.re} ×ˢ Set.univ) := by
    refine continuousOn_of_dominated (bound := fun z : ℂ => (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2))
      (fun x _ => (continuous_G_z a b x.1 x.2).aestronglyMeasurable) (fun x hx => ?_) (integrable_bracket a b hσ)
      (Filter.Eventually.of_forall fun z => (continuous_G_wζ a b z).continuousOn)
    obtain ⟨hx1, -⟩ := hx
    exact Filter.Eventually.of_forall fun z => norm_G_le a b (le_of_lt hx1) x.2 z
  exact (hcont.continuousAt (hS.mem_nhds ⟨hσp, Set.mem_univ _⟩)).continuousWithinAt

private def G' (a b : ℕ) (w ζ z : ℂ) : ℂ :=
  z ^ a * conj z ^ b * ((((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w) * Complex.log (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) * (-1))
    * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))

private theorem hasDerivAt_G (a b : ℕ) (w ζ z : ℂ) : HasDerivAt (fun w => G a b w ζ z) (G' a b w ζ z) w := by
  unfold G G'
  have hR : (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.2 (one_add_norm_sq_pos z).ne'
  have h := ((Complex.hasStrictDerivAt_const_cpow (Or.inl hR)).hasDerivAt.comp w (hasDerivAt_id w).neg)
  exact (h.const_mul _).mul_const _

private theorem norm_G' (a b : ℕ) (w ζ z : ℂ) :
    ‖G' a b w ζ z‖ = ‖z‖ ^ (a + b) * (1 + ‖z‖ ^ 2) ^ (-w.re) * Real.log (1 + ‖z‖ ^ 2) := by
  unfold G'
  have hR0 := one_add_norm_sq_pos z
  rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos hR0, Complex.neg_re, norm_character, mul_one, pow_add,
    ← Complex.ofReal_log hR0.le, Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg (one_le_one_add_norm_sq z)),
    norm_neg, norm_one, mul_one]
  ring

private theorem continuous_G'_z (a b : ℕ) (w ζ : ℂ) : Continuous (fun z => G' a b w ζ z) := by
  have h1 : Continuous (fun z : ℂ => z ^ a * conj z ^ b) :=
    (continuous_id.pow a).mul (Complex.continuous_conj.pow b)
  have h2 : Continuous (fun z : ℂ => (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w) * Complex.log (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) * (-1)) :=
    ((continuous_bracketC.cpow continuous_const bracketC_mem_slitPlane).mul
      (continuous_bracketC.clog bracketC_mem_slitPlane)).mul continuous_const
  have h3 : Continuous (fun z : ℂ => Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))) :=
    continuous_character.comp (Continuous.prodMk continuous_const continuous_id)
  exact (h1.mul h2).mul h3

private theorem norm_G'_le (a b : ℕ) {σ ε : ℝ} (hε : 0 < ε) {w : ℂ} (hw : σ ≤ w.re) (ζ z : ℂ) :
    ‖G' a b w ζ z‖ ≤ ε⁻¹ * (1 + ‖z‖ ^ 2) ^ (-(2 * (σ - ε) - ((a + b : ℕ) : ℝ)) / 2) := by
  rw [norm_G', ← norm_G a b w ζ z]
  have hR0 := one_add_norm_sq_pos z
  have hlog : Real.log (1 + ‖z‖ ^ 2) ≤ (1 + ‖z‖ ^ 2) ^ ε / ε := Real.log_le_rpow_div hR0.le hε
  calc ‖G a b w ζ z‖ * Real.log (1 + ‖z‖ ^ 2)
      ≤ (1 + ‖z‖ ^ 2) ^ (-(2 * σ - ((a + b : ℕ) : ℝ)) / 2) * ((1 + ‖z‖ ^ 2) ^ ε / ε) :=
        mul_le_mul (norm_G_le a b hw ζ z) hlog (Real.log_nonneg (one_le_one_add_norm_sq z)) (Real.rpow_nonneg hR0.le _)
    _ = ε⁻¹ * (1 + ‖z‖ ^ 2) ^ (-(2 * (σ - ε) - ((a + b : ℕ) : ℝ)) / 2) := by
        rw [show -(2 * (σ - ε) - ((a + b : ℕ) : ℝ)) / 2 = -(2 * σ - ((a + b : ℕ) : ℝ)) / 2 + ε by ring,
          Real.rpow_add hR0]
        ring

private theorem differentiableOn_integral_G (a b : ℕ) (ζ : ℂ) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ z, G a b w ζ z) {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} := by
  intro w₀ hw₀
  simp only [Set.mem_setOf_eq] at hw₀
  set t : ℝ := ((a + b : ℕ) : ℝ) / 2 + 1 with ht
  set σ : ℝ := (t + w₀.re) / 2 with hσdef
  set ε : ℝ := (σ - t) / 2 with hεdef
  have hσ : t < σ := by rw [hσdef]; linarith
  have hσw : σ < w₀.re := by rw [hσdef]; linarith
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hσε : ((a + b : ℕ) : ℝ) / 2 + 1 < σ - ε := by rw [hεdef]; linarith
  have hs : {w : ℂ | σ < w.re} ∈ 𝓝 w₀ := (isOpen_halfPlane σ).mem_nhds hσw
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure ℂ))
    (F := fun w z => G a b w ζ z) (F' := fun w z => G' a b w ζ z) (x₀ := w₀)
    (bound := fun z : ℂ => ε⁻¹ * (1 + ‖z‖ ^ 2) ^ (-(2 * (σ - ε) - ((a + b : ℕ) : ℝ)) / 2)) hs
    (Filter.Eventually.of_forall fun w => (continuous_G_z a b w ζ).aestronglyMeasurable)
    (integrable_G a b (by linarith) ζ) (continuous_G'_z a b w₀ ζ).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z w hw => norm_G'_le a b hε (le_of_lt hw) ζ z)
    ((integrable_bracket a b hσε).const_mul _)
    (Filter.Eventually.of_forall fun z w _ => hasDerivAt_G a b w ζ z)
  exact key.2.differentiableAt.differentiableWithinAt

private def BddSmooth (f : ℂ → ℂ) : Prop :=
  ContDiff ℝ ∞ f ∧ ∀ n : ℕ, ∃ C : ℝ, ∀ z : ℂ, ‖iteratedFDeriv ℝ n f z‖ ≤ C

private theorem bddSmooth_const (c : ℂ) : BddSmooth (fun _ : ℂ => c) := by
  refine ⟨contDiff_const, fun n => ⟨‖c‖, fun z => ?_⟩⟩
  rcases n with _ | n
  · rw [norm_iteratedFDeriv_zero]
  · rw [iteratedFDeriv_succ_const]
    simp

private theorem BddSmooth.mul {f g : ℂ → ℂ} (hf : BddSmooth f) (hg : BddSmooth g) : BddSmooth (fun z => f z * g z) := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  choose Cf hCf using hf.2
  choose Cg hCg using hg.2
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * Cf i * Cg (n - i), fun z => ?_⟩
  refine (norm_iteratedFDeriv_mul_le (n := n) hf.1 hg.1 z (mod_cast le_top)).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  have h0 : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
  refine mul_le_mul (mul_le_mul_of_nonneg_left (hCf i z) h0) (hCg (n - i) z) (norm_nonneg _) ?_
  exact mul_nonneg h0 ((norm_nonneg _).trans (hCf i z))

private theorem BddSmooth.pow {f : ℂ → ℂ} (hf : BddSmooth f) : ∀ k : ℕ, BddSmooth (fun z => f z ^ k)
  | 0 => by
      simp only [pow_zero]
      exact bddSmooth_const 1
  | k + 1 => by
      simp only [pow_succ]
      exact (hf.pow k).mul hf

private theorem bddSmooth_kC_one (i j : Fin 2) : BddSmooth (fun z => kC 1 z i j) := by
  have hdet : (1 : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := by
    rw [Matrix.det_one]
    exact one_ne_zero
  obtain ⟨hC, hB⟩ := AutomorphicForm.ComplexIwasawa.contDiff_and_exists_bound_iteratedFDeriv_kC_apply hdet
  exact ⟨hC i j, fun n => by
    obtain ⟨C, -, h⟩ := hB n
    exact ⟨C, h i j⟩⟩

private def P (a b : ℕ) (z : ℂ) : ℂ := kC 1 z 1 1 ^ a * kC 1 z 0 0 ^ b

private theorem bddSmooth_P (a b : ℕ) : BddSmooth (P a b) :=
  ((bddSmooth_kC_one 1 1).pow a).mul ((bddSmooth_kC_one 0 0).pow b)

private def L : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun z ζ : ℂ => 2 * (ζ * z).re)
      (fun z₁ z₂ ζ => by
        simp only [Complex.mul_re, Complex.add_re, Complex.add_im]
        ring)
      (fun c z ζ => by
        simp only [Complex.real_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring)
      (fun z ζ₁ ζ₂ => by
        simp only [Complex.mul_re, Complex.add_re, Complex.add_im]
        ring)
      (fun c z ζ => by
        simp only [Complex.real_smul, smul_eq_mul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
        ring))
    2 (fun z ζ => by
      rw [LinearMap.mk₂_apply, Real.norm_eq_abs, abs_mul, abs_of_pos (two_pos : (0 : ℝ) < 2)]
      calc 2 * |(ζ * z).re| ≤ 2 * ‖ζ * z‖ := by
            gcongr
            exact Complex.abs_re_le_norm _
        _ = 2 * ‖z‖ * ‖ζ‖ := by rw [norm_mul]; ring)

private theorem L_apply (z ζ : ℂ) : L z ζ = 2 * (ζ * z).re := by
  simp only [L, LinearMap.mkContinuous₂_apply, LinearMap.mk₂_apply]

private theorem L_coercive (ξ : ℂ) : ∃ v : ℂ, ‖v‖ ≤ 1 ∧ 2 * ‖ξ‖ ≤ ‖L v ξ‖ := by
  by_cases hξ : ξ = 0
  · refine ⟨0, by simp, ?_⟩
    rw [hξ, norm_zero, mul_zero]
    exact norm_nonneg _
  · have hn : (‖ξ‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 hξ)
    refine ⟨conj ξ / (‖ξ‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hξ)]
    · rw [L_apply]
      have h : ξ * (conj ξ / (‖ξ‖ : ℂ)) = (‖ξ‖ : ℂ) := by
        rw [mul_div_assoc', Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast
        rw [sq, mul_div_assoc, div_self hn, mul_one]
      rw [h, Complex.ofReal_re, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem radC_one (z : ℂ) : radC 1 z = Real.sqrt (1 + ‖z‖ ^ 2) := by
  simp [radC, botP, botQ, Complex.normSq_eq_norm_sq]

private theorem kC_one_apply_one_one (z : ℂ) : kC 1 z 1 1 = z / (radC 1 z : ℂ) := by
  simp [kC, botQ]

private theorem kC_one_apply_zero_zero (z : ℂ) : kC 1 z 0 0 = conj z / (radC 1 z : ℂ) := by
  simp [kC, botQ]

private theorem weight_identity (a b : ℕ) (w z : ℂ) :
    ((radC 1 z : ℂ)) ^ (-(2 * w - ((a + b : ℕ) : ℂ))) * P a b z
      = z ^ a * conj z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w) := by
  rw [P, kC_one_apply_one_one, kC_one_apply_zero_zero, radC_one]
  set R : ℝ := 1 + ‖z‖ ^ 2 with hRdef
  have hR0 : 0 < R := one_add_norm_sq_pos z
  set r : ℝ := Real.sqrt R with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.2 hR0
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr0.ne'
  have hR' : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hR0.ne'
  have hrR : (r : ℂ) ^ (-2 * w) = (R : ℂ) ^ (-w) := by
    rw [Complex.cpow_def_of_ne_zero hr', Complex.cpow_def_of_ne_zero hR', ← Complex.ofReal_log hr0.le,
      ← Complex.ofReal_log hR0.le, hrdef, Real.log_sqrt hR0.le]
    congr 1
    push_cast
    ring
  have hsplit : (r : ℂ) ^ (-(2 * w - ((a + b : ℕ) : ℂ))) = (R : ℂ) ^ (-w) * ((r : ℂ) ^ a * (r : ℂ) ^ b) := by
    rw [show -(2 * w - ((a + b : ℕ) : ℂ)) = -2 * w + ((a + b : ℕ) : ℂ) by ring, Complex.cpow_add _ _ hr',
      Complex.cpow_natCast, ← pow_add, hrR]
  rw [hsplit, div_pow, div_pow]
  field_simp

private theorem fourier_integrand_eq (a b : ℕ) (w ζ z : ℂ) :
    𝐞 (-(L z ζ)) • (((radC 1 z : ℂ)) ^ (-(2 * w - ((a + b : ℕ) : ℂ))) * P a b z) = G a b w ζ z := by
  rw [weight_identity, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, L_apply, G, mul_comm]
  congr 2
  push_cast
  ring

private theorem fourierIntegral_eq (a b : ℕ) (w ζ : ℂ) :
    VectorFourier.fourierIntegral 𝐞 volume L.toLinearMap₁₂
        (fun z => ((radC 1 z : ℂ)) ^ (-(2 * w - ((a + b : ℕ) : ℂ))) * P a b z) ζ
      = ∫ z, G a b w ζ z := by
  unfold VectorFourier.fourierIntegral
  congr 1
  funext z
  rw [ContinuousLinearMap.toLinearMap₁₂_apply]
  exact fourier_integrand_eq a b w ζ z

private theorem decay (a b : ℕ) (K : Set ℂ) (hK : IsCompact K) (hKsub : K ⊆ {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re})
    (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ w ∈ K, ∀ ζ : ℂ, ‖∫ z, G a b w ζ z‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ)) := by
  obtain ⟨hPC, hPB⟩ := bddSmooth_P a b
  have hPB' : ∀ n : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ g ∈ ({1} : Set (Matrix (Fin 2) (Fin 2) ℂ)), ∀ z : ℂ,
      ‖iteratedFDeriv ℝ n ((fun _ : Matrix (Fin 2) (Fin 2) ℂ => P a b) g) z‖ ≤ C := by
    intro n
    obtain ⟨C, hC⟩ := hPB n
    exact ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun g _ z => (hC z).trans (le_max_left _ _)⟩
  have hdet : ∀ g ∈ ({1} : Set (Matrix (Fin 2) (Fin 2) ℂ)), g.det ≠ 0 := by
    intro g hg
    rw [Set.mem_singleton_iff.1 hg, Matrix.det_one]
    exact one_ne_zero
  have hUc : IsCompact ((fun w : ℂ => 2 * w - ((a + b : ℕ) : ℂ)) '' K) :=
    hK.image ((continuous_const.mul continuous_id).sub continuous_const)
  have hU2 : ∀ u ∈ (fun w : ℂ => 2 * w - ((a + b : ℕ) : ℂ)) '' K, 2 < u.re := by
    rintro u ⟨w, hw, rfl⟩
    have h := hKsub hw
    simp only [Set.mem_setOf_eq] at h
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.natCast_re, zero_mul,
      sub_zero]
    push_cast at h ⊢
    linarith
  obtain ⟨C, hC0, hC⟩ :=
    AutomorphicForm.ComplexIwasawa.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact
      {1} isCompact_singleton hdet _ hUc hU2 (fun _ => P a b) (fun _ _ => hPC) hPB' L two_pos L_coercive N
  refine ⟨C, hC0, fun w hw ζ => ?_⟩
  have h := hC 1 rfl (2 * w - ((a + b : ℕ) : ℂ)) ⟨w, hw, rfl⟩ ζ
  rwa [fourierIntegral_eq a b w ζ] at h

end HARCHC

end

open HARCHC in
theorem solution (a b : ℕ) :
    let j : ℂ → ℂ → ℂ := fun w ζ => ∫ z : ℂ, z ^ a * (starRingEnd ℂ) z ^ b * (((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) ^ (-w)
          * Complex.exp (-(((4 * Real.pi * (ζ * z).re : ℝ) : ℂ) * Complex.I))
    ContinuousOn (fun p : ℂ × ℂ => j p.1 p.2) ({w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} ×ˢ Set.univ) ∧
    (∀ ζ : ℂ, DifferentiableOn ℂ (fun w : ℂ => j w ζ) {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re}) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {w : ℂ | ((a + b : ℕ) : ℝ) / 2 + 1 < w.re} → ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ w ∈ K, ∀ ζ : ℂ, ‖j w ζ‖ ≤ C * (1 + ‖ζ‖) ^ (-(N : ℝ))) := by
  intro j
  simp only [j]
  exact ⟨continuousOn_integral_G a b, differentiableOn_integral_G a b, fun K hK hKsub N => decay a b K hK hKsub N⟩

end S_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral
end P2MW
export P2MW.S_AutomorphicForm_ComplexIwasawa_continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral (solution)
