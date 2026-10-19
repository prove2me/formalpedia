-- Prove2me | solution 1 for AMPUniversality.Universal.eq_4_15
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:53:46.209067+00:00
-- url     : https://prove2.me/submissions/68a0a411-aa09-49b6-9eaa-b756e3915c6a

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

/-- Lemma: `x^s ≤ (s/e)^s e^x` for `x > 0`. -/
lemma amp12_aux (s x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    x ^ s ≤ (s / Real.exp 1) ^ s * Real.exp x := by
  have hse : 0 < s / Real.exp 1 := div_pos hs (Real.exp_pos 1)
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hse, ← Real.exp_add, Real.exp_le_exp]
  have hl : Real.log (x / s) ≤ x / s - 1 := Real.log_le_sub_one_of_pos (div_pos hx hs)
  rw [Real.log_div hx.ne' hs.ne'] at hl
  rw [Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp]
  have h2 : s * (Real.log x - Real.log s) ≤ s * (x / s - 1) := mul_le_mul_of_nonneg_left hl hs.le
  have h3 : s * (x / s - 1) = x - s := by field_simp
  nlinarith [h2, h3]

/-- Pointwise bound `|y|^s ≤ M (e^{ty} + e^{-ty})` with `M = (s/(e t))^s`. -/
lemma amp_pointwise (s t y : ℝ) (hs : 0 < s) (ht : 0 < t) :
    |y| ^ s ≤ ((s / Real.exp 1) ^ s * (t ^ s)⁻¹) * (Real.exp (t * y) + Real.exp (-t * y)) := by
  have hM : 0 ≤ (s / Real.exp 1) ^ s * (t ^ s)⁻¹ := by positivity
  have hts : 0 < t ^ s := Real.rpow_pos_of_pos ht s
  rcases eq_or_lt_of_le (abs_nonneg y) with h0 | hpos
  · rw [← h0, Real.zero_rpow hs.ne']
    positivity
  · have h1 := amp12_aux s (t * |y|) hs (by positivity)
    rw [Real.mul_rpow ht.le (abs_nonneg y)] at h1
    have h2 : |y| ^ s ≤ ((s / Real.exp 1) ^ s * (t ^ s)⁻¹) * Real.exp (t * |y|) := by
      have : |y| ^ s = (t ^ s)⁻¹ * (t ^ s * |y| ^ s) := by field_simp
      rw [this]
      calc (t ^ s)⁻¹ * (t ^ s * |y| ^ s) ≤ (t ^ s)⁻¹ * ((s / Real.exp 1) ^ s * Real.exp (t * |y|)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = _ := by ring
    refine h2.trans ?_
    apply mul_le_mul_of_nonneg_left _ hM
    rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; have := Real.exp_pos (-t * y); linarith
    · rw [h]; have := Real.exp_pos (t * y)
      have e : t * -y = -t * y := by ring
      rw [e]; linarith

lemma amp_const (s c : ℝ) (hs : 0 < s) (hc : 0 < c) :
    (s / Real.exp 1) ^ s * ((Real.sqrt (s / c)) ^ s)⁻¹ * Real.exp (s / 2)
      = c ^ (s / 2) * (s / Real.exp 1) ^ (s / 2) := by
  have hse : 0 < s / Real.exp 1 := div_pos hs (Real.exp_pos 1)
  have hsq : 0 < Real.sqrt (s / c) := Real.sqrt_pos.2 (div_pos hs hc)
  have hL : 0 < (s / Real.exp 1) ^ s * ((Real.sqrt (s / c)) ^ s)⁻¹ * Real.exp (s / 2) := by positivity
  have hR : 0 < c ^ (s / 2) * (s / Real.exp 1) ^ (s / 2) := by positivity
  apply Real.log_injOn_pos (Set.mem_Ioi.2 hL) (Set.mem_Ioi.2 hR)
  have e1 : Real.log ((s / Real.exp 1) ^ s * ((Real.sqrt (s / c)) ^ s)⁻¹ * Real.exp (s / 2))
      = s * (Real.log s - 1) - s * (Real.log (s / c) / 2) + s / 2 := by
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul (by positivity) (by positivity),
      Real.log_inv, Real.log_rpow hse, Real.log_rpow hsq, Real.log_exp,
      Real.log_sqrt (div_pos hs hc).le, Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp]
    ring
  have e2 : Real.log (c ^ (s / 2) * (s / Real.exp 1) ^ (s / 2))
      = s / 2 * Real.log c + s / 2 * (Real.log s - 1) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hc, Real.log_rpow hse,
      Real.log_div hs.ne' (Real.exp_pos 1).ne', Real.log_exp]
  rw [e1, e2, Real.log_div hs.ne' hc.ne']
  ring

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (C : ℝ) (hC : 0 < C) (N : ℕ) (hN : 0 < N)
    (hX : HasSubgaussianMGF X (Real.toNNReal (C / N)) P) (s : ℝ) (hs : 0 < s) :
    Integrable (fun ω => |X ω| ^ s) P ∧
      ∫ ω, |X ω| ^ s ∂P ≤
        2 * C ^ (s / 2) * (s / Real.exp 1) ^ (s / 2) * (N : ℝ) ^ (-(s / 2)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < C / N := div_pos hC hNr
  have hcc : ((Real.toNNReal (C / N) : NNReal) : ℝ) = C / N := Real.coe_toNNReal _ hc.le
  set t : ℝ := Real.sqrt (s / (C / N)) with ht_def
  have ht : 0 < t := Real.sqrt_pos.2 (div_pos hs hc)
  set M : ℝ := (s / Real.exp 1) ^ s * (t ^ s)⁻¹ with hM_def
  have hMpos : 0 < M := by positivity
  have hpt : ∀ ω, |X ω| ^ s ≤ M * (Real.exp (t * X ω) + Real.exp (-t * X ω)) :=
    fun ω => amp_pointwise s t (X ω) hs ht
  have i1 := hX.integrable_exp_mul t
  have i2 := hX.integrable_exp_mul (-t)
  have hint : Integrable (fun ω => M * (Real.exp (t * X ω) + Real.exp (-t * X ω))) P :=
    (i1.add i2).const_mul M
  have hmeas : AEStronglyMeasurable (fun ω => |X ω| ^ s) P := by
    have : AEMeasurable (fun ω => |X ω| ^ s) P :=
      (hX.aemeasurable.abs).pow_const s
    exact this.aestronglyMeasurable
  have hint2 : Integrable (fun ω => |X ω| ^ s) P := by
    refine hint.mono' hmeas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt ω
  refine ⟨hint2, ?_⟩
  calc ∫ ω, |X ω| ^ s ∂P ≤ ∫ ω, M * (Real.exp (t * X ω) + Real.exp (-t * X ω)) ∂P :=
        integral_mono hint2 hint hpt
    _ = M * (mgf X P t + mgf X P (-t)) := by
        rw [integral_const_mul, integral_add i1 i2]; rfl
    _ ≤ M * (Real.exp (((Real.toNNReal (C / N) : NNReal) : ℝ) * t ^ 2 / 2) +
          Real.exp (((Real.toNNReal (C / N) : NNReal) : ℝ) * (-t) ^ 2 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ hMpos.le
        exact add_le_add (hX.mgf_le t) (hX.mgf_le (-t))
    _ = 2 * (M * Real.exp (s / 2)) := by
        have h1 : ((Real.toNNReal (C / N) : NNReal) : ℝ) * t ^ 2 / 2 = s / 2 := by
          rw [hcc, ht_def, Real.sq_sqrt (div_pos hs hc).le]
          field_simp
        rw [neg_sq, h1]; ring
    _ = 2 * (C / N) ^ (s / 2) * (s / Real.exp 1) ^ (s / 2) := by
        have := amp_const s (C / N) hs hc
        rw [← ht_def] at this
        rw [hM_def, this]; ring
    _ = _ := by
        rw [Real.div_rpow hC.le hNr.le, Real.rpow_neg hNr.le]
        field_simp
