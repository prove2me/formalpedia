-- Prove2me | solution 1 for Arxivcond_mat_0004049.laguerre_normalization_pos_finite
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T14:38:34.02807+00:00
-- url     : https://prove2.me/submissions/927aab67-a299-4a3c-ae38-83fa66e667cd

import Mathlib
import Definitions.Def_Arxivcond_mat_0004049_Basic

open MeasureTheory Set

namespace Arxivcond_mat_0004049

/-! ### Finiteness: a product majorant -/

private lemma laguerreWeight_measurable (N : ℕ) (γ : ℝ) : Measurable (laguerreWeight N γ) := by
  unfold laguerreWeight
  refine Measurable.ennreal_ofReal (Measurable.mul ?_ ?_)
  · refine Finset.measurable_prod _ fun i _ => Finset.measurable_prod _ fun j _ => ?_
    by_cases h : i < j
    · simp only [h, if_true]; fun_prop
    · simp only [h, if_false]; exact measurable_const
  · exact Finset.measurable_prod _ fun k _ =>
      Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply k)) (by fun_prop)
        measurable_const

/-- One-coordinate majorant of the Laguerre weight: `(1+x)^{2N} e^{-γ(N+1)x}` on `x > 0`. -/
private noncomputable def lagBound (N : ℕ) (γ x : ℝ) : ℝ :=
  if 0 < x then (1 + x) ^ (2 * N) * Real.exp (-γ * ((N : ℝ) + 1) * x) else 0

private lemma lagBound_nonneg (N : ℕ) (γ x : ℝ) : 0 ≤ lagBound N γ x := by
  unfold lagBound; split_ifs with h
  · exact mul_nonneg (pow_nonneg (by linarith) _) (Real.exp_pos _).le
  · exact le_rfl

private lemma lagBound_integrable (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    Integrable (lagBound N γ) := by
  have hb : 0 < γ * ((N : ℝ) + 1) := by positivity
  have hfun : lagBound N γ = (Ioi (0 : ℝ)).indicator
      (fun x => ∑ k ∈ Finset.range (2 * N + 1),
        ((2 * N).choose k : ℝ) * (x ^ (k : ℝ) * Real.exp (-(γ * ((N : ℝ) + 1)) * x ^ (1 : ℝ)))) := by
    funext x
    unfold lagBound
    by_cases hx : 0 < x
    · rw [if_pos hx, indicator_of_mem (show x ∈ Ioi 0 from hx), add_comm (1 : ℝ) x, add_pow,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.rpow_natCast, Real.rpow_one, one_pow, mul_one]
      ring_nf
    · rw [if_neg hx, indicator_of_notMem (show x ∉ Ioi 0 from hx)]
  rw [hfun, integrable_indicator_iff measurableSet_Ioi]
  refine integrable_finsetSum _ fun k _ => Integrable.const_mul ?_ _
  exact integrableOn_rpow_mul_exp_neg_mul_rpow
    (by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith) one_pos hb

private lemma laguerreWeight_le_prod (N : ℕ) (γ : ℝ) (μ : Fin N → ℝ) :
    laguerreWeight N γ μ ≤ ENNReal.ofReal (∏ k, lagBound N γ (μ k)) := by
  unfold laguerreWeight
  refine ENNReal.ofReal_le_ofReal ?_
  by_cases hpos : ∀ k, 0 < μ k
  · have hE : (∏ k, if 0 < μ k then Real.exp (-γ * ((N : ℝ) + 1) * μ k) else 0) =
        ∏ k, Real.exp (-γ * ((N : ℝ) + 1) * μ k) :=
      Finset.prod_congr rfl fun k _ => if_pos (hpos k)
    have hB : (∏ k, lagBound N γ (μ k)) =
        (∏ k, (1 + μ k) ^ (2 * N)) * ∏ k, Real.exp (-γ * ((N : ℝ) + 1) * μ k) := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => if_pos (hpos k)
    rw [hE, hB]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun k _ => (Real.exp_pos _).le)
    have hV : (∏ i, ∏ j, if i < j then |μ i - μ j| else 1) ≤
        ∏ i : Fin N, ∏ j : Fin N, ((1 + μ i) * (1 + μ j)) := by
      refine Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => ?_) fun i _ => ?_
      · split_ifs <;> positivity
      refine Finset.prod_le_prod (fun j _ => ?_) fun j _ => ?_
      · split_ifs <;> positivity
      have hi := hpos i; have hj := hpos j
      split_ifs
      · rw [abs_le]; constructor <;> nlinarith
      · nlinarith
    refine hV.trans (le_of_eq ?_)
    simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_pow]
    ring
  · push Not at hpos
    obtain ⟨k, hk⟩ := hpos
    have : (∏ k, if 0 < μ k then Real.exp (-γ * ((N : ℝ) + 1) * μ k) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (not_lt.2 hk))
    rw [this, mul_zero]
    exact Finset.prod_nonneg fun k _ => lagBound_nonneg N γ (μ k)

/-- The normalization `∫ laguerreWeight` of eq. (7) is finite. -/
private lemma laguerre_norm_ne_top (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∫⁻ μ, laguerreWeight N γ μ ≠ ⊤ := by
  refine (lt_of_le_of_lt (lintegral_mono fun μ => laguerreWeight_le_prod N γ μ) ?_).ne
  have := Integrable.fintype_prod (μ := fun _ : Fin N => (volume : Measure ℝ))
    (fun _ => lagBound_integrable N γ hγ)
  rw [← volume_pi] at this
  exact this.lintegral_lt_top

/-! ### Positivity: a lower bound on a box -/

/-- The box `∏_k (2k+2, 2k+3)`: coordinates are positive, bounded by `2N+3`, and pairwise
separated by at least `1`. -/
private def lagBox (N : ℕ) : Set (Fin N → ℝ) :=
  Set.pi univ fun k : Fin N => Ioo (2 * ((k : ℕ) : ℝ) + 2) (2 * ((k : ℕ) : ℝ) + 3)

private lemma laguerreWeight_ge_on_box (N : ℕ) (γ : ℝ) (hγ : 0 < γ) (μ : Fin N → ℝ)
    (hμ : μ ∈ lagBox N) :
    ENNReal.ofReal (Real.exp (-(γ * ((N : ℝ) + 1)) * (2 * (N : ℝ) + 3)) ^ N) ≤
      laguerreWeight N γ μ := by
  have hk : ∀ k : Fin N, 2 * ((k : ℕ) : ℝ) + 2 < μ k ∧ μ k < 2 * ((k : ℕ) : ℝ) + 3 := fun k =>
    Set.mem_univ_pi.1 hμ k
  have hc : 0 ≤ γ * ((N : ℝ) + 1) := by positivity
  unfold laguerreWeight
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : ∀ i j : Fin N, 1 ≤ (if i < j then |μ i - μ j| else (1 : ℝ)) := by
    intro i j
    split_ifs with hij
    · have hij' : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
      rw [abs_sub_comm, le_abs]; left; linarith [(hk i).2, (hk j).1]
    · exact le_rfl
  have hV : 1 ≤ ∏ i, ∏ j, if i < j then |μ i - μ j| else 1 :=
    calc (1 : ℝ) = ∏ _i : Fin N, ∏ _j : Fin N, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod
          (fun _ _ => Finset.prod_nonneg fun _ _ => zero_le_one)
          fun i _ => Finset.prod_le_prod (fun _ _ => zero_le_one) fun j _ => h1 i j
  have hEx : Real.exp (-(γ * ((N : ℝ) + 1)) * (2 * (N : ℝ) + 3)) ^ N ≤
      ∏ k, if 0 < μ k then Real.exp (-γ * ((N : ℝ) + 1) * μ k) else 0 :=
    calc _ = ∏ _k : Fin N, Real.exp (-(γ * ((N : ℝ) + 1)) * (2 * (N : ℝ) + 3)) := by simp
      _ ≤ _ := by
        refine Finset.prod_le_prod (fun _ _ => (Real.exp_pos _).le) fun k _ => ?_
        have hk0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
        have hkN : ((k : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast k.isLt
        rw [if_pos (by linarith [(hk k).1]), Real.exp_le_exp]
        have : μ k ≤ 2 * (N : ℝ) + 3 := by linarith [(hk k).2]
        nlinarith
  calc _ = 1 * Real.exp (-(γ * ((N : ℝ) + 1)) * (2 * (N : ℝ) + 3)) ^ N := (one_mul _).symm
    _ ≤ _ := mul_le_mul hV hEx (by positivity) (by linarith)

/-- The normalization `∫ laguerreWeight` of eq. (7) is positive. -/
private lemma laguerre_norm_ne_zero (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    ∫⁻ μ, laguerreWeight N γ μ ≠ 0 := by
  have hbox : MeasurableSet (lagBox N) := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hvol : volume (lagBox N) = 1 := by
    rw [lagBox, volume_pi, Measure.pi_pi]
    norm_num [Real.volume_Ioo]
  refine (lt_of_lt_of_le ?_ (lintegral_mono fun μ =>
    (show (lagBox N).indicator (fun _ => ENNReal.ofReal
        (Real.exp (-(γ * ((N : ℝ) + 1)) * (2 * (N : ℝ) + 3)) ^ N)) μ ≤ laguerreWeight N γ μ by
      by_cases hμ : μ ∈ lagBox N
      · rw [indicator_of_mem hμ]; exact laguerreWeight_ge_on_box N γ hγ μ hμ
      · rw [indicator_of_notMem hμ]; exact zero_le))).ne'
  rw [lintegral_indicator_const hbox, hvol, mul_one]
  exact ENNReal.ofReal_pos.2 (by positivity)

end Arxivcond_mat_0004049

open Arxivcond_mat_0004049 in
theorem solution (N : ℕ) (γ : ℝ) (hγ : 0 < γ) :
    (∫⁻ μ, laguerreWeight N γ μ) ≠ 0 ∧ (∫⁻ μ, laguerreWeight N γ μ) ≠ ⊤ :=
  ⟨laguerre_norm_ne_zero N γ hγ, laguerre_norm_ne_top N γ hγ⟩
