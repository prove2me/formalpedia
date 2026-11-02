-- Prove2me | solution 1 for AffineStorage.Ruin.Fstar_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:57:09.234219+00:00
-- url     : https://prove2.me/submissions/590a20fc-ec69-4008-8287-bb7f5c0b43db

import Mathlib
import Definitions.Def_AffineStorage_Ruin_Model
open MeasureTheory ProbabilityTheory Filter Topology
open AffineStorage.Ruin

lemma affRuinF_monoOn_Ioo {a b : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ x ∈ Set.Ioo a b, HasDerivAt h (h' x) x) (hnn : ∀ x ∈ Set.Ioo a b, 0 ≤ h' x) :
    MonotoneOn h (Set.Ioo a b) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioo a b)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (by rw [interior_Ioo]; intro x hx; exact (hd x hx).hasDerivWithinAt)
    (by rw [interior_Ioo]; exact hnn)

lemma affRuinF_monoOn_Ioi {a : ℝ} {h h' : ℝ → ℝ}
    (hd : ∀ x ∈ Set.Ioi a, HasDerivAt h (h' x) x) (hnn : ∀ x ∈ Set.Ioi a, 0 ≤ h' x) :
    MonotoneOn h (Set.Ioi a) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi a)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt)
    (by rw [interior_Ioi]; intro x hx; exact (hd x hx).hasDerivWithinAt)
    (by rw [interior_Ioi]; exact hnn)

lemma affRuinF_d_integrable (P : Params) (hS : P.Standing) :
    IntegrableOn P.d (Set.Ioi 0) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h1⟩ := hS
  by_contra h
  rw [integral_undef h] at h1
  norm_num at h1

lemma affRuinF_lst_bounds (P : Params) (hS : P.Standing) (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ P.lst s ∧ P.lst s ≤ 1 := by
  have hdi := affRuinF_d_integrable P hS
  obtain ⟨-, -, -, -, -, -, -, -, -, hdm, hd0, -, h1⟩ := hS
  have hint : IntegrableOn (fun y => Real.exp (-(s * y)) * P.d y) (Set.Ioi 0) := by
    refine Integrable.mono' hdi
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).measurable.mul
        hdm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    have he : Real.exp (-(s * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hd0 y))]
    nlinarith [hd0 y, Real.exp_pos (-(s * y))]
  constructor
  · unfold Params.lst
    exact setIntegral_nonneg measurableSet_Ioi fun y _ => mul_nonneg (Real.exp_pos _).le (hd0 y)
  · unfold Params.lst
    rw [← h1]
    refine setIntegral_mono_on hint hdi measurableSet_Ioi fun y hy => ?_
    have hy' : (0 : ℝ) < y := hy
    have he : Real.exp (-(s * y)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith [hd0 y, Real.exp_pos (-(s * y))]

theorem solution (P : Params) (hS : P.Standing) (Fs : ℝ → ℝ)
    (hF : IsPrimitiveF P Fs) :
    Tendsto (F P) atTop (𝓝 (P.p / P.r)) ∧
    Tendsto Fs atTop atTop ∧
    Tendsto Fs (𝓝[>] 0) atTop ∧
    Tendsto Fs (𝓝[<] P.μ) atTop ∧
    Tendsto Fs (𝓝[>] P.μ) atTop := by
  obtain ⟨hp, hr, hlp, hlm, hμ, hν, hα, -⟩ := id hS
  set A := (P.α + P.ν) / P.r with hA_def
  set B := P.lamPlus / P.r with hB_def
  set L := P.lamMinus / P.r with hL_def
  have hA : 0 < A := div_pos (by linarith) hr
  have hB : 0 < B := div_pos hlp hr
  have hL : 0 < L := div_pos hlm hr
  have hpr : 0 < P.p / P.r := div_pos hp hr
  have key : ∀ ϑ, F P ϑ = P.p / P.r - L * ((1 - P.lst ϑ) / ϑ) + B * (1 / (P.μ - ϑ))
      - A * (1 / ϑ) := by
    intro ϑ; simp only [F, Fbar, hA_def, hB_def, hL_def]; ring
  -- the quotient `(1 - δ(ϑ))/ϑ` lies in `[0, 1/ϑ]`
  have hq : ∀ ϑ, 0 < ϑ → 0 ≤ (1 - P.lst ϑ) / ϑ ∧ (1 - P.lst ϑ) / ϑ ≤ 1 / ϑ := by
    intro ϑ hϑ
    obtain ⟨h0, h1⟩ := affRuinF_lst_bounds P hS ϑ hϑ.le
    exact ⟨div_nonneg (by linarith) hϑ.le, div_le_div_of_nonneg_right (by linarith) hϑ.le⟩
  have hFd : ∀ η, 0 < η → η ≠ P.μ → HasDerivAt Fs (F P η) η := hF
  -- Part 1
  have h1 : Tendsto (F P) atTop (𝓝 (P.p / P.r)) := by
    have hinv : Tendsto (fun ϑ : ℝ => 1 / ϑ) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_inv_atTop_zero
    have hqt : Tendsto (fun ϑ => (1 - P.lst ϑ) / ϑ) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with ϑ hϑ using (hq ϑ hϑ).1
      · filter_upwards [eventually_gt_atTop 0] with ϑ hϑ using (hq ϑ hϑ).2
    have hm : Tendsto (fun ϑ : ℝ => 1 / (P.μ - ϑ)) atTop (𝓝 0) := by
      have : Tendsto (fun ϑ : ℝ => P.μ - ϑ) atTop atBot :=
        tendsto_atBot_add_const_left _ _ tendsto_neg_atTop_atBot
      simp only [one_div]; exact tendsto_inv_atBot_zero.comp this
    have := ((tendsto_const_nhds (x := P.p / P.r)).sub (hqt.const_mul L)).add
      (hm.const_mul B) |>.sub (hinv.const_mul A)
    simp only [mul_zero, sub_zero, add_zero] at this
    exact this.congr fun ϑ => (key ϑ).symm
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · -- Part 2: `F ≥ p/(2r)` eventually, so `Fs` grows at least linearly
    have hev : ∀ᶠ ϑ in atTop, P.p / P.r / 2 < F P ϑ :=
      h1.eventually (lt_mem_nhds (by linarith))
    obtain ⟨c, hc⟩ := eventually_atTop.mp hev
    set c' := max c (P.μ + 1)
    have hc'μ : P.μ < c' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
    have hmono : MonotoneOn (fun ϑ => Fs ϑ - P.p / P.r / 2 * ϑ) (Set.Ioi c') := by
      refine affRuinF_monoOn_Ioi (h' := fun ϑ => F P ϑ - P.p / P.r / 2) ?_ ?_
      · intro x hx
        have hx' : c' < x := hx
        have := hFd x (by linarith) (by linarith)
        exact (this.sub ((hasDerivAt_id' x).const_mul (P.p / P.r / 2))).congr_deriv (by ring)
      · intro x hx
        have hx' : c' < x := hx
        have := hc x (le_trans (le_max_left _ _) hx'.le)
        linarith
    set x0 := c' + 1
    have hx0 : x0 ∈ Set.Ioi c' := by simp [x0]
    have hlow : ∀ᶠ ϑ in atTop, Fs x0 - P.p / P.r / 2 * x0 + P.p / P.r / 2 * ϑ ≤ Fs ϑ := by
      filter_upwards [eventually_ge_atTop x0] with ϑ hϑ
      have := hmono hx0 (show ϑ ∈ Set.Ioi c' from lt_of_lt_of_le hx0 hϑ) hϑ
      simp only at this; linarith
    refine tendsto_atTop_mono' _ hlow ?_
    exact tendsto_atTop_add_const_left _ _ (Tendsto.const_mul_atTop (by linarith) tendsto_id)
  · -- Part 3: near `0`, `F ≤ C - A/ϑ`
    set C := P.p / P.r + B * (2 / P.μ)
    have hC : 0 ≤ C := by positivity
    have hmono : MonotoneOn (fun ϑ => -Fs ϑ + C * ϑ - A * Real.log ϑ) (Set.Ioo 0 (P.μ / 2)) := by
      refine affRuinF_monoOn_Ioo (h' := fun ϑ => -F P ϑ + C - A * (1 / ϑ)) ?_ ?_
      · intro x hx
        have hx0 : 0 < x := hx.1
        have := ((hFd x hx0 (by linarith [hx.2])).neg.add
          ((hasDerivAt_id' x).const_mul C)).sub ((Real.hasDerivAt_log hx0.ne').const_mul A)
        exact this.congr_deriv (by ring)
      · intro x hx
        have hx0 : 0 < x := hx.1
        have hx2 : x < P.μ / 2 := hx.2
        have h2 : 1 / (P.μ - x) ≤ 2 / P.μ := by
          rw [div_le_div_iff₀ (by linarith) hμ]; linarith
        have := (hq x hx0).1
        have hk := key x
        nlinarith [mul_nonneg hL.le this, mul_le_mul_of_nonneg_left h2 hB.le]
    set x0 := P.μ / 4
    have hx0 : x0 ∈ Set.Ioo 0 (P.μ / 2) := ⟨by positivity, by simp only [x0]; linarith⟩
    have hlow : ∀ᶠ ϑ in 𝓝[>] (0 : ℝ),
        -(A * Real.log ϑ) - (-Fs x0 + C * x0 - A * Real.log x0) ≤ Fs ϑ := by
      filter_upwards [Ioo_mem_nhdsGT hx0.1] with ϑ hϑ
      have hm := hmono ⟨hϑ.1, lt_trans hϑ.2 hx0.2⟩ hx0 hϑ.2.le
      simp only at hm
      nlinarith [hϑ.1]
    refine tendsto_atTop_mono' _ hlow ?_
    exact tendsto_atTop_add_const_right _ _
      (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.const_mul_atBot hA))
  · -- Part 4: below `μ`, `F ≥ -C' + B/(μ-ϑ)`
    set C' := L * (2 / P.μ) + A * (2 / P.μ)
    have hC' : 0 ≤ C' := by positivity
    have hmono : MonotoneOn (fun ϑ => Fs ϑ + C' * ϑ + B * Real.log (P.μ - ϑ))
        (Set.Ioo (P.μ / 2) P.μ) := by
      refine affRuinF_monoOn_Ioo (h' := fun ϑ => F P ϑ + C' + B * (-1 / (P.μ - ϑ))) ?_ ?_
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hne : P.μ - x ≠ 0 := by linarith [hx.2]
        have := ((hFd x hx0 (by linarith [hx.2])).add
          ((hasDerivAt_id' x).const_mul C')).add
          ((((hasDerivAt_id' x).const_sub P.μ).log hne).const_mul B)
        exact this.congr_deriv (by ring)
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hx1 : P.μ / 2 < x := hx.1
        have h2 : 1 / x ≤ 2 / P.μ := by
          rw [div_le_div_iff₀ hx0 hμ]; linarith
        have := (hq x hx0).2
        have hk := key x
        rw [neg_div]
        nlinarith [mul_le_mul_of_nonneg_left (this.trans h2) hL.le,
          mul_le_mul_of_nonneg_left h2 hA.le]
    set x0 := 3 * P.μ / 4
    have hx0 : x0 ∈ Set.Ioo (P.μ / 2) P.μ := ⟨by simp only [x0]; linarith,
      by simp only [x0]; linarith⟩
    have hlow : ∀ᶠ ϑ in 𝓝[<] P.μ,
        -(B * Real.log (P.μ - ϑ)) + ((Fs x0 + C' * x0 + B * Real.log (P.μ - x0)) - C' * P.μ)
          ≤ Fs ϑ := by
      filter_upwards [Ioo_mem_nhdsLT hx0.2] with ϑ hϑ
      have hm := hmono hx0 ⟨lt_trans hx0.1 hϑ.1, hϑ.2⟩ hϑ.1.le
      simp only at hm
      nlinarith [hϑ.2]
    refine tendsto_atTop_mono' _ hlow ?_
    refine tendsto_atTop_add_const_right _ _
      (tendsto_neg_atBot_atTop.comp (Tendsto.const_mul_atBot hB ?_))
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ϑ : ℝ => P.μ - ϑ) (𝓝 P.μ) (𝓝 (P.μ - P.μ)) :=
        tendsto_const_nhds.sub tendsto_id
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ϑ hϑ
      exact Set.mem_Ioi.mpr (sub_pos.mpr (by simpa using hϑ))
  · -- Part 5: above `μ`, `F ≤ p/r + B/(μ-ϑ)`
    set C := P.p / P.r
    have hmono : MonotoneOn (fun ϑ => -Fs ϑ + C * ϑ - B * Real.log (ϑ - P.μ))
        (Set.Ioo P.μ (2 * P.μ)) := by
      refine affRuinF_monoOn_Ioo (h' := fun ϑ => -F P ϑ + C - B * (1 / (ϑ - P.μ))) ?_ ?_
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hne : x - P.μ ≠ 0 := by linarith [hx.1]
        have := ((hFd x hx0 (by linarith [hx.1])).neg.add
          ((hasDerivAt_id' x).const_mul C)).sub
          ((((hasDerivAt_id' x).sub_const P.μ).log hne).const_mul B)
        exact this.congr_deriv (by ring)
      · intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        have hx1 : P.μ < x := hx.1
        have h2 : 1 / (P.μ - x) = -(1 / (x - P.μ)) := by
          rw [← neg_sub, div_neg]
        have := (hq x hx0).1
        have hk := key x
        have h3 : 0 ≤ 1 / x := by positivity
        rw [h2] at hk
        nlinarith [mul_nonneg hL.le this, mul_nonneg hA.le h3]
    set x0 := 3 * P.μ / 2
    have hx0 : x0 ∈ Set.Ioo P.μ (2 * P.μ) := ⟨by simp only [x0]; linarith,
      by simp only [x0]; linarith⟩
    have hlow : ∀ᶠ ϑ in 𝓝[>] P.μ,
        -(B * Real.log (ϑ - P.μ)) - (-Fs x0 + C * x0 - B * Real.log (x0 - P.μ)) ≤ Fs ϑ := by
      filter_upwards [Ioo_mem_nhdsGT hx0.1] with ϑ hϑ
      have hm := hmono ⟨hϑ.1, lt_trans hϑ.2 hx0.2⟩ hx0 hϑ.2.le
      simp only at hm
      nlinarith [hϑ.1, hpr]
    refine tendsto_atTop_mono' _ hlow ?_
    refine tendsto_atTop_add_const_right _ _
      (tendsto_neg_atBot_atTop.comp (Tendsto.const_mul_atBot hB ?_))
    refine Real.tendsto_log_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun ϑ : ℝ => ϑ - P.μ) (𝓝 P.μ) (𝓝 (P.μ - P.μ)) :=
        tendsto_id.sub tendsto_const_nhds
      rw [sub_self] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ϑ hϑ
      exact Set.mem_Ioi.mpr (sub_pos.mpr (by simpa using hϑ))
