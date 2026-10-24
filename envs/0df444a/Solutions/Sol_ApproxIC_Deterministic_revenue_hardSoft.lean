-- Prove2me | solution 1 for ApproxIC.Deterministic.revenue_hardSoft
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:33:45.109131+00:00
-- url     : https://prove2.me/submissions/4049c1f0-cda9-4da3-9964-7ad20baae84e

import Mathlib
import Definitions.Def_ApproxIC_Deterministic_Setting
import Definitions.Def_ApproxIC_Deterministic_HardSoft

open MeasureTheory

namespace ApproxIC.Deterministic

lemma aic3r_f_int (M : Model) (hM : M.Standing) : Integrable M.f :=
  hM.2.2.2.1.integrable_of_forall_notMem_eq_zero (fun x hx => hM.2.2.1 x hx)

lemma aic3r_f_ii (M : Model) (hM : M.Standing) (a b : ℝ) : IntervalIntegrable M.f volume a b :=
  (aic3r_f_int M hM).intervalIntegrable

lemma aic3r_ae_ne (p : ℝ) : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ p := by
  rw [ae_iff]; simp

/-- `F̄(c) = 1 - F(r) - ∫_r^c f` for all `c`. -/
lemma aic3r_cdfBar_eq (M : Model) (hM : M.Standing) (r c : ℝ) :
    cdfBar M c = (1 - ∫ u in (0)..r, M.f u) - ∫ u in r..c, M.f u := by
  unfold cdfBar cdf
  rw [← intervalIntegral.integral_add_adjacent_intervals (aic3r_f_ii M hM 0 r)
    (aic3r_f_ii M hM r c)]
  ring

lemma aic3r_cdfBar_eq' (M : Model) (hM : M.Standing) (c : ℝ) :
    cdfBar M c = ∫ u in c..M.vbar, M.f u := by
  unfold cdfBar cdf
  have := intervalIntegral.integral_add_adjacent_intervals (aic3r_f_ii M hM 0 c)
    (aic3r_f_ii M hM c M.vbar)
  rw [hM.2.2.2.2] at this
  linarith

lemma aic3r_ii_mul (M : Model) (hM : M.Standing) {g : ℝ → ℝ} (hg : Measurable g) (a b C : ℝ)
    (hC : ∀ x ∈ Set.uIoc a b, |g x| ≤ C) :
    IntervalIntegrable (fun x => g x * M.f x) volume a b := by
  have hf := aic3r_f_ii M hM a b
  rw [intervalIntegrable_iff] at hf ⊢
  refine Integrable.bdd_mul (c := C) hf hg.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
  simpa using hC x hx

lemma aic3r_hs_meas (p s : ℝ) : Measurable (hardSoft p s).t := by
  show Measurable (fun v : ℝ => if v < p then (0:ℝ) else if v < s then v else s)
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iio measurable_id measurable_const)

lemma aic3r_hs_ii (M : Model) (hM : M.Standing) (p s a b : ℝ) :
    IntervalIntegrable (fun x => (hardSoft p s).t x * M.f x) volume a b := by
  refine aic3r_ii_mul M hM (aic3r_hs_meas p s) a b (|s| + |a| + |b|) ?_
  intro x hx
  have hx' := Set.uIoc_subset_uIcc hx
  have hxa : |x| ≤ |a| + |b| := by
    rcases le_total a b with h | h
    · rw [Set.uIcc_of_le h] at hx'
      rw [abs_le]; constructor
      · have := neg_abs_le a; have := abs_nonneg b; linarith [hx'.1]
      · have := le_abs_self b; have := abs_nonneg a; linarith [hx'.2]
    · rw [Set.uIcc_of_ge h] at hx'
      rw [abs_le]; constructor
      · have := neg_abs_le b; have := abs_nonneg a; linarith [hx'.1]
      · have := le_abs_self a; have := abs_nonneg b; linarith [hx'.2]
  show |(if x < p then (0:ℝ) else if x < s then x else s)| ≤ |s| + |a| + |b|
  split_ifs
  · simp; positivity
  · have := abs_nonneg s; linarith
  · have := abs_nonneg a; have := abs_nonneg b; linarith

theorem aic3_revenue_hardSoft (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (r : ℝ) (hr : r ∈ Set.Icc 0 M.vbar) :
    revenue M (hardSoft r (r + ε)) =
        (∫ v in r..(r + ε), v * M.f v) + (r + ε) * cdfBar M (r + ε) ∧
      revenue M (hardSoft r (r + ε)) = r * cdfBar M r + ∫ v in r..(r + ε), cdfBar M v := by
  set c := r + ε with hc
  have hrc : r ≤ c := by linarith
  have first : revenue M (hardSoft r c) = (∫ v in r..c, v * M.f v) + c * cdfBar M c := by
    unfold revenue
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := r) (aic3r_hs_ii M hM _ _ _ _)
      (aic3r_hs_ii M hM _ _ _ _),
      ← intervalIntegral.integral_add_adjacent_intervals (a := r) (b := c)
      (aic3r_hs_ii M hM _ _ _ _) (aic3r_hs_ii M hM _ _ _ _)]
    have P1 : ∫ v in (0)..r, (hardSoft r c).t v * M.f v = 0 := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => (0:ℝ))]
      · simp
      filter_upwards [aic3r_ae_ne r] with x hx hxI
      rw [Set.uIoc_of_le hr.1] at hxI
      have : x < r := lt_of_le_of_ne hxI.2 hx
      show (if x < r then (0:ℝ) else if x < c then x else c) * M.f x = 0
      simp [this]
    have P2 : ∫ v in r..c, (hardSoft r c).t v * M.f v = ∫ v in r..c, v * M.f v := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [aic3r_ae_ne c] with x hx hxI
      rw [Set.uIoc_of_le hrc] at hxI
      have h1 : x < c := lt_of_le_of_ne hxI.2 hx
      have h2 : ¬ x < r := not_lt.2 hxI.1.le
      show (if x < r then (0:ℝ) else if x < c then x else c) * M.f x = x * M.f x
      simp [h1, h2]
    have P3 : ∫ v in c..M.vbar, (hardSoft r c).t v * M.f v = c * cdfBar M c := by
      rw [aic3r_cdfBar_eq' M hM c, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun x hxI => ?_)
      show (if x < r then (0:ℝ) else if x < c then x else c) * M.f x = c * M.f x
      rcases le_total c M.vbar with h | h
      · rw [Set.uIoc_of_le h] at hxI
        have h1 : ¬ x < c := not_lt.2 hxI.1.le
        have h2 : ¬ x < r := fun h' => h1 (h'.trans_le hrc)
        simp [h1, h2]
      · rw [Set.uIoc_of_ge h] at hxI
        have : M.f x = 0 := hM.2.2.1 x (fun h' => absurd h'.2 (not_le.2 hxI.1))
        simp [this]
    rw [P1, P2, P3]; ring
  refine ⟨first, ?_⟩
  rw [first]
  -- integration by parts for absolutely continuous functions
  set K := 1 - ∫ u in (0)..r, M.f u with hK
  have hg : cdfBar M = fun x => K - ∫ u in r..x, M.f u := by
    funext x; exact aic3r_cdfBar_eq M hM r x
  have hacI : AbsolutelyContinuousOnInterval (fun x => ∫ u in r..x, M.f u) r c :=
    (aic3r_f_ii M hM r c).absolutelyContinuousOnInterval_intervalIntegral
      (Set.left_mem_uIcc)
  have hacK : AbsolutelyContinuousOnInterval (fun _ : ℝ => K) r c :=
    (LipschitzWith.const K).lipschitzOnWith.absolutelyContinuousOnInterval
  have hacg : AbsolutelyContinuousOnInterval (fun x => K - ∫ u in r..x, M.f u) r c :=
    hacK.sub hacI
  have hacid : AbsolutelyContinuousOnInterval (fun x : ℝ => x) r c :=
    LipschitzWith.id.lipschitzOnWith.absolutelyContinuousOnInterval
  have ibp := hacid.integral_mul_deriv_eq_deriv_mul hacg
  have hderiv : ∀ᵐ x ∂(volume : Measure ℝ),
      deriv (fun x => K - ∫ u in r..x, M.f u) x = - M.f x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral (aic3r_f_int M hM).locallyIntegrable] with x hx
    exact ((hx r).const_sub K).deriv
  have e1 : ∫ x in r..c, x * deriv (fun x => K - ∫ u in r..x, M.f u) x
      = - ∫ x in r..c, x * M.f x := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hderiv] with x hx _
    rw [hx]; ring
  have e2 : ∫ x in r..c, deriv (fun x : ℝ => x) x * (K - ∫ u in r..x, M.f u)
      = ∫ x in r..c, cdfBar M x := by
    rw [hg]; simp
  rw [e1, e2] at ibp
  rw [hg] at *
  simp only at ibp ⊢
  linarith

end ApproxIC.Deterministic

open ApproxIC.Deterministic

theorem solution (M : Model) (hM : M.Standing) (ε : ℝ) (hε : 0 ≤ ε)
    (r : ℝ) (hr : r ∈ Set.Icc 0 M.vbar) :
    revenue M (hardSoft r (r + ε)) =
        (∫ v in r..(r + ε), v * M.f v) + (r + ε) * cdfBar M (r + ε) ∧
      revenue M (hardSoft r (r + ε)) = r * cdfBar M r + ∫ v in r..(r + ε), cdfBar M v :=
  aic3_revenue_hardSoft M hM ε hε r hr
