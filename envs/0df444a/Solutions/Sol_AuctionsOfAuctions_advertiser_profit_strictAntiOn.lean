-- Prove2me | solution 1 for AuctionsOfAuctions.advertiser_profit_strictAntiOn
-- status  : ACCEPTED   (prove)
-- author  : @Albert
-- created : 2026-11-13T10:17:28.019813+00:00
-- url     : https://prove2.me/submissions/ccb5ade9-8128-435a-bce2-d67b68202121

import Definitions.Def_AuctionsOfAuctions_Model

open Set MeasureTheory Filter
open AuctionsOfAuctions
open scoped Topology

private lemma intPos {g : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn g (Icc a b)) (hn : ∀ x ∈ Icc a b, 0 ≤ g x)
    (hp : ∀ x ∈ Ioo a b, 0 < g x) : 0 < ∫ x in a..b, g x := by
  rw [← intervalIntegral.integral_zero]
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hab continuousOn_const hc
  · exact fun x hx => hn x ⟨hx.1.le, hx.2⟩
  · obtain ⟨x,hx,hy⟩ := exists_between hab
    exact ⟨x, ⟨hx.le,hy.le⟩, hp x ⟨hx,hy⟩⟩

private lemma subInterval {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Icc a b ⊆ Icc (0 : ℝ) 1 := fun _ hx => ⟨ha.trans hx.1,hx.2.trans hb⟩

private lemma intCont {g : ℝ → ℝ} (hc : ContinuousOn g (Icc (0 : ℝ) 1))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun b => ∫ x in a..b, g x) (Icc (0 : ℝ) 1) := by
  simpa only [uIcc_of_le zero_le_one] using
    (intervalIntegral.continuousOn_primitive_interval' (hc.intervalIntegrable_of_Icc zero_le_one)
      (by simpa only [uIcc_of_le zero_le_one] using ha))

private lemma Fcont (D : ValuationDist) : ContinuousOn D.F (Icc 0 1) :=
  intCont D.continuousOn_f (left_mem_Icc.mpr zero_le_one)

private lemma Fnonneg (D : ValuationDist) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    0 ≤ D.F x :=
  intervalIntegral.integral_nonneg hx.1 (fun y hy => D.nonneg_f y (subInterval le_rfl hx.2 hy))

private lemma Fpos (D : ValuationDist) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    0 < D.F x :=
  intPos hx.1 (D.continuousOn_f.mono (subInterval le_rfl hx.2))
    (fun y hy => D.nonneg_f y (subInterval le_rfl hx.2 hy))
    (fun y hy => D.pos_f y ⟨hy.1,hy.2.trans_le hx.2⟩)

private lemma Fderiv (D : ValuationDist) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt D.F (D.f x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · exact (D.continuousOn_f.mono (subInterval le_rfl hx.2.le)).intervalIntegrable_of_Icc hx.1.le
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (D.continuousOn_f.mono Ioo_subset_Icc_self) x hx
  · exact (D.continuousOn_f x ⟨hx.1.le,hx.2.le⟩).continuousAt (Icc_mem_nhds hx.1 hx.2)

private lemma betaIdentity (D : ValuationDist) {r v : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (hrv : r ≤ v) (hv0 : 0 < v) :
    (v - D.beta v r) * D.F v ^ 3 = ∫ t in r..v, D.F t ^ 3 := by
  have hc : ContinuousOn (fun t => t * (3 * D.F t ^ 2 * D.f t)) (Icc (0 : ℝ) 1) :=
    continuousOn_id.mul ((continuousOn_const.mul ((Fcont D).pow 2)).mul D.continuousOn_f)
  have hcont : ContinuousOn (fun t => t * D.F t ^ 3) (Icc r v) :=
    (continuousOn_id.mul ((Fcont D).pow 3)).mono (subInterval hr.1 hv.2)
  have hder : ∀ x ∈ Ioo r v,
      HasDerivAt (fun t => t * D.F t ^ 3) (D.F x ^ 3 + x * (3 * D.F x ^ 2 * D.f x)) x := by
    intro x hx
    have h := (hasDerivAt_id x).mul ((Fderiv D ⟨hr.1.trans_lt hx.1,hx.2.trans_le hv.2⟩).pow 3)
    change HasDerivAt (fun t => t * D.F t ^ 3)
      (1 * D.F x ^ 3 + x * (3 * D.F x ^ (3 - 1) * D.f x)) x at h
    simpa only [one_mul, Nat.reduceSub] using h
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hrv hcont hder
    (((((Fcont D).pow 3).add hc).mono (subInterval hr.1 hv.2)).intervalIntegrable_of_Icc hrv)
  rw [intervalIntegral.integral_add (f := fun t => D.F t ^ 3)
    (((Fcont D).pow 3).mono (subInterval hr.1 hv.2) |>.intervalIntegrable_of_Icc hrv)
    ((hc.mono (subInterval hr.1 hv.2)).intervalIntegrable_of_Icc hrv)] at hi
  unfold ValuationDist.beta
  have hne := (pow_pos (Fpos D ⟨hv0,hv.2⟩) 3).ne'
  rw [sub_mul, div_mul_cancel₀ _ hne]
  linarith

private noncomputable def profitDensity (D : ValuationDist) (r v : ℝ) : ℝ :=
  (∫ t in r..v, D.F t ^ 3) * D.f v

private lemma densityCont (D : ValuationDist) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (profitDensity D r) (Icc 0 1) :=
  (intCont ((Fcont D).pow 3) hr).mul D.continuousOn_f

private lemma profitEq (D : ValuationDist) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    D.advertiserProfit r = ∫ x in r..1, profitDensity D r x := by
  unfold ValuationDist.advertiserProfit
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le hr.2
  intro x hx
  have he := betaIdentity D hr ⟨hr.1.trans hx.1.le,hx.2.le⟩ hx.1.le (hr.1.trans_lt hx.1)
  unfold profitDensity
  rw [← he]
  ring

private lemma densityNonneg (D : ValuationDist) {r v : ℝ} (hr : 0 ≤ r) (hv : v ≤ 1)
    (hrv : r ≤ v) : 0 ≤ profitDensity D r v := by
  apply mul_nonneg
  · exact intervalIntegral.integral_nonneg hrv (fun x hx => pow_nonneg (Fnonneg D (subInterval hr hv hx)) 3)
  · exact D.nonneg_f v ⟨hr.trans hrv,hv⟩

theorem solution (D : ValuationDist) : StrictAntiOn D.advertiserProfit (Icc 0 1) := by
  intro a ha b hb hab
  rw [profitEq D ha, profitEq D hb]
  have hpos : 0 < ∫ x in a..b, profitDensity D a x := by
    apply intPos hab ((densityCont D ha).mono (subInterval ha.1 hb.2))
    · exact fun x hx => densityNonneg D ha.1 (hx.2.trans hb.2) hx.1
    · intro x hx
      apply mul_pos _ (D.pos_f x ⟨ha.1.trans_lt hx.1,hx.2.trans_le hb.2⟩)
      exact intPos hx.1 (((Fcont D).pow 3).mono (subInterval ha.1 (hx.2.le.trans hb.2)))
        (fun t ht => pow_nonneg (Fnonneg D ⟨ha.1.trans ht.1,ht.2.trans (hx.2.le.trans hb.2)⟩) 3)
        (fun t ht => pow_pos (Fpos D ⟨ha.1.trans_lt ht.1,ht.2.le.trans (hx.2.le.trans hb.2)⟩) 3)
  have hm : (∫ x in b..1, profitDensity D b x) ≤ ∫ x in b..1, profitDensity D a x := by
    apply intervalIntegral.integral_mono_on hb.2
      ((densityCont D hb).mono (subInterval hb.1 le_rfl) |>.intervalIntegrable_of_Icc hb.2)
      ((densityCont D ha).mono (subInterval hb.1 le_rfl) |>.intervalIntegrable_of_Icc hb.2)
    intro x hx
    apply mul_le_mul_of_nonneg_right _ (D.nonneg_f x (subInterval hb.1 le_rfl hx))
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (((Fcont D).pow 3).mono (subInterval ha.1 hb.2) |>.intervalIntegrable_of_Icc hab.le)
      (((Fcont D).pow 3).mono (subInterval hb.1 hx.2) |>.intervalIntegrable_of_Icc hx.1)
    have hn := intervalIntegral.integral_nonneg (μ := volume) hab.le
      (fun t ht => pow_nonneg (Fnonneg D (subInterval ha.1 hb.2 ht)) 3)
    change (∫ t in a..b, D.F t ^ 3) + (∫ t in b..x, D.F t ^ 3) =
      (∫ t in a..x, D.F t ^ 3) at h
    linarith
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((densityCont D ha).mono (subInterval ha.1 hb.2) |>.intervalIntegrable_of_Icc hab.le)
    ((densityCont D ha).mono (subInterval hb.1 le_rfl) |>.intervalIntegrable_of_Icc hb.2)
  linarith
