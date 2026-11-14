-- Prove2me | solution 1 for AuctionsOfAuctions.revenue_ranking_fixed_reserve
-- status  : ACCEPTED   (prove)
-- author  : @Albert
-- created : 2026-11-13T10:21:42.556205+00:00
-- url     : https://prove2.me/submissions/b71f0197-b995-4236-a375-f2613b4b4bff

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

private lemma primitiveCont {g : ℝ → ℝ} (hc : ContinuousOn g (Icc (0 : ℝ) 1))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun b => ∫ x in a..b, g x) (Icc (0 : ℝ) 1) := by
  simpa only [uIcc_of_le zero_le_one] using
    (intervalIntegral.continuousOn_primitive_interval' (hc.intervalIntegrable_of_Icc zero_le_one)
      (by simpa only [uIcc_of_le zero_le_one] using ha))

private lemma Fcont (D : ValuationDist) : ContinuousOn D.F (Icc 0 1) :=
  primitiveCont D.continuousOn_f (left_mem_Icc.mpr zero_le_one)

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

private lemma subIcc {a b c d : ℝ} (ha : a ≤ c) (hb : d ≤ b) :
    Icc c d ⊆ Icc a b := fun _ h => ⟨ha.trans h.1,h.2.trans hb⟩

private lemma betaBounds (D : ValuationDist) {r v : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (h : r < v) :
    r < D.beta v r ∧ D.beta v r ≤ v := by
  have hv0 := hr.1.trans_lt h
  have hp := pow_pos (Fpos D ⟨hv0,hv.2⟩) 3
  have hid := betaIdentity D hr hv h.le hv0
  have hF : ∀ t ∈ Icc r v, D.F t ≤ D.F v := by
    intro t ht
    have ha := hr.1.trans ht.1
    have hb := ht.2.trans hv.2
    have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((D.continuousOn_f.mono (subInterval le_rfl hb)).intervalIntegrable_of_Icc ha)
      ((D.continuousOn_f.mono (subInterval ha hv.2)).intervalIntegrable_of_Icc ht.2)
    have hn := intervalIntegral.integral_nonneg (μ := volume) ht.2
      (fun x hx => D.nonneg_f x (subInterval ha hv.2 hx))
    unfold ValuationDist.F
    linarith
  have hle : (∫ t in r..v, D.F t ^ 3) < (v-r)*D.F v^3 := by
    rw [← smul_eq_mul, ← intervalIntegral.integral_const]
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h
      (((Fcont D).pow 3).mono (subInterval hr.1 hv.2)) continuousOn_const
    · intro x hx
      exact pow_le_pow_left₀ (Fnonneg D ⟨hr.1.trans hx.1.le,hx.2.trans hv.2⟩)
        (hF x ⟨hx.1.le,hx.2⟩) 3
    · refine ⟨r,⟨le_rfl,h.le⟩,?_⟩
      apply pow_lt_pow_left₀ _ (Fnonneg D hr) (by decide)
      unfold ValuationDist.F
      rw [← intervalIntegral.integral_add_adjacent_intervals
        ((D.continuousOn_f.mono (subInterval le_rfl hr.2)).intervalIntegrable_of_Icc hr.1)
        ((D.continuousOn_f.mono (subInterval hr.1 hv.2)).intervalIntegrable_of_Icc h.le)]
      have := intPos h (D.continuousOn_f.mono (subInterval hr.1 hv.2))
        (fun x hx => D.nonneg_f x (subInterval hr.1 hv.2 hx))
        (fun x hx => D.pos_f x ⟨hr.1.trans_lt hx.1,hx.2.trans_le hv.2⟩)
      linarith
  have hn := intervalIntegral.integral_nonneg (μ := volume) h.le
    (fun x hx => pow_nonneg (Fnonneg D (subInterval hr.1 hv.2 hx)) 3)
  constructor
  · apply lt_of_sub_pos
    apply pos_of_mul_pos_left _ hp.le
    nlinarith only [hid, hle]
  · exact sub_nonneg.mp (nonneg_of_mul_nonneg_left (hid ▸ hn) hp)

private lemma betaCont (D : ValuationDist) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    ContinuousOn (fun x => D.beta x r) (Icc r 1) := by
  let g := fun t => t * (3 * D.F t ^ 2 * D.f t)
  have hc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    continuousOn_id.mul ((continuousOn_const.mul ((Fcont D).pow 2)).mul D.continuousOn_f)
  have hnum := (continuousOn_const (c := r * D.F r ^ 3)).add (primitiveCont hc hr :
    ContinuousOn (fun x => ∫ t in r..x, g t) (Icc 0 1))
  intro x hx
  by_cases hp : 0 < x
  · have hpos : ContinuousOn (fun y => D.beta y r) (Ioc 0 1) :=
      (hnum.mono Ioc_subset_Icc_self).div (((Fcont D).pow 3).mono Ioc_subset_Icc_self)
        (fun y hy => (pow_pos (Fpos D hy) 3).ne')
    apply (hpos x ⟨hp,hx.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hp),
      self_mem_nhdsWithin (s := Icc r 1) (a := x)] with y hy hy'
    exact ⟨hy,hy'.2⟩
  · have hx0 : x = 0 := le_antisymm (le_of_not_gt hp) (hr.1.trans hx.1)
    have hr0 : r = 0 := le_antisymm (hx0 ▸ hx.1) hr.1
    subst x
    subst r
    have hb0 : D.beta 0 0 = 0 := by simp [ValuationDist.beta]
    change Tendsto (fun y => D.beta y 0) (𝓝[Icc 0 1] 0) (𝓝 (D.beta 0 0))
    rw [hb0]
    apply squeeze_zero' _ _ continuous_id.continuousWithinAt
    all_goals
      filter_upwards [self_mem_nhdsWithin (s := Icc (0 : ℝ) 1) (a := 0)] with y hy
      rcases hy.1.eq_or_lt with he | he
      · simp [← he, hb0]
      · first | exact (betaBounds D ⟨le_rfl,zero_le_one⟩ hy he).1.le |
          exact (betaBounds D ⟨le_rfl,zero_le_one⟩ hy he).2

private lemma betaMono (D : ValuationDist) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    StrictMonoOn (fun x => D.beta x r) (Icc r 1) := by
  let g := fun t => t * (3 * D.F t ^ 2 * D.f t)
  have hc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    continuousOn_id.mul ((continuousOn_const.mul ((Fcont D).pow 2)).mul D.continuousOn_f)
  apply strictMonoOn_of_deriv_pos (convex_Icc r 1) (betaCont D hr)
  · intro x hx
    rw [interior_Icc] at hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hr.1.trans_lt hx.1,hx.2⟩
    have hgd : HasDerivAt (fun y => ∫ t in r..y, g t) (g x) x :=
      intervalIntegral.integral_hasDerivAt_right
        ((hc.mono (subInterval hr.1 hx.2.le)).intervalIntegrable_of_Icc hx.1.le)
        (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hc.mono Ioo_subset_Icc_self) x hx')
        ((hc x ⟨hx'.1.le,hx'.2.le⟩).continuousAt (Icc_mem_nhds hx'.1 hx'.2))
    have hp := Fpos D ⟨hx'.1,hx'.2.le⟩
    have hdiv := ((hasDerivAt_const x (r * D.F r ^ 3)).add hgd).div
      ((Fderiv D hx').pow 3) (pow_ne_zero _ hp.ne')
    change HasDerivAt (fun y => D.beta y r) _ x at hdiv
    rw [hdiv.deriv]
    apply div_pos _ (pow_pos (pow_pos hp 3) 2)
    have hi := betaIdentity D hr ⟨hx'.1.le,hx'.2.le⟩ hx.1.le hx'.1
    have hstrict : 0 < ∫ t in r..x, D.F t ^ 3 :=
      intPos hx.1 (((Fcont D).pow 3).mono (subInterval hr.1 hx'.2.le))
        (fun y hy => pow_nonneg (Fnonneg D (subInterval hr.1 hx'.2.le hy)) 3)
        (fun y hy => pow_pos (Fpos D ⟨hr.1.trans_lt hy.1,hy.2.le.trans hx'.2.le⟩) 3)
    have hprod : 0 < (∫ t in r..x, D.F t ^ 3) * (3 * D.F x ^ 2 * D.f x) :=
      mul_pos hstrict (mul_pos (mul_pos (by norm_num) (pow_pos hp 2)) (D.pos_f x hx'))
    unfold ValuationDist.beta at hi
    rw [sub_mul, div_mul_cancel₀ _ (pow_ne_zero _ hp.ne')] at hi
    dsimp [g]
    rw [← hi] at hprod
    nlinarith only [hprod]

private lemma FsqIntegral (D : ValuationDist) {r v : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (h : r ≤ v) :
    (∫ t in r..v, 2 * D.F t * D.f t) = D.F v ^ 2 - D.F r ^ 2 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h
    (((Fcont D).pow 2).mono (subInterval hr.1 hv.2))
  · intro x hx
    have hd := (Fderiv D ⟨hr.1.trans_lt hx.1,hx.2.trans_le hv.2⟩).pow 2
    norm_num at hd
    exact hd
  · exact (((continuousOn_const.mul (Fcont D)).mul D.continuousOn_f).mono
      (subInterval hr.1 hv.2)).intervalIntegrable_of_Icc h

private lemma sigmaBounds (D : ValuationDist) {r v : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (h : r < v) :
    r < D.sigmaTilde v r ∧ D.sigmaTilde v r < D.beta v r := by
  let w := fun x => 2 * D.F x * D.f x
  have hw : ContinuousOn w (Icc r v) :=
    ((continuousOn_const.mul (Fcont D)).mul D.continuousOn_f).mono (subInterval hr.1 hv.2)
  have hb := betaMono D hr
  have hc := (betaCont D hr).mono (subIcc le_rfl hv.2)
  have hw0 : ∀ x ∈ Icc r v, 0 ≤ w x := fun x hx =>
    mul_nonneg (mul_nonneg (by norm_num) (Fnonneg D (subInterval hr.1 hv.2 hx)))
      (D.nonneg_f x (subInterval hr.1 hv.2 hx))
  have hwpos : ∀ x ∈ Ioo r v, 0 < w x := fun x hx =>
    mul_pos (mul_pos (by norm_num) (Fpos D ⟨hr.1.trans_lt hx.1,hx.2.le.trans hv.2⟩))
      (D.pos_f x ⟨hr.1.trans_lt hx.1,hx.2.trans_le hv.2⟩)
  obtain ⟨c,hcr,hcv⟩ := exists_between h
  have hv' : v ∈ Icc r 1 := ⟨h.le,hv.2⟩
  have hlo : (∫ x in r..v, r * w x) < ∫ x in r..v, D.beta x r * w x := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h
      (continuousOn_const.mul hw) (hc.mul hw)
    · intro x hx
      exact mul_le_mul_of_nonneg_right
        (betaBounds D hr (subInterval hr.1 hv.2 ⟨hx.1.le,hx.2⟩) hx.1).1.le
        (hw0 x ⟨hx.1.le,hx.2⟩)
    · refine ⟨c,⟨hcr.le,hcv.le⟩,mul_lt_mul_of_pos_right ?_ (hwpos c ⟨hcr,hcv⟩)⟩
      exact (betaBounds D hr ⟨hr.1.trans hcr.le,hcv.le.trans hv.2⟩ hcr).1
  have hhi : (∫ x in r..v, D.beta x r * w x) < ∫ x in r..v, D.beta v r * w x := by
    apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt h
      (hc.mul hw) (continuousOn_const.mul hw)
    · intro x hx
      exact mul_le_mul_of_nonneg_right
        (hb.monotoneOn ⟨hx.1.le,hx.2.trans hv.2⟩ hv' hx.2) (hw0 x ⟨hx.1.le,hx.2⟩)
    · exact ⟨c,⟨hcr.le,hcv.le⟩,mul_lt_mul_of_pos_right
        (hb ⟨hcr.le,hcv.le.trans hv.2⟩ hv' hcv) (hwpos c ⟨hcr,hcv⟩)⟩
  rw [intervalIntegral.integral_const_mul] at hlo hhi
  have he : (∫ x in r..v, w x) = D.F v ^ 2 - D.F r ^ 2 := FsqIntegral D hr hv h.le
  rw [he] at hlo hhi
  have hp := pow_pos (Fpos D ⟨hr.1.trans_lt h,hv.2⟩) 2
  unfold ValuationDist.sigmaTilde
  constructor
  · apply (lt_div_iff₀ hp).2
    change _ < r * D.F r ^ 2 + ∫ x in r..v, D.beta x r * w x
    linarith
  · apply (div_lt_iff₀ hp).2
    have hbr := (betaBounds D hr hv h).1.le
    have := mul_le_mul_of_nonneg_right hbr (sq_nonneg (D.F r))
    change r * D.F r ^ 2 + (∫ x in r..v, D.beta x r * w x) < _
    linarith

theorem solution (D : ValuationDist) (r : ℝ) (hr : r ∈ Ico (0 : ℝ) 1) :
    (∀ v ∈ Ioc r 1, r < D.sigmaTilde v r ∧ D.sigmaTilde v r < D.beta v r) ∧
    D.revMono r < D.revEx r ∧ D.revEx r < D.revDir r := by
  have hr' : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1,hr.2.le⟩
  have hs : ∀ v ∈ Ioc r 1, r < D.sigmaTilde v r ∧ D.sigmaTilde v r < D.beta v r :=
    fun v hv => sigmaBounds D hr' ⟨hr.1.trans hv.1.le,hv.2⟩ hv.1
  refine ⟨hs, ?_⟩
  let w := fun x => 4 * D.F x ^ 3 * D.f x
  let e := fun x => (r * D.F r ^ 2 + ∫ y in r..x, D.beta y r * (2 * D.F y * D.f y)) *
    (4 * D.F x * D.f x)
  let d := fun x => (r * D.F r ^ 3 + ∫ y in r..x, y * (3 * D.F y ^ 2 * D.f y)) *
    (4 * D.f x)
  have hw : ContinuousOn w (Icc r 1) :=
    (((continuousOn_const.mul ((Fcont D).pow 3)).mul D.continuousOn_f).mono
      (subInterval hr.1 le_rfl))
  have he : ContinuousOn e (Icc r 1) := by
    have hc : ContinuousOn (fun y => D.beta y r * (2 * D.F y * D.f y)) (Icc r 1) := (betaCont D hr').mul
      (((continuousOn_const.mul (Fcont D)).mul D.continuousOn_f).mono (subInterval hr.1 le_rfl))
    have hp := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
      (hc.intervalIntegrable_of_Icc hr.2.le) (left_mem_uIcc : r ∈ uIcc r 1)
    rw [uIcc_of_le hr.2.le] at hp
    exact (continuousOn_const.add hp).mul
      (((continuousOn_const.mul (Fcont D)).mul D.continuousOn_f).mono (subInterval hr.1 le_rfl))
  have hd : ContinuousOn d (Icc r 1) :=
    ((continuousOn_const.add (primitiveCont
      (continuousOn_id.mul ((continuousOn_const.mul ((Fcont D).pow 2)).mul D.continuousOn_f))
      hr')).mul (continuousOn_const.mul D.continuousOn_f)).mono (subInterval hr.1 le_rfl)
  have heq (x : ℝ) (hx : x ∈ Ioc r 1) : e x = D.sigmaTilde x r * w x := by
    have hp := (Fpos D ⟨hr.1.trans_lt hx.1,hx.2⟩).ne'
    dsimp [e,w,ValuationDist.sigmaTilde]
    field_simp <;> ring
  have hdq (x : ℝ) (hx : x ∈ Ioc r 1) : d x = D.beta x r * w x := by
    have hp := (Fpos D ⟨hr.1.trans_lt hx.1,hx.2⟩).ne'
    dsimp [d,w,ValuationDist.beta]
    field_simp <;> ring
  have hev : D.revEx r = ∫ x in r..1, e x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hr.2.le
    exact fun x hx => (heq x ⟨hx.1,hx.2.le⟩).symm
  have hdv : D.revDir r = ∫ x in r..1, d x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hr.2.le
    exact fun x hx => (hdq x ⟨hx.1,hx.2.le⟩).symm
  have hwv : (∫ x in r..1, w x) = 1 - D.F r ^ 4 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.2.le
      (((Fcont D).pow 4).mono (subInterval hr.1 le_rfl))
      (fun x (hx : x ∈ Ioo r 1) => (Fderiv D ⟨hr.1.trans_lt hx.1,hx.2⟩).pow 4)
      (hw.intervalIntegrable_of_Icc hr.2.le)
    have hf1 : D.F 1 = 1 := D.integral_f
    change (∫ y in r..1, (4 : ℝ) * D.F y ^ 3 * D.f y) = D.F 1 ^ 4 - D.F r ^ 4 at h
    simpa only [w,hf1,one_pow] using h
  have hnonneg (x : ℝ) (hx : x ∈ Ioc r 1) : 0 ≤ w x :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (Fpos D ⟨hr.1.trans_lt hx.1,hx.2⟩).le 3))
      (D.nonneg_f x ⟨hr.1.trans hx.1.le,hx.2⟩)
  obtain ⟨c,hcr,hc1⟩ := exists_between hr.2
  have hc : c ∈ Ioc r 1 := ⟨hcr,hc1.le⟩
  have hcp : 0 < w c :=
    mul_pos (mul_pos (by norm_num) (pow_pos (Fpos D ⟨hr.1.trans_lt hcr,hc1.le⟩) 3))
      (D.pos_f c ⟨hr.1.trans_lt hcr,hc1⟩)
  rw [hev,hdv]
  constructor
  · have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hr.2
      (continuousOn_const.mul hw : ContinuousOn (fun x => r * w x) (Icc r 1)) he
      (fun x hx => heq x hx ▸ mul_le_mul_of_nonneg_right (hs x hx).1.le (hnonneg x hx))
      ⟨c,⟨hcr.le,hc1.le⟩,heq c hc ▸ mul_lt_mul_of_pos_right (hs c hc).1 hcp⟩
    change (∫ x in r..1, r * w x) < _ at h
    rwa [intervalIntegral.integral_const_mul,hwv] at h
  · apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hr.2 he hd
    · intro x hx
      rw [heq x hx,hdq x hx]
      exact mul_le_mul_of_nonneg_right (hs x hx).2.le (hnonneg x hx)
    · refine ⟨c,⟨hcr.le,hc1.le⟩,?_⟩
      rw [heq c hc,hdq c hc]
      exact mul_lt_mul_of_pos_right (hs c hc).2 hcp
