-- Prove2me | solution 1 for AuctionsOfAuctions.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Albert
-- created : 2026-11-13T10:28:12.295776+00:00
-- url     : https://prove2.me/submissions/d1a752b8-14c8-47d7-824a-3912c2e940be

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

private lemma Flt (D : ValuationDist) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hab : a < b) : D.F a < D.F b := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((D.continuousOn_f.mono (subInterval le_rfl (hab.le.trans hb))).intervalIntegrable_of_Icc ha)
    ((D.continuousOn_f.mono (subInterval ha hb)).intervalIntegrable_of_Icc hab.le)
  have hp := intPos hab (D.continuousOn_f.mono (subInterval ha hb))
    (fun x hx => D.nonneg_f x (subInterval ha hb hx))
    (fun x hx => D.pos_f x ⟨ha.trans_lt hx.1,hx.2.trans_le hb⟩)
  unfold ValuationDist.F
  linarith

private lemma hazardFactor (D : ValuationDist) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.lamTilde x = (2 * D.F x / (3 - D.F x)) * D.lam 1 x := by
  have hF : D.F x < 1 := (D.integral_f : D.F 1 = 1) ▸ Flt D hx.1.le le_rfl hx.2
  unfold ValuationDist.lamTilde ValuationDist.lam
  simp only [Nat.sub_self, pow_zero, Nat.cast_one, one_mul, pow_one]
  have h1 : 1 - D.F x ≠ 0 := by linarith
  have h3 : 3 - D.F x ≠ 0 := by linarith
  field_simp
  <;> ring

private lemma factorRange (D : ValuationDist) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < 2 * D.F x / (3 - D.F x) ∧ 2 * D.F x / (3 - D.F x) < 1 := by
  have hF : D.F x < 1 := (D.integral_f : D.F 1 = 1) ▸ Flt D hx.1.le le_rfl hx.2
  have hp := Fpos D ⟨hx.1,hx.2.le⟩
  exact ⟨div_pos (by linarith) (by linarith), (div_lt_iff₀ (by linarith)).2 (by linarith)⟩

private lemma lamOnePos (D : ValuationDist) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    0 < D.lam 1 x := by
  have hF : D.F x < 1 := (D.integral_f : D.F 1 = 1) ▸ Flt D hx.1.le le_rfl hx.2
  simpa [ValuationDist.lam] using div_pos (D.pos_f x hx) (sub_pos.mpr hF)

private lemma hazardLt (D : ValuationDist) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    D.lamTilde x < D.lam 1 x := by
  rw [hazardFactor D hx]
  simpa using mul_lt_mul_of_pos_right (factorRange D hx).2 (lamOnePos D hx)

private lemma hazardMono (D : ValuationDist)
    (hm : StrictMonoOn (D.lam 1) (Ioo 0 1)) :
    StrictMonoOn D.lamTilde (Ico 0 1) := by
  intro a ha b hb hab
  have hb' : b ∈ Ioo (0 : ℝ) 1 := ⟨ha.1.trans_lt hab,hb.2⟩
  by_cases h : a = 0
  · subst a
    have h0 : D.lamTilde 0 = 0 := by simp [ValuationDist.lamTilde,ValuationDist.F]
    rw [h0,hazardFactor D hb']
    exact mul_pos (factorRange D hb').1 (lamOnePos D hb')
  · have ha' : a ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne ha.1 (Ne.symm h),ha.2⟩
    rw [hazardFactor D ha',hazardFactor D hb']
    have hFa : D.F a < 1 := (D.integral_f : D.F 1 = 1) ▸ Flt D ha.1 le_rfl ha.2
    have hFb : D.F b < 1 := (D.integral_f : D.F 1 = 1) ▸ Flt D hb.1 le_rfl hb.2
    have hf : 2 * D.F a / (3 - D.F a) < 2 * D.F b / (3 - D.F b) := by
      apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
      nlinarith only [Flt D ha.1 hb.2.le hab]
    exact (mul_lt_mul_of_pos_right hf (lamOnePos D ha')).trans_le
      (mul_le_mul_of_nonneg_left (hm ha' hb' hab).le (factorRange D hb').1.le)

private lemma psiSign (D : ValuationDist) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (h : 1 < x * D.lam 1 x) : 0 < D.psi x := by
  have hF : D.F x < 1 := (D.integral_f : D.F 1 = 1) ▸ Flt D hx.1.le le_rfl hx.2
  have hh : 1 < (x * D.f x) / (1 - D.F x) := by
    simpa [ValuationDist.lam, mul_div_assoc] using h
  have hp := (lt_div_iff₀ (sub_pos.mpr hF)).1 hh
  unfold ValuationDist.psi
  apply sub_pos.mpr
  exact (div_lt_iff₀ (D.pos_f x hx)).2 (by simpa using hp)

private lemma primDeriv (D : ValuationDist) {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    {r x : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => ∫ t in r..y, g t) (g x) x := by
  have hi : IntervalIntegrable g volume 0 1 := hg.intervalIntegrable_of_Icc zero_le_one
  apply intervalIntegral.integral_hasDerivAt_right
  · apply hi.mono_set
    rw [uIcc_of_le zero_le_one]
    exact uIcc_subset_Icc hr ⟨hx.1.le,hx.2.le⟩
  · exact ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo (hg.mono Ioo_subset_Icc_self) x hx
  · exact (hg x ⟨hx.1.le,hx.2.le⟩).continuousAt (Icc_mem_nhds hx.1 hx.2)

private lemma exchangeNumerator (D : ValuationDist) {r v : ℝ}
    (hr : r ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (h : r < v) :
    r * D.F r ^ 2 + (∫ y in r..v, D.beta y r * (2 * D.F y * D.f y)) =
      v * D.F v ^ 2 + 2 * (∫ t in r..v, D.F t ^ 3) / D.F v -
        3 * (∫ t in r..v, D.F t ^ 2) := by
  let J := fun x => ∫ t in r..x, D.F t ^ 3
  let K := fun x => ∫ t in r..x, D.F t ^ 2
  let G := fun x => x * D.F x ^ 2 + 2 * J x / D.F x - 3 * K x
  have hJ : ContinuousOn J (Icc 0 1) := primitiveCont ((Fcont D).pow 3) hr
  have hK : ContinuousOn K (Icc 0 1) := primitiveCont ((Fcont D).pow 2) hr
  have hG : ContinuousOn G (Icc r v) := by
    intro x hx
    have hx' := subInterval hr.1 hv.2 hx
    by_cases hp : 0 < x
    · have hn : D.F x ≠ 0 := (Fpos D ⟨hp,hx'.2⟩).ne'
      have hf := ((Fcont D) x hx').mono (subInterval hr.1 hv.2)
      exact (((continuous_id.continuousWithinAt.mul (hf.pow 2)).add
        ((continuousWithinAt_const.mul ((hJ x hx').mono (subInterval hr.1 hv.2))).div hf hn)).sub
        (continuousWithinAt_const.mul ((hK x hx').mono (subInterval hr.1 hv.2))))
    · have hx0 : x = 0 := le_antisymm (le_of_not_gt hp) hx'.1
      have hr0 : r = 0 := le_antisymm (hx0 ▸ hx.1) hr.1
      have hQ : ContinuousWithinAt (fun y => J y / D.F y) (Icc r v) x := by
        have hzero : J x / D.F x = 0 := by simp [J,hx0,hr0]
        change Tendsto (fun y => J y / D.F y) (𝓝[Icc r v] x) (𝓝 (J x / D.F x))
        rw [hzero]
        have ht : Tendsto (fun y => y * D.F y ^ 2) (𝓝[Icc r v] x) (𝓝 0) := by
          have hc : ContinuousWithinAt (fun y => y * D.F y ^ 2) (Icc r v) x :=
            continuous_id.continuousWithinAt.mul
              ((((Fcont D) x hx').mono (subInterval hr.1 hv.2)).pow 2)
          have ht := hc.tendsto
          change Tendsto (fun y => y * D.F y ^ 2) (𝓝[Icc r v] x) (𝓝 (x * D.F x ^ 2)) at ht
          simpa only [hx0,zero_mul] using ht
        apply squeeze_zero' _ _ ht
        all_goals
          filter_upwards [self_mem_nhdsWithin (s := Icc r v) (a := x)] with y hy
          have hy' := subInterval hr.1 hv.2 hy
          by_cases hy0 : 0 < y
          · have he := betaIdentity D hr hy' hy.1 hy0
            have hf := Fpos D ⟨hy0,hy'.2⟩
            have hb := betaBounds D hr hy' (by simpa [hr0] using hy0)
            first
            | exact div_nonneg (intervalIntegral.integral_nonneg hy.1
                  (fun t ht => pow_nonneg (Fnonneg D (subInterval hr.1 hy'.2 ht)) 3)) hf.le
            | apply (div_le_iff₀ hf).2
              change J y ≤ _
              change _ = J y at he
              have hn := mul_nonneg (hr.1.trans hb.1.le) (pow_nonneg hf.le 3)
              nlinarith only [he,hn]
          · have hyz := le_antisymm (le_of_not_gt hy0) hy'.1
            simp [J,hyz,hr0]
      have hf := ((Fcont D) x hx').mono (subInterval hr.1 hv.2)
      have hcont : ContinuousWithinAt
          (fun y => y * D.F y ^ 2 + 2 * (J y / D.F y) - 3 * K y) (Icc r v) x :=
        ((continuous_id.continuousWithinAt.mul (hf.pow 2)).add
          (continuousWithinAt_const.mul hQ)).sub
          (continuousWithinAt_const.mul ((hK x hx').mono (subInterval hr.1 hv.2)))
      simpa only [G, mul_div_assoc] using hcont
  have hder : ∀ x ∈ Ioo r v, HasDerivAt G (D.beta x r * (2 * D.F x * D.f x)) x := by
    intro x hx
    have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hr.1.trans_lt hx.1,hx.2.trans_le hv.2⟩
    have hf := Fderiv D hx'
    have hp := Fpos D ⟨hx'.1,hx'.2.le⟩
    have hJd := primDeriv D ((Fcont D).pow 3) hr hx'
    have hKd := primDeriv D ((Fcont D).pow 2) hr hx'
    have hd := (((hasDerivAt_id x).mul (hf.pow 2)).add
      ((hJd.div hf hp.ne').const_mul 2)).sub (hKd.const_mul 3)
    have he := betaIdentity D hr ⟨hx'.1.le,hx'.2.le⟩ hx.1.le hx'.1
    change _ = J x at he
    have hfun : (fun y => (id y * (D.F ^ 2) y + 2 * (J y / D.F y)) - 3 * K y) = G := by
      funext y
      simp [G,mul_div_assoc]
    have hcoef : (1 * D.F x ^ 2 + x * ((2 : ℕ) * D.F x ^ (2 - 1) * D.f x)) +
        2 * ((D.F x ^ 3 * D.F x - J x * D.f x) / D.F x ^ 2) - 3 * D.F x ^ 2 =
        D.beta x r * (2 * D.F x * D.f x) := by
      rw [← he]
      push_cast
      field_simp
      <;> ring
    change HasDerivAt (fun y => id y * (D.F ^ 2) y + 2 * (J y / D.F y) - 3 * K y) _ x at hd
    rw [hfun] at hd
    convert hd using 1 <;> first | rfl | exact hcoef.symm
  have hc := (betaCont D hr).mul
    (((continuousOn_const (c := (2 : ℝ))).mul (Fcont D)).mul D.continuousOn_f
      |>.mono (subInterval hr.1 le_rfl))
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.le hG hder
    ((hc.mono (subIcc le_rfl hv.2)).intervalIntegrable_of_Icc h.le)
  have hg : G r = r * D.F r ^ 2 := by simp [G,J,K]
  rw [hg] at he
  change _ = G v
  linarith

private lemma powerDeriv (D : ValuationDist) (k : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y => D.F y ^ k) ((k : ℝ) * D.F x ^ (k-1) * D.f x) x :=
  (Fderiv D hx).pow k

private lemma integrateProduct (D : ValuationDist) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    {u du v dv : ℝ → ℝ}
    (hu : ContinuousOn u (Icc 0 1)) (hv : ContinuousOn v (Icc 0 1))
    (hdu : ContinuousOn du (Icc 0 1)) (hdv : ContinuousOn dv (Icc 0 1))
    (hu' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt u (du x) x)
    (hv' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt v (dv x) x) :
    (∫ x in r..1, u x * dv x) =
      u 1 * v 1 - u r * v r - ∫ x in r..1, du x * v x := by
  have hsub : Icc r 1 ⊆ Icc (0 : ℝ) 1 := subInterval hr.1 le_rfl
  apply intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
  · rw [uIcc_of_le hr.2]; exact hu.mono hsub
  · rw [uIcc_of_le hr.2]; exact hv.mono hsub
  · rw [min_eq_left hr.2,max_eq_right hr.2]
    exact fun x hx => hu' x ⟨hr.1.trans_lt hx.1,hx.2⟩
  · rw [min_eq_left hr.2,max_eq_right hr.2]
    exact fun x hx => hv' x ⟨hr.1.trans_lt hx.1,hx.2⟩
  · exact (hdu.mono hsub).intervalIntegrable_of_Icc hr.2
  · exact (hdv.mono hsub).intervalIntegrable_of_Icc hr.2

private lemma revFormulas (D : ValuationDist) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) :
    D.revDir r = 1 - r * D.F r ^ 4 + 3 * (∫ t in r..1, D.F t ^ 4) -
      4 * (∫ t in r..1, D.F t ^ 3) ∧
    D.revEx r = 1 - r * D.F r ^ 4 - 3 * (∫ t in r..1, D.F t ^ 4) +
      8 * (∫ t in r..1, D.F t ^ 3) - 6 * (∫ t in r..1, D.F t ^ 2) := by
  let J := fun x => ∫ t in r..x, D.F t ^ 3
  let K := fun x => ∫ t in r..x, D.F t ^ 2
  let A := fun x => x * (4 * D.F x ^ 3 * D.f x)
  let B := fun x => J x * D.f x
  let C := fun x => K x * (2 * D.F x * D.f x)
  have hF := Fcont D
  have hf1 : D.F 1 = 1 := D.integral_f
  have hJ : ContinuousOn J (Icc 0 1) := primitiveCont (hF.pow 3) hr
  have hK : ContinuousOn K (Icc 0 1) := primitiveCont (hF.pow 2) hr
  have hw : ContinuousOn (fun x => 4 * D.F x ^ 3 * D.f x) (Icc 0 1) :=
    (continuousOn_const.mul (hF.pow 3)).mul D.continuousOn_f
  have hw2 : ContinuousOn (fun x => 2 * D.F x * D.f x) (Icc 0 1) :=
    (continuousOn_const.mul hF).mul D.continuousOn_f
  have hA : (∫ x in r..1, A x) = 1 - r * D.F r ^ 4 - ∫ t in r..1, D.F t ^ 4 := by
    have h := integrateProduct D hr continuousOn_id (hF.pow 4) continuousOn_const hw
      (fun x _ => hasDerivAt_id x) (fun x hx => by exact powerDeriv D 4 hx)
    simpa [A,hf1] using h
  have hB : (∫ x in r..1, B x) = J 1 - ∫ t in r..1, D.F t ^ 4 := by
    have h := integrateProduct D hr hJ hF (hF.pow 3) D.continuousOn_f
      (fun _ hx => primDeriv D (hF.pow 3) hr hx) (fun _ hx => Fderiv D hx)
    change _ = J 1 * D.F 1 - J r * D.F r - _ at h
    have hz : J r = 0 := by simp [J]
    rw [hf1,hz,zero_mul,mul_one,sub_zero] at h
    convert h using 2
    apply intervalIntegral.integral_congr
    intro x _
    change D.F x ^ 4 = _
    simp only [Pi.pow_apply]
    ring
  have hC : (∫ x in r..1, C x) = K 1 - ∫ t in r..1, D.F t ^ 4 := by
    have h := integrateProduct D hr hK (hF.pow 2) (hF.pow 2) hw2
      (fun _ hx => primDeriv D (hF.pow 2) hr hx) (fun _ hx => by
        have hd := powerDeriv D 2 hx
        norm_num at hd
        exact hd)
    change _ = K 1 * D.F 1 ^ 2 - K r * D.F r ^ 2 - _ at h
    have hz : K r = 0 := by simp [K]
    rw [hf1,one_pow,hz,zero_mul,mul_one,sub_zero] at h
    convert h using 2
    apply intervalIntegral.integral_congr
    intro x _
    change D.F x ^ 4 = _
    simp only [Pi.pow_apply]
    ring
  have intC {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
      IntervalIntegrable g volume r 1 :=
    (hg.mono (subInterval hr.1 le_rfl)).intervalIntegrable_of_Icc hr.2
  have ia : IntervalIntegrable A volume r 1 := intC (continuousOn_id.mul hw)
  have ib : IntervalIntegrable B volume r 1 := intC (hJ.mul D.continuousOn_f)
  have ic : IntervalIntegrable C volume r 1 := intC (hK.mul hw2)
  constructor
  · have he : D.revDir r = ∫ x in r..1, A x - 4 * B x := by
      apply intervalIntegral.integral_congr_Ioo_of_le hr.2
      intro x hx
      have hi := betaIdentity D hr ⟨hr.1.trans hx.1.le,hx.2.le⟩ hx.1.le (hr.1.trans_lt hx.1)
      change _ = J x at hi
      have hm := congrArg (fun y : ℝ => 4 * D.f x * y) hi
      dsimp [A,B]
      linarith only [show _ = _ from hm]
    rw [he, intervalIntegral.integral_sub ia (ib.const_mul 4), intervalIntegral.integral_const_mul,hA,hB]
    dsimp [J]
    ring
  · have he : D.revEx r = ∫ x in r..1, A x + 8 * B x - 6 * C x := by
      apply intervalIntegral.integral_congr_Ioo_of_le hr.2
      intro x hx
      have hi := exchangeNumerator D hr ⟨hr.1.trans hx.1.le,hx.2.le⟩ hx.1
      change _ = x * D.F x ^ 2 + 2 * J x / D.F x - 3 * K x at hi
      have hp := (Fpos D ⟨hr.1.trans_lt hx.1,hx.2.le⟩).ne'
      change D.sigmaTilde x r * (4 * D.F x ^ 3 * D.f x) = _
      unfold ValuationDist.sigmaTilde
      rw [hi]
      dsimp [A,B,C]
      field_simp <;> ring
    rw [he,intervalIntegral.integral_sub (ia.add (ib.const_mul 8)) (ic.const_mul 6),
      intervalIntegral.integral_add ia (ib.const_mul 8),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,hA,hB,hC]
    dsimp [J,K]
    ring

private lemma tailCont (D : ValuationDist) (k : ℕ) :
    ContinuousOn (fun r => ∫ t in r..1, D.F t ^ k) (Icc 0 1) := by
  have h : ContinuousOn (fun r => -(∫ t in (1 : ℝ)..r, D.F t ^ k)) (Icc 0 1) :=
    (primitiveCont ((Fcont D).pow k) (right_mem_Icc.mpr zero_le_one)).neg
  simpa only [intervalIntegral.integral_symm (a := (1 : ℝ)),neg_neg] using h

private lemma tailDeriv (D : ValuationDist) (k : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun r => ∫ t in r..1, D.F t ^ k) (-(D.F r ^ k)) r := by
  have h : HasDerivAt (fun r => -(∫ t in (1 : ℝ)..r, D.F t ^ k)) (-(D.F r ^ k)) r :=
    (primDeriv D ((Fcont D).pow k) (right_mem_Icc.mpr zero_le_one) hr).neg
  simpa only [intervalIntegral.integral_symm (a := (1 : ℝ)),neg_neg] using h

private lemma revExCont (D : ValuationDist) : ContinuousOn D.revEx (Icc 0 1) := by
  apply ContinuousOn.congr _ (fun x hx => (revFormulas D hx).2)
  exact (((continuousOn_const.sub (continuousOn_id.mul ((Fcont D).pow 4))).sub
    (continuousOn_const.mul (tailCont D 4))).add (continuousOn_const.mul (tailCont D 3))).sub
    (continuousOn_const.mul (tailCont D 2))

private lemma revDeriv (D : ValuationDist) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt D.revDir (4 * D.F r ^ 3 * (1 - D.F r - r * D.f r)) r ∧
    HasDerivAt D.revEx (2 * D.F r ^ 2 *
      ((1 - D.F r) * (3 - D.F r) - 2 * r * D.F r * D.f r)) r := by
  have base := (hasDerivAt_const r (1 : ℝ)).sub ((hasDerivAt_id r).mul (powerDeriv D 4 hr))
  have hdir := (base.add ((tailDeriv D 4 hr).const_mul 3)).sub ((tailDeriv D 3 hr).const_mul 4)
  have hex := ((base.sub ((tailDeriv D 4 hr).const_mul 3)).add
    ((tailDeriv D 3 hr).const_mul 8)).sub ((tailDeriv D 2 hr).const_mul 6)
  have hevent := Icc_mem_nhds hr.1 hr.2
  constructor
  · have h := hdir.congr_of_eventuallyEq (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Icc 0 1,hevent, fun x hx => (revFormulas D hx).1⟩)
    convert h using 1 <;> first | rfl | (simp only [id_eq]; push_cast; ring)
  · have h := hex.congr_of_eventuallyEq (Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨Icc 0 1,hevent, fun x hx => (revFormulas D hx).2⟩)
    convert h using 1 <;> first | rfl | (simp only [id_eq]; push_cast; ring)

private lemma exInterior (D : ValuationDist) {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1)
    (hm : IsMaxOn D.revEx (Icc 0 1) r) : r ∈ Ioo 0 1 := by
  refine ⟨?_,?_⟩
  · by_contra! hn
    have hz := le_antisymm hn hr.1
    subst r
    let g := fun x => (1 - D.F x) * (3 - D.F x) - 2 * x * D.F x * D.f x
    have hg : ContinuousOn g (Icc 0 1) :=
      ((continuousOn_const.sub (Fcont D)).mul (continuousOn_const.sub (Fcont D))).sub
        (((continuousOn_const.mul continuousOn_id).mul (Fcont D)).mul D.continuousOn_f)
    have h0 : g 0 = 3 := by simp [g,ValuationDist.F]
    have hpos : ∀ᶠ x in 𝓝[Icc (0 : ℝ) 1] 0, 0 < g x :=
      (hg 0 ⟨le_rfl,zero_le_one⟩).tendsto (Ioi_mem_nhds (by rw [h0]; norm_num))
    rw [eventually_nhdsWithin_iff] at hpos
    obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hpos
    let y := min (ε / 2) (1 / 2)
    have hy : 0 < y := lt_min (by positivity) (by norm_num)
    have hy1 : y < 1 := (min_le_right _ _).trans_lt (by norm_num)
    have hyε : y < ε := (min_le_left _ _).trans_lt (by linarith)
    have hmono := strictMonoOn_of_deriv_pos (convex_Icc 0 y)
      ((revExCont D).mono (subInterval le_rfl hy1.le)) (fun x hx => by
        rw [interior_Icc] at hx
        have hx' : x ∈ Ioo (0 : ℝ) 1 := ⟨hx.1,hx.2.trans hy1⟩
        rw [(revDeriv D hx').2.deriv]
        apply mul_pos (mul_pos (by norm_num) (pow_pos (Fpos D ⟨hx'.1,hx'.2.le⟩) 2))
        apply hball
        · rw [Real.dist_eq,sub_zero,abs_of_pos hx.1]
          exact hx.2.trans hyε
        · exact ⟨hx'.1.le,hx'.2.le⟩)
    exact (not_lt_of_ge (hm ⟨hy.le,hy1.le⟩)) (hmono ⟨le_rfl,hy.le⟩ ⟨hy.le,le_rfl⟩ hy)
  · by_contra! hn
    have hz := le_antisymm hr.2 hn
    subst r
    have hrh : (1/2 : ℝ) ∈ Icc 0 1 := by constructor <;> norm_num
    have he : 0 < D.revEx (1/2) := by
      have hc : ContinuousOn (fun x =>
        ((1/2 : ℝ) * D.F (1/2) ^ 2 + ∫ y in (1/2 : ℝ)..x, D.beta y (1/2) * (2 * D.F y * D.f y)) /
          D.F x ^ 2 * (4 * D.F x ^ 3 * D.f x)) (Icc (1/2) 1) := by
        have hweight : ContinuousOn (fun y => D.beta y (1/2) * (2 * D.F y * D.f y)) (Icc (1/2) 1) :=
          (betaCont D hrh).mul (((continuousOn_const.mul (Fcont D)).mul D.continuousOn_f).mono
            (subInterval hrh.1 le_rfl))
        have hp := intervalIntegral.continuousOn_primitive_interval' (μ := volume)
          (hweight.intervalIntegrable_of_Icc hrh.2) (left_mem_uIcc : (1/2 : ℝ) ∈ uIcc (1/2) 1)
        rw [uIcc_of_le hrh.2] at hp
        exact ((continuousOn_const.add hp).div (((Fcont D).pow 2).mono (subInterval hrh.1 le_rfl))
          (fun x hx => pow_ne_zero _ (Fpos D ⟨(by norm_num : (0 : ℝ) < 1/2).trans_le hx.1,hx.2⟩).ne')).mul
          (((continuousOn_const.mul ((Fcont D).pow 3)).mul D.continuousOn_f).mono
            (subInterval hrh.1 le_rfl))
      unfold ValuationDist.revEx
      apply intPos (by norm_num) hc
      · intro x hx
        have hp := Fpos D ⟨(by norm_num : (0 : ℝ) < 1/2).trans_le hx.1,hx.2⟩
        have hbid : 0 ≤ D.sigmaTilde x (1/2) := by
          rcases hx.1.eq_or_lt with he | he
          · subst x
            unfold ValuationDist.sigmaTilde
            simp only [intervalIntegral.integral_same,add_zero]
            positivity
          · exact (by norm_num : (0 : ℝ) ≤ 1/2).trans (sigmaBounds D hrh
              ⟨hrh.1.trans hx.1,hx.2⟩ he).1.le
        exact mul_nonneg hbid (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp.le _))
          (D.nonneg_f x ⟨hrh.1.trans hx.1,hx.2⟩))
      · intro x hx
        have hxx : x ∈ Ioo (0 : ℝ) 1 := ⟨hrh.1.trans_lt hx.1,hx.2⟩
        exact mul_pos ((by norm_num : (0 : ℝ) < 1/2).trans
          (sigmaBounds D hrh ⟨hxx.1.le,hxx.2.le⟩ hx.1).1)
          (mul_pos (mul_pos (by norm_num) (pow_pos (Fpos D ⟨hxx.1,hxx.2.le⟩) 3)) (D.pos_f x hxx))
    have hm' := hm hrh
    change D.revEx (1/2) ≤ D.revEx 1 at hm'
    have hz : D.revEx 1 = 0 := by simp [ValuationDist.revEx]
    rw [hz] at hm'
    exact (not_lt_of_ge hm') he

theorem solution (D : ValuationDist) (hreg : D.IsRegular) :
    (∀ Re ∈ Icc (0 : ℝ) 1, IsMaxOn D.revEx (Icc 0 1) Re →
      Re ∈ Ioo (0 : ℝ) 1 ∧ Re * D.lamTilde Re = 1) ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, D.lamTilde x < D.lam 1 x) ∧
    (∀ Rd ∈ Icc (0 : ℝ) 1, ∀ Re ∈ Icc (0 : ℝ) 1,
      IsMaxOn D.revDir (Icc 0 1) Rd → IsMaxOn D.revEx (Icc 0 1) Re → Rd < Re) ∧
    (StrictMonoOn (D.lam 1) (Ioo 0 1) → StrictMonoOn D.lamTilde (Ico 0 1)) := by
  have he : ∀ r ∈ Icc (0 : ℝ) 1, IsMaxOn D.revEx (Icc 0 1) r →
      r ∈ Ioo (0 : ℝ) 1 ∧ r * D.lamTilde r = 1 := by
    intro r hr hm
    have hi := exInterior D hr hm
    have hF : D.F r < 1 := (D.integral_f : D.F 1 = 1) ▸ Flt D hi.1.le le_rfl hi.2
    have hp := Fpos D ⟨hi.1,hi.2.le⟩
    have hz := (hm.isLocalMax (Icc_mem_nhds hi.1 hi.2)).hasDerivAt_eq_zero (revDeriv D hi).2
    have heq := (mul_eq_zero.mp hz).resolve_left (by positivity : 2 * D.F r ^ 2 ≠ 0)
    refine ⟨hi,?_⟩
    unfold ValuationDist.lamTilde
    rw [← mul_div_assoc, div_eq_iff (mul_ne_zero (by linarith) (by linarith))]
    nlinarith only [heq]
  refine ⟨he, fun x hx => hazardLt D hx, ?_,hazardMono D⟩
  intro rd hd re hr hmd hme
  obtain ⟨hre,heq⟩ := he re hr hme
  have hψ : 0 < D.psi re := psiSign D hre (heq ▸ mul_lt_mul_of_pos_left (hazardLt D hre) hre.1)
  have hcont : ContinuousOn D.revDir (Icc 0 1) := by
    apply ContinuousOn.congr _ (fun x hx => (revFormulas D hx).1)
    exact ((continuousOn_const.sub (continuousOn_id.mul ((Fcont D).pow 4))).add
      (continuousOn_const.mul (tailCont D 4))).sub (continuousOn_const.mul (tailCont D 3))
  have hneg (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) (hp : 0 < D.psi x) : deriv D.revDir x < 0 := by
    rw [(revDeriv D hx).1.deriv]
    have h := (div_lt_iff₀ (D.pos_f x hx)).1 (sub_pos.mp hp)
    exact mul_neg_of_pos_of_neg
      (mul_pos (by norm_num) (pow_pos (Fpos D ⟨hx.1,hx.2.le⟩) 3)) (by linarith)
  by_contra! hn
  have hanti := strictAntiOn_of_deriv_neg (convex_Icc re 1)
    (hcont.mono (subInterval hre.1.le le_rfl)) (fun x hx => by
      rw [interior_Icc] at hx
      have hxi : x ∈ Ioo (0 : ℝ) 1 := ⟨hre.1.trans hx.1,hx.2⟩
      exact hneg x hxi (hψ.trans_le (hreg hre hxi hx.1.le)))
  rcases hn.eq_or_lt with hh | hh
  · subst rd
    have hz := (hmd.isLocalMax (Icc_mem_nhds hre.1 hre.2)).deriv_eq_zero
    exact (hneg re hre hψ).ne hz
  · exact (not_lt_of_ge (hmd hr)) (hanti ⟨le_rfl,hr.2⟩ ⟨hn,hd.2⟩ hh)
