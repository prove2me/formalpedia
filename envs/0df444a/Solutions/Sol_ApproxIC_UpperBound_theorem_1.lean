-- Prove2me | solution 1 for ApproxIC.UpperBound.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T19:46:24.458926+00:00
-- url     : https://prove2.me/submissions/f3290b6d-3a06-4b6e-9194-c4118c3cfe55

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting

-- ===== part A =====

open MeasureTheory Set ApproxIC.UpperBound

namespace AIC1T1

lemma f_integrable (M : Model) (hM : M.Standing) : Integrable M.f := by
  obtain ⟨_, _, hz, hint, _⟩ := hM
  exact hint.integrable_of_forall_notMem_eq_zero (fun v hv => hz v hv)

lemma f_ii (M : Model) (hM : M.Standing) (a b : ℝ) : IntervalIntegrable M.f volume a b :=
  (f_integrable M hM).intervalIntegrable

lemma f_bdd (M : Model) (hM : M.Assumption1) : ∃ B > 0, ∀ v, M.f v ≤ B := by
  obtain ⟨⟨hv, _, hz, _, _⟩, hbv⟩ := hM
  refine ⟨|M.f 0| + (eVariationOn M.f (Icc 0 M.vbar)).toReal + 1, by positivity, fun v => ?_⟩
  by_cases hvS : v ∈ Icc 0 M.vbar
  · have h0 : (0:ℝ) ∈ Icc 0 M.vbar := ⟨le_rfl, hv.le⟩
    have h1 := eVariationOn.edist_le M.f hvS h0
    have h2 : dist (M.f v) (M.f 0) ≤ (eVariationOn M.f (Icc 0 M.vbar)).toReal := by
      rw [dist_edist]; exact ENNReal.toReal_mono hbv h1
    rw [Real.dist_eq] at h2
    have h3 := le_abs_self (M.f v - M.f 0)
    have h4 := le_abs_self (M.f 0)
    have h5 : 0 ≤ (eVariationOn M.f (Icc 0 M.vbar)).toReal := ENNReal.toReal_nonneg
    linarith
  · rw [hz v hvS]; positivity

lemma cdf_cont (M : Model) (hM : M.Standing) : Continuous (cdf M) := by
  have := intervalIntegral.continuous_primitive (f_ii M hM) 0
  exact this

lemma cdfBar_cont (M : Model) (hM : M.Standing) : Continuous (cdfBar M) := by
  unfold cdfBar; exact continuous_const.sub (cdf_cont M hM)

lemma R_cont (M : Model) (hM : M.Standing) : Continuous (R M) := by
  unfold R; exact continuous_id.mul (cdfBar_cont M hM)

lemma cdfBar_eq (M : Model) (hM : M.Standing) (p : ℝ) :
    cdfBar M p = ∫ v in p..M.vbar, M.f v := by
  have hone := hM.2.2.2.2
  unfold cdfBar cdf
  rw [← hone]
  exact intervalIntegral.integral_interval_sub_left (f_ii M hM _ _) (f_ii M hM _ _)

lemma cdfBar_eq_zero (M : Model) (hM : M.Standing) (p : ℝ) (hp : M.vbar ≤ p) :
    cdfBar M p = 0 := by
  rw [cdfBar_eq M hM]
  have hz := hM.2.2.1
  rw [intervalIntegral.integral_symm]
  have : ∫ v in M.vbar..p, M.f v = ∫ v in M.vbar..p, (0:ℝ) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [uIoc_of_le hp] at hx
    exact hz x (fun h => by linarith [h.2, hx.1])
  rw [this]; simp

lemma R_eq_zero (M : Model) (hM : M.Standing) (p : ℝ) (hp : M.vbar ≤ p) : R M p = 0 := by
  unfold R; rw [cdfBar_eq_zero M hM p hp, mul_zero]

lemma cdfBar_nonneg (M : Model) (hM : M.Standing) (p : ℝ) (hp : p ≤ M.vbar) :
    0 ≤ cdfBar M p := by
  rw [cdfBar_eq M hM]
  exact intervalIntegral.integral_nonneg hp (fun x _ => hM.2.1 x)

lemma R_nonneg (M : Model) (hM : M.Standing) (p : ℝ) (hp : 0 ≤ p) : 0 ≤ R M p := by
  unfold R
  rcases le_total p M.vbar with h | h
  · exact mul_nonneg hp (cdfBar_nonneg M hM p h)
  · rw [cdfBar_eq_zero M hM p h, mul_zero]

/-- `R(b) - R(a) = ∫_a^b Ṙ` for `0 ≤ a ≤ b`. -/
lemma R_sub_eq (M : Model) (hM : M.Standing) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    R M b - R M a = ∫ x in a..b, Rdot M x := by
  have hb : 0 ≤ b := ha.trans hab
  have hsub : uIcc a b ⊆ uIcc 0 b := by
    rw [uIcc_of_le hab, uIcc_of_le hb]; exact Icc_subset_Icc ha le_rfl
  have hF : AbsolutelyContinuousOnInterval (cdf M) a b := by
    have := (f_ii M hM 0 b).absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by simp)
    exact this.mono hsub
  have hC : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1:ℝ)) a b :=
    (LipschitzWith.const (α := ℝ) (1:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  have hid : AbsolutelyContinuousOnInterval (fun x : ℝ => x) a b :=
    (LipschitzWith.id).lipschitzOnWith.absolutelyContinuousOnInterval
  have hR : AbsolutelyContinuousOnInterval (R M) a b := by
    have := hid.mul (hC.sub hF)
    exact this
  rw [← hR.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  have hae := (f_ii M hM 0 b).ae_hasDerivAt_integral
  filter_upwards [hae] with x hx hxI
  have hxI' : x ∈ uIcc 0 b := hsub (uIoc_subset_uIcc hxI)
  have hd : HasDerivAt (cdf M) (M.f x) x := hx hxI' 0 (by simp)
  have hd2 : HasDerivAt (R M) (1 * cdfBar M x + x * (-M.f x)) x := by
    have h1 : HasDerivAt (cdfBar M) (-M.f x) x := by
      have := hd.const_sub (1:ℝ)
      exact this
    exact (hasDerivAt_id x).mul h1
  rw [hd2.deriv]; unfold Rdot; ring

lemma Rdot_ii (M : Model) (hM : M.Standing) (a b : ℝ) :
    IntervalIntegrable (Rdot M) volume a b := by
  unfold Rdot
  apply IntervalIntegrable.sub
  · exact (cdfBar_cont M hM).intervalIntegrable _ _
  · have := (f_ii M hM a b).continuousOn_mul (g := fun x : ℝ => x) continuousOn_id
    simpa [mul_comm] using this

/-- Integral of the power function. -/
lemma integral_pow_shift (α d : ℝ) (hα : 1 < α) (hd : 0 ≤ d) :
    ∫ x in (0:ℝ)..d, α * x ^ (α - 1) = d ^ α := by
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith))]
  have h1 : α - 1 + 1 = α := by ring
  rw [h1, Real.zero_rpow (by linarith)]
  field_simp
  ring

/-- Definition 1 gives `κ_L |p - p⋆|^α ≤ R(p⋆) - R(p)` on the neighborhood. -/
lemma R_drop (M : Model) (hM : M.Standing) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) :
    ∀ p ∈ Ioo (pstar - ℓ) (pstar + ℓ), κL * |p - pstar| ^ α ≤ R M pstar - R M p := by
  obtain ⟨hpI, _, _, hα, hκL, _, hℓ, hN, henv⟩ := hD
  intro p hp
  have hp0 : 0 < p := (hN hp).1
  have hps0 : 0 < pstar := hpI.1
  have hcont : Continuous (fun x : ℝ => x) := continuous_id
  rcases le_total pstar p with hle | hle
  · -- p ≥ p⋆
    have key : ∫ x in pstar..p, Rdot M x ≤ ∫ x in pstar..p, -(κL * (α * (x - pstar) ^ (α - 1))) := by
      apply intervalIntegral.integral_mono_ae_restrict hle (Rdot_ii M hM _ _)
      · apply Continuous.intervalIntegrable
        apply Continuous.neg; apply Continuous.mul continuous_const
        apply Continuous.mul continuous_const
        exact (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr (by linarith))
      · rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        have hxN : x ∈ Ioo (pstar - ℓ) (pstar + ℓ) := ⟨by linarith [hx.1], by linarith [hx.2, hp.2]⟩
        have h1 := (henv x hxN).1
        have hxp : 0 < x - pstar := by linarith [hx.1]
        rw [abs_of_pos hxp] at h1
        have h2 : (x - pstar) ^ α = (x - pstar) ^ (α - 1) * (x - pstar) := by
          rw [← Real.rpow_add_one hxp.ne']; ring_nf
        rw [h2] at h1
        have h3 : 0 ≤ (x - pstar) ^ (α - 1) := Real.rpow_nonneg hxp.le _
        show Rdot M x ≤ -(κL * (α * (x - pstar) ^ (α - 1)))
        nlinarith
    have hval : ∫ x in pstar..p, -(κL * (α * (x - pstar) ^ (α - 1))) = -(κL * (p - pstar) ^ α) := by
      rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_comp_sub_right (fun x => α * x ^ (α - 1)) pstar]
      rw [sub_self, integral_pow_shift α _ hα (by linarith)]
    rw [hval] at key
    have := R_sub_eq M hM pstar p hps0.le hle
    rw [abs_of_nonneg (by linarith)]
    linarith
  · -- p ≤ p⋆
    have key : ∫ x in p..pstar, κL * (α * (pstar - x) ^ (α - 1)) ≤ ∫ x in p..pstar, Rdot M x := by
      apply intervalIntegral.integral_mono_ae_restrict hle _ (Rdot_ii M hM _ _)
      · rw [← Measure.restrict_congr_set Ico_ae_eq_Icc]
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ico]
        refine Filter.Eventually.of_forall (fun x hx => ?_)
        have hxN : x ∈ Ioo (pstar - ℓ) (pstar + ℓ) := ⟨by linarith [hx.1, hp.1], by linarith [hx.2]⟩
        have h1 := (henv x hxN).1
        have hxp : 0 < pstar - x := by linarith [hx.2]
        rw [abs_sub_comm, abs_of_pos hxp] at h1
        have h2 : (pstar - x) ^ α = (pstar - x) ^ (α - 1) * (pstar - x) := by
          rw [← Real.rpow_add_one hxp.ne']; ring_nf
        rw [h2] at h1
        have h3 : 0 ≤ (pstar - x) ^ (α - 1) := Real.rpow_nonneg hxp.le _
        show κL * (α * (pstar - x) ^ (α - 1)) ≤ Rdot M x
        nlinarith
      · apply Continuous.intervalIntegrable
        apply Continuous.mul continuous_const
        apply Continuous.mul continuous_const
        exact (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by linarith))
    have hval : ∫ x in p..pstar, κL * (α * (pstar - x) ^ (α - 1)) = κL * (pstar - p) ^ α := by
      rw [intervalIntegral.integral_const_mul]
      rw [intervalIntegral.integral_comp_sub_left (fun x => α * x ^ (α - 1)) pstar]
      rw [sub_self, integral_pow_shift α _ hα (by linarith)]
    rw [hval] at key
    have := R_sub_eq M hM p pstar hp0.le hle
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith

/-- Away from the neighborhood, `R` is uniformly below `R(p⋆)`. -/
lemma far_gap (M : Model) (hM : M.Standing) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) :
    ∃ c0 > 0, ∀ p, 0 ≤ p → p ∉ Ioo (pstar - ℓ) (pstar + ℓ) → R M p ≤ R M pstar - c0 := by
  obtain ⟨hpI, hmax, huniq, _, _, _, hℓ, hN, _⟩ := hD
  set K := Icc 0 M.vbar ∩ (Ioo (pstar - ℓ) (pstar + ℓ))ᶜ with hK
  have hKc : IsCompact K := isCompact_Icc.inter_right isOpen_Ioo.isClosed_compl
  have hvbarK : M.vbar ∈ K := by
    refine ⟨⟨hM.1.le, le_rfl⟩, fun h => ?_⟩
    have := (hN h).2; linarith
  obtain ⟨q, hqK, hqmax⟩ := hKc.exists_isMaxOn ⟨_, hvbarK⟩ (R_cont M hM).continuousOn
  have hqle : R M q ≤ R M pstar := hmax hqK.1
  have hqne : R M q ≠ R M pstar := by
    intro h
    have := huniq q hqK.1 h
    apply hqK.2; rw [this]; exact ⟨by linarith, by linarith⟩
  refine ⟨R M pstar - R M q, by
    have := lt_of_le_of_ne hqle hqne; linarith, fun p hp0 hpN => ?_⟩
  rcases le_total p M.vbar with h | h
  · have : R M p ≤ R M q := hqmax ⟨⟨hp0, h⟩, hpN⟩
    linarith
  · rw [R_eq_zero M hM p h]
    have : R M M.vbar ≤ R M q := hqmax hvbarK
    rw [R_eq_zero M hM _ le_rfl] at this
    linarith

end AIC1T1

-- ===== part B =====

open MeasureTheory Set ApproxIC.UpperBound

namespace AIC1T1

/-- The buyer's envelope utility `U(s) = max(0, sup_{y ∈ S} (s x(y) - t(y)))`. -/
noncomputable def Uf (M : Model) (m : Mech) (s : ℝ) : ℝ :=
  sSup (insert 0 ((fun y => s * m.x y - m.t y) '' Icc 0 M.vbar))

section Env

variable (M : Model) (m : Mech) (ε : ℝ)

lemma U_bdd (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (s : ℝ) :
    BddAbove (insert 0 ((fun y => s * m.x y - m.t y) '' Icc 0 M.vbar)) := by
  obtain ⟨⟨_, _, hx01⟩, hIR, hIC⟩ := hm
  have hvS : M.vbar ∈ Icc 0 M.vbar := ⟨hv.le, le_rfl⟩
  refine ⟨M.vbar * m.x M.vbar - m.t M.vbar + ε + |s - M.vbar| + |ε|, ?_⟩
  rintro a (rfl | ⟨y, hy, rfl⟩)
  · have := hIR _ hvS
    have := abs_nonneg (s - M.vbar)
    have := neg_abs_le ε
    linarith
  · have h1 := hIC _ hvS y hy
    have hxy := hx01 y hy
    have h2 : (s - M.vbar) * m.x y ≤ |s - M.vbar| := by
      calc (s - M.vbar) * m.x y ≤ |s - M.vbar| * m.x y := by
            exact mul_le_mul_of_nonneg_right (le_abs_self _) hxy.1
        _ ≤ |s - M.vbar| * 1 := mul_le_mul_of_nonneg_left hxy.2 (abs_nonneg _)
        _ = _ := mul_one _
    have := le_abs_self ε
    have := hIR _ hvS
    show s * m.x y - m.t y ≤ _
    have e : s * m.x y = M.vbar * m.x y + (s - M.vbar) * m.x y := by ring
    have := abs_nonneg ε
    linarith

lemma U_ge_line (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (y : ℝ) (hy : y ∈ Icc 0 M.vbar) (s : ℝ) :
    s * m.x y - m.t y ≤ Uf M m s :=
  le_csSup (U_bdd M m ε hv hm s) (mem_insert_of_mem _ ⟨y, hy, rfl⟩)

lemma U_nonneg (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (s : ℝ) : 0 ≤ Uf M m s :=
  le_csSup (U_bdd M m ε hv hm s) (mem_insert _ _)

lemma U_le_u (hε : 0 ≤ ε) (hm : m ∈ Mset M ε) (z : ℝ) (hz : z ∈ Icc 0 M.vbar) :
    Uf M m z ≤ z * m.x z - m.t z + ε := by
  obtain ⟨_, hIR, hIC⟩ := hm
  apply csSup_le ⟨0, mem_insert _ _⟩
  rintro a (rfl | ⟨y, hy, rfl⟩)
  · have := hIR z hz; linarith
  · have := hIC z hz y hy; linarith

lemma U_mono (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (a b : ℝ) (hab : a ≤ b) :
    Uf M m a ≤ Uf M m b := by
  apply csSup_le ⟨0, mem_insert _ _⟩
  rintro c (rfl | ⟨y, hy, rfl⟩)
  · exact U_nonneg M m ε hv hm b
  · have hxy := hm.1.2.2 y hy
    have := U_ge_line M m ε hv hm y hy b
    have : a * m.x y ≤ b * m.x y := mul_le_mul_of_nonneg_right hab hxy.1
    linarith

lemma U_lip (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (a b : ℝ) (hab : a ≤ b) :
    Uf M m b ≤ Uf M m a + (b - a) := by
  apply csSup_le ⟨0, mem_insert _ _⟩
  rintro c (rfl | ⟨y, hy, rfl⟩)
  · have := U_nonneg M m ε hv hm a; linarith
  · have hxy := hm.1.2.2 y hy
    have := U_ge_line M m ε hv hm y hy a
    have : (b - a) * m.x y ≤ (b - a) * 1 := mul_le_mul_of_nonneg_left hxy.2 (by linarith)
    show b * m.x y - m.t y ≤ _
    nlinarith

lemma U_conv (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (a c : ℝ) :
    Uf M m ((a + c) / 2) ≤ (Uf M m a + Uf M m c) / 2 := by
  apply csSup_le ⟨0, mem_insert _ _⟩
  rintro d (rfl | ⟨y, hy, rfl⟩)
  · have := U_nonneg M m ε hv hm a; have := U_nonneg M m ε hv hm c; linarith
  · have := U_ge_line M m ε hv hm y hy a
    have := U_ge_line M m ε hv hm y hy c
    show (a + c) / 2 * m.x y - m.t y ≤ _
    linarith

end Env

/-- hinge `(s - p)^+`. -/
noncomputable def hinge (p s : ℝ) : ℝ := max (s - p) 0

lemma hinge_cont (p : ℝ) : Continuous (hinge p) := by
  unfold hinge; exact (continuous_id.sub continuous_const).max continuous_const

lemma sum_cell (σ : ℕ → ℝ) (h : ℝ) (hh : 0 < h) (j : ℕ) (s : ℝ) (hs1 : (j:ℝ) * h ≤ s)
    (hs2 : s ≤ ((j:ℝ) + 1) * h) : ∀ n : ℕ,
    ∑ i ∈ Finset.range n, σ i * (hinge ((i:ℝ) * h) s - hinge (((i:ℝ) + 1) * h) s) =
      ∑ i ∈ Finset.range (min n j), σ i * h + (if j < n then σ j * (s - (j:ℝ) * h) else 0) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    rcases lt_trichotomy n j with hnj | hnj | hnj
    · have h1 : min (n+1) j = n + 1 := min_eq_left hnj
      have h2 : min n j = n := min_eq_left hnj.le
      have h3 : ¬ j < n + 1 := by omega
      have h4 : ¬ j < n := by omega
      rw [h1, h2, if_neg h3, if_neg h4, Finset.sum_range_succ]
      have hnj' : ((n:ℝ) + 1) ≤ j := by exact_mod_cast hnj
      have e1 : hinge ((n:ℝ) * h) s = s - n * h := by
        unfold hinge; rw [max_eq_left]; nlinarith
      have e2 : hinge (((n:ℝ) + 1) * h) s = s - (n + 1) * h := by
        unfold hinge; rw [max_eq_left]; nlinarith
      rw [e1, e2]; ring
    · subst hnj
      have h1 : min (n+1) n = n := by omega
      rw [h1, min_self, if_neg (show ¬ n < n by omega), if_pos (show n < n + 1 by omega)]
      have e1 : hinge ((n:ℝ) * h) s = s - n * h := by
        unfold hinge; rw [max_eq_left]; linarith
      have e2 : hinge (((n:ℝ) + 1) * h) s = 0 := by
        unfold hinge; rw [max_eq_right]; linarith
      rw [e1, e2]; ring
    · have h1 : min (n+1) j = j := by omega
      have h2 : min n j = j := by omega
      rw [h1, h2, if_pos hnj, if_pos (show j < n + 1 by omega)]
      have hnj' : (j:ℝ) + 1 ≤ n := by exact_mod_cast hnj
      have e1 : hinge ((n:ℝ) * h) s = 0 := by
        unfold hinge; rw [max_eq_right]; nlinarith
      have e2 : hinge (((n:ℝ) + 1) * h) s = 0 := by
        unfold hinge; rw [max_eq_right]; nlinarith
      rw [e1, e2]; ring

section Grid

variable (M : Model) (m : Mech) (ε : ℝ) (N : ℕ) (h : ℝ)

/-- grid slopes -/
noncomputable def sig (i : ℕ) : ℝ := (Uf M m (((i:ℝ) + 1) * h) - Uf M m ((i:ℝ) * h)) / h

/-- piecewise-linear interpolant of `U` on the grid `r_i = i h`, `i ≤ N`. -/
noncomputable def Uhat (s : ℝ) : ℝ :=
  Uf M m 0 + ∑ i ∈ Finset.range N,
    sig M m h i * (hinge ((i:ℝ) * h) s - hinge (((i:ℝ) + 1) * h) s)

lemma Uhat_cont : Continuous (Uhat M m N h) := by
  unfold Uhat
  apply continuous_const.add
  apply continuous_finsetSum
  intro i _
  exact continuous_const.mul ((hinge_cont _).sub (hinge_cont _))

lemma sig_mul (hh : 0 < h) (i : ℕ) :
    sig M m h i * h = Uf M m (((i:ℝ) + 1) * h) - Uf M m ((i:ℝ) * h) := by
  unfold sig; field_simp

lemma Uhat_cell (hh : 0 < h) (j : ℕ) (hj : j < N) (s : ℝ) (hs1 : (j:ℝ) * h ≤ s)
    (hs2 : s ≤ ((j:ℝ) + 1) * h) :
    Uhat M m N h s = Uf M m ((j:ℝ) * h) + sig M m h j * (s - (j:ℝ) * h) := by
  unfold Uhat
  rw [sum_cell (sig M m h) h hh j s hs1 hs2 N, min_eq_right hj.le, if_pos hj]
  have : ∑ i ∈ Finset.range j, sig M m h i * h = Uf M m ((j:ℝ) * h) - Uf M m 0 := by
    have := Finset.sum_range_sub (fun i : ℕ => Uf M m ((i:ℝ) * h)) j
    rw [Finset.sum_congr rfl (fun i _ => sig_mul M m h hh i)]
    push_cast at this ⊢
    rw [this]; simp
  rw [this]; ring

lemma exists_cell (hN : 0 < N) (hh : 0 < h) (s : ℝ) (hs0 : 0 ≤ s) (hsW : s ≤ (N:ℝ) * h) :
    ∃ j < N, (j:ℝ) * h ≤ s ∧ s ≤ ((j:ℝ) + 1) * h := by
  by_cases hsl : s < (N:ℝ) * h
  · refine ⟨⌊s / h⌋₊, ?_, ?_, ?_⟩
    · have : s / h < N := by rw [div_lt_iff₀ hh]; exact hsl
      exact (Nat.floor_lt (div_nonneg hs0 hh.le)).mpr this
    · have := Nat.floor_le (div_nonneg hs0 hh.le)
      rwa [le_div_iff₀ hh] at this
    · have := Nat.lt_floor_add_one (s / h)
      rw [div_lt_iff₀ hh] at this
      exact this.le
  · refine ⟨N - 1, by omega, ?_, ?_⟩
    · have : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]; nlinarith
    · have : ((N - 1 : ℕ) : ℝ) = (N:ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [this]; nlinarith

lemma sig_nonneg (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (hh : 0 < h) (i : ℕ) :
    0 ≤ sig M m h i := by
  unfold sig
  apply div_nonneg _ hh.le
  have := U_mono M m ε hv hm ((i:ℝ) * h) (((i:ℝ) + 1) * h) (by nlinarith)
  linarith

lemma sig_le_one (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (hh : 0 < h) (i : ℕ) :
    sig M m h i ≤ 1 := by
  unfold sig
  rw [div_le_one hh]
  have := U_lip M m ε hv hm ((i:ℝ) * h) (((i:ℝ) + 1) * h) (by nlinarith)
  linarith

lemma sig_mono (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (hh : 0 < h) (i : ℕ) :
    sig M m h i ≤ sig M m h (i + 1) := by
  unfold sig
  apply div_le_div_of_nonneg_right _ hh.le
  have := U_conv M m ε hv hm ((i:ℝ) * h) (((i:ℝ) + 2) * h)
  have e : ((i:ℝ) * h + ((i:ℝ) + 2) * h) / 2 = ((i:ℝ) + 1) * h := by ring
  rw [e] at this
  push_cast
  have e2 : ((i:ℝ) + 1 + 1) * h = ((i:ℝ) + 2) * h := by ring
  rw [e2]
  linarith

lemma Uhat_ge_line (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (hN : 0 < N) (hh : 0 < h)
    (y : ℝ) (hy : y ∈ Icc 0 M.vbar) (s : ℝ) (hs0 : 0 ≤ s) (hsW : s ≤ (N:ℝ) * h) :
    s * m.x y - m.t y ≤ Uhat M m N h s := by
  obtain ⟨j, hj, hs1, hs2⟩ := exists_cell N h hN hh s hs0 hsW
  rw [Uhat_cell M m N h hh j hj s hs1 hs2]
  have ha := U_ge_line M m ε hv hm y hy ((j:ℝ) * h)
  have hb := U_ge_line M m ε hv hm y hy (((j:ℝ) + 1) * h)
  have hsm := sig_mul M m h hh j
  set a := Uf M m ((j:ℝ) * h) - ((j:ℝ) * h * m.x y - m.t y)
  set b := Uf M m (((j:ℝ) + 1) * h) - (((j:ℝ) + 1) * h * m.x y - m.t y)
  have ha0 : 0 ≤ a := by simp only [a]; linarith
  have hb0 : 0 ≤ b := by simp only [b]; linarith
  have key : (sig M m h j - m.x y) * h = b - a := by
    simp only [a, b]; rw [sub_mul, hsm]; ring
  -- goal: s x - t ≤ U_j + σ (s - r_j)
  have hl0 : 0 ≤ s - (j:ℝ) * h := by linarith
  have hl1 : s - (j:ℝ) * h ≤ h := by linarith
  have goal' : h * ((Uf M m ((j:ℝ) * h) + sig M m h j * (s - (j:ℝ) * h)) - (s * m.x y - m.t y))
      = a * (h - (s - (j:ℝ) * h)) + b * (s - (j:ℝ) * h) := by
    have : h * ((Uf M m ((j:ℝ) * h) + sig M m h j * (s - (j:ℝ) * h)) - (s * m.x y - m.t y))
        = h * a + (sig M m h j - m.x y) * h * (s - (j:ℝ) * h) := by
      simp only [a]; ring
    rw [this, key]; ring
  have : 0 ≤ h * ((Uf M m ((j:ℝ) * h) + sig M m h j * (s - (j:ℝ) * h)) - (s * m.x y - m.t y)) := by
    rw [goal']
    have := mul_nonneg ha0 (sub_nonneg.mpr hl1)
    have := mul_nonneg hb0 hl0
    linarith
  have := (mul_nonneg_iff_of_pos_left hh).mp this
  linarith

lemma Uhat_le (hv : 0 < M.vbar) (hm : m ∈ Mset M ε) (hN : 0 < N) (hh : 0 < h)
    (s : ℝ) (hs0 : 0 ≤ s) (hsW : s ≤ (N:ℝ) * h) :
    Uhat M m N h s ≤ Uf M m s + h := by
  obtain ⟨j, hj, hs1, hs2⟩ := exists_cell N h hN hh s hs0 hsW
  rw [Uhat_cell M m N h hh j hj s hs1 hs2]
  have h1 := sig_le_one M m ε h hv hm hh j
  have h2 := sig_nonneg M m ε h hv hm hh j
  have h3 := U_mono M m ε hv hm ((j:ℝ) * h) s hs1
  have : sig M m h j * (s - (j:ℝ) * h) ≤ 1 * h := by
    apply mul_le_mul h1 (by linarith) (by linarith) zero_le_one
  linarith

end Grid

end AIC1T1

-- ===== part C =====

open MeasureTheory Set ApproxIC.UpperBound

namespace AIC1T1

section Path

variable (pstar e c : ℝ)

/-- the gap `δ(z) = e + c |z - p⋆|` of the path `w(z) = z + δ(z)` -/
noncomputable def del (z : ℝ) : ℝ := e + c * |z - pstar|

/-- the path `w(z) = z + δ(z)` -/
noncomputable def wp (z : ℝ) : ℝ := z + del pstar e c z

/-- the dual weight of the posted price `p` -/
noncomputable def bp (p z : ℝ) : ℝ :=
  z * (hinge p (wp pstar e c z) - hinge p z) / del pstar e c z - hinge p z

lemma del_pos (he : 0 < e) (hc : 0 ≤ c) (z : ℝ) : 0 < del pstar e c z := by
  unfold del; have := abs_nonneg (z - pstar); positivity

lemma del_cont : Continuous (del pstar e c) := by
  unfold del; exact continuous_const.add (continuous_const.mul (continuous_id.sub continuous_const).abs)

lemma wp_cont : Continuous (wp pstar e c) := by
  unfold wp; exact continuous_id.add (del_cont pstar e c)

lemma bp_cont (he : 0 < e) (hc : 0 ≤ c) (p : ℝ) : Continuous (bp pstar e c p) := by
  unfold bp
  apply Continuous.sub _ (hinge_cont p)
  apply Continuous.div _ (del_cont pstar e c) (fun z => (del_pos pstar e c he hc z).ne')
  exact continuous_id.mul (((hinge_cont p).comp (wp_cont pstar e c)).sub (hinge_cont p))

lemma bp_eq_of_le (he : 0 < e) (hc : 0 ≤ c) (p z : ℝ) (hpz : p ≤ z) : bp pstar e c p z = p := by
  have hd := del_pos pstar e c he hc z
  unfold bp hinge
  have h1 : max (z - p) 0 = z - p := max_eq_left (by linarith)
  have h2 : max (wp pstar e c z - p) 0 = wp pstar e c z - p := by
    apply max_eq_left; unfold wp; linarith
  rw [h1, h2]
  have : wp pstar e c z - p - (z - p) = del pstar e c z := by unfold wp; ring
  rw [this, mul_div_assoc, div_self hd.ne']; ring

lemma bp_bounds (he : 0 < e) (hc : 0 ≤ c) (p z : ℝ) (hz : 0 ≤ z) (hzp : z ≤ p) :
    0 ≤ bp pstar e c p z ∧ bp pstar e c p z ≤ z := by
  have hd := del_pos pstar e c he hc z
  unfold bp
  have h1 : hinge p z = 0 := by unfold hinge; exact max_eq_right (by linarith)
  rw [h1, sub_zero, sub_zero]
  have h2 : 0 ≤ hinge p (wp pstar e c z) := le_max_right _ _
  have h3 : hinge p (wp pstar e c z) ≤ del pstar e c z := by
    unfold hinge; apply max_le _ hd.le; unfold wp; linarith
  constructor
  · positivity
  · rw [mul_div_assoc]
    have : hinge p (wp pstar e c z) / del pstar e c z ≤ 1 := (div_le_one hd).mpr h3
    nlinarith [div_nonneg h2 hd.le]

lemma bp_nonneg (he : 0 < e) (hc : 0 ≤ c) (p z : ℝ) (hp : 0 ≤ p) (hz : 0 ≤ z) :
    0 ≤ bp pstar e c p z := by
  rcases le_total p z with h | h
  · rw [bp_eq_of_le pstar e c he hc p z h]; exact hp
  · exact (bp_bounds pstar e c he hc p z hz h).1

lemma bp_zero (he : 0 < e) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) (p z : ℝ)
    (hz : z ≤ p - 2 * del pstar e c p) : bp pstar e c p z = 0 := by
  have hdp := del_pos pstar e c he hc p
  unfold bp
  have h1 : hinge p z = 0 := by unfold hinge; exact max_eq_right (by linarith)
  have h2 : hinge p (wp pstar e c z) = 0 := by
    unfold hinge; apply max_eq_right
    unfold wp del
    have t1 : |z - pstar| ≤ |p - pstar| + |z - p| := by
      have := abs_sub_le z p pstar
      linarith [abs_sub_comm p pstar]
    have t2 : |z - p| = p - z := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [t2] at t1
    have t3 : c * |z - pstar| ≤ c * (|p - pstar| + (p - z)) := mul_le_mul_of_nonneg_left t1 hc
    unfold del at hz hdp
    nlinarith
  rw [h1, h2]; simp

end Path

/-- Abel summation bound. -/
lemma abel_le (σ Ψ : ℕ → ℝ) (S : ℝ) (N : ℕ) (hσ0 : ∀ i, 0 ≤ σ i) (hσ1 : ∀ i, σ i ≤ 1)
    (hmono : ∀ i, σ i ≤ σ (i + 1)) (hΨ : ∀ i < N, Ψ i ≤ S) (hΨN : 0 ≤ Ψ N) (hS : 0 ≤ S) :
    ∑ i ∈ Finset.range N, σ i * (Ψ i - Ψ (i + 1)) ≤ S := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simpa using hS
  have aux : ∀ n, n + 1 ≤ N → ∑ i ∈ Finset.range (n + 1), σ i * (Ψ i - Ψ (i + 1)) ≤
      σ n * S - σ n * Ψ (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro h1
      simp only [zero_add, Finset.sum_range_one]
      have := hΨ 0 (by omega)
      nlinarith [hσ0 0]
    | succ n ih =>
      intro h1
      rw [Finset.sum_range_succ]
      have := ih (by omega)
      have h2 := hΨ (n + 1) (by omega)
      have h3 := hmono n
      nlinarith
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := aux n le_rfl
  have h1 := hσ0 n; have h2 := hσ1 n
  nlinarith

lemma int_inv_lin (e c L : ℝ) (he : 0 < e) (hc : 0 < c) (hL : 0 ≤ L) :
    ∫ s in (0:ℝ)..L, (e + c * s)⁻¹ = c⁻¹ * Real.log ((e + c * L) / e) := by
  have : (fun s : ℝ => (e + c * s)⁻¹) = fun s => (fun x : ℝ => x⁻¹) (c * s + e) := by
    funext s; ring_nf
  rw [this, intervalIntegral.integral_comp_mul_add (fun x : ℝ => x⁻¹) hc.ne' e]
  rw [integral_inv_of_pos (by simp [he]) (by nlinarith)]
  simp only [mul_zero, zero_add, smul_eq_mul]
  ring_nf

lemma int_inv_del (pstar e c vbar : ℝ) (he : 0 < e) (hc : 0 < c) (hp0 : 0 ≤ pstar)
    (hpv : pstar ≤ vbar) :
    ∫ z in (0:ℝ)..vbar, (del pstar e c z)⁻¹ ≤ 2 * (c⁻¹ * Real.log ((e + c * vbar) / e)) := by
  have hcont : Continuous (fun z => (del pstar e c z)⁻¹) :=
    (del_cont pstar e c).inv₀ (fun z => (del_pos pstar e c he hc.le z).ne')
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable 0 pstar)
    (hcont.intervalIntegrable pstar vbar)]
  have hL : ∫ z in (0:ℝ)..pstar, (del pstar e c z)⁻¹ = ∫ s in (0:ℝ)..pstar, (e + c * s)⁻¹ := by
    have : ∫ z in (0:ℝ)..pstar, (del pstar e c z)⁻¹ =
        ∫ z in (0:ℝ)..pstar, (fun s => (e + c * s)⁻¹) (pstar - z) := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le hp0] at hz
      simp only [del]
      rw [abs_sub_comm, abs_of_nonneg (by linarith [hz.2])]
    rw [this, intervalIntegral.integral_comp_sub_left (fun s => (e + c * s)⁻¹)]
    simp
  have hR : ∫ z in pstar..vbar, (del pstar e c z)⁻¹ = ∫ s in (0:ℝ)..(vbar - pstar), (e + c * s)⁻¹ := by
    have : ∫ z in pstar..vbar, (del pstar e c z)⁻¹ =
        ∫ z in pstar..vbar, (fun s => (e + c * s)⁻¹) (z - pstar) := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le hpv] at hz
      simp only [del]
      rw [abs_of_nonneg (by linarith [hz.1])]
    rw [this, intervalIntegral.integral_comp_sub_right (fun s => (e + c * s)⁻¹)]
    simp
  rw [hL, hR, int_inv_lin e c _ he hc hp0, int_inv_lin e c _ he hc (by linarith)]
  have hci : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
  have m1 : Real.log ((e + c * pstar) / e) ≤ Real.log ((e + c * vbar) / e) := by
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  have m2 : Real.log ((e + c * (vbar - pstar)) / e) ≤ Real.log ((e + c * vbar) / e) := by
    apply Real.log_le_log (div_pos (by nlinarith) he)
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  have := mul_le_mul_of_nonneg_left m1 hci
  have := mul_le_mul_of_nonneg_left m2 hci
  linarith

end AIC1T1

-- ===== part D =====

open MeasureTheory Set ApproxIC.UpperBound

namespace AIC1T1

/-- `∫_0^{v̄} f(z) b_p(z) dz`, the dual value of the posted price `p`. -/
noncomputable def Lb (M : Model) (pstar e c p : ℝ) : ℝ :=
  ∫ z in (0:ℝ)..M.vbar, M.f z * bp pstar e c p z

lemma Fp_ii (M : Model) (hM : M.Standing) (pstar e c p : ℝ) (he : 0 < e) (hc : 0 ≤ c)
    (a b : ℝ) : IntervalIntegrable (fun z => M.f z * bp pstar e c p z) volume a b :=
  (f_ii M hM a b).mul_continuousOn (bp_cont pstar e c he hc p).continuousOn

lemma Lb_nonneg (M : Model) (hM : M.Standing) (pstar e c p : ℝ) (he : 0 < e) (hc : 0 ≤ c)
    (hp : 0 ≤ p) : 0 ≤ Lb M pstar e c p :=
  intervalIntegral.integral_nonneg hM.1.le
    (fun z hz => mul_nonneg (hM.2.1 z) (bp_nonneg pstar e c he hc p z hp hz.1))

lemma Lb_le (M : Model) (hM : M.Standing) (B : ℝ) (hB : ∀ v, M.f v ≤ B) (pstar e c : ℝ)
    (he : 0 < e) (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) (p : ℝ) (hp : 0 ≤ p) :
    Lb M pstar e c p ≤ R M p + 2 * M.vbar * B * del pstar e c p := by
  set d := del pstar e c p with hd
  have hd0 : 0 < d := del_pos pstar e c he hc p
  set P := min p M.vbar with hPdef
  set q := min (max 0 (p - 2 * d)) P with hqdef
  have hv := hM.1
  have hB0 : 0 ≤ B := (hM.2.1 0).trans (hB 0)
  have hP0 : 0 ≤ P := le_min hp hv.le
  have hPv : P ≤ M.vbar := min_le_right _ _
  have hPp : P ≤ p := min_le_left _ _
  have hq0 : 0 ≤ q := le_min (le_max_left _ _) hP0
  have hqP : q ≤ P := min_le_right _ _
  have hg := Fp_ii M hM pstar e c p he hc
  unfold Lb
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg 0 q) (hg q M.vbar),
    ← intervalIntegral.integral_add_adjacent_intervals (hg q P) (hg P M.vbar)]
  -- piece 1
  have I1 : ∫ z in (0:ℝ)..q, M.f z * bp pstar e c p z = 0 := by
    have : ∫ z in (0:ℝ)..q, M.f z * bp pstar e c p z = ∫ z in (0:ℝ)..q, (0:ℝ) := by
      apply intervalIntegral.integral_congr
      intro z hz
      rw [uIcc_of_le hq0] at hz
      show M.f z * bp pstar e c p z = 0
      rcases eq_or_lt_of_le hz.1 with h0 | h0
      · subst h0
        have : bp pstar e c p 0 = 0 := by
          unfold bp hinge; rw [max_eq_right (by linarith : (0:ℝ) - p ≤ 0)]; simp
        rw [this, mul_zero]
      · have hzq : z ≤ max 0 (p - 2 * d) := hz.2.trans (min_le_left _ _)
        have hz2 : z ≤ p - 2 * d := by
          rcases le_max_iff.mp hzq with h1 | h1
          · linarith
          · exact h1
        rw [bp_zero pstar e c he hc hc2 p z hz2, mul_zero]
    rw [this]; simp
  -- piece 2
  have I2 : ∫ z in q..P, M.f z * bp pstar e c p z ≤ 2 * M.vbar * B * d := by
    have h1 : ∫ z in q..P, M.f z * bp pstar e c p z ≤ ∫ z in q..P, B * M.vbar := by
      apply intervalIntegral.integral_mono_on hqP (hg q P) (continuous_const.intervalIntegrable _ _)
      intro z hz
      have hz0 : 0 ≤ z := hq0.trans hz.1
      have hzp : z ≤ p := hz.2.trans hPp
      have hb := bp_bounds pstar e c he hc p z hz0 hzp
      calc M.f z * bp pstar e c p z ≤ B * z := mul_le_mul (hB z) hb.2 hb.1 hB0
        _ ≤ B * M.vbar := mul_le_mul_of_nonneg_left (hz.2.trans hPv) hB0
    rw [intervalIntegral.integral_const, smul_eq_mul] at h1
    have h2 : P - q ≤ 2 * d := by
      have : P - 2 * d ≤ q := le_min (le_max_of_le_right (by linarith)) (by linarith)
      linarith
    have h3 : (P - q) * (B * M.vbar) ≤ (2 * d) * (B * M.vbar) :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    linarith
  -- piece 3
  have I3 : ∫ z in P..M.vbar, M.f z * bp pstar e c p z ≤ R M p := by
    rcases le_total p M.vbar with hpv | hpv
    · have hPe : P = p := min_eq_left hpv
      rw [hPe]
      have : ∫ z in p..M.vbar, M.f z * bp pstar e c p z = ∫ z in p..M.vbar, p * M.f z := by
        apply intervalIntegral.integral_congr
        intro z hz
        rw [uIcc_of_le hpv] at hz
        show M.f z * bp pstar e c p z = p * M.f z
        rw [bp_eq_of_le pstar e c he hc p z hz.1]; ring
      rw [this, intervalIntegral.integral_const_mul, ← cdfBar_eq M hM]
      unfold R; exact le_rfl
    · have hPe : P = M.vbar := min_eq_right hpv
      rw [hPe, intervalIntegral.integral_same, R_eq_zero M hM p hpv]
  rw [I1]
  linarith

section Rev

variable (M : Model) (m : Mech) (ε : ℝ) (pstar e c : ℝ) (N : ℕ) (h : ℝ)

lemma t_bound (hv : 0 < M.vbar) (hε : 0 ≤ ε) (hm : m ∈ Mset M ε) (he : 0 < e) (hc : 0 ≤ c)
    (hN : 0 < N) (hh : 0 < h) (z : ℝ) (hz : z ∈ Icc 0 M.vbar)
    (hW : wp pstar e c z ≤ (N:ℝ) * h) :
    m.t z ≤ z * (Uhat M m N h (wp pstar e c z) - Uhat M m N h z + (ε + h)) / del pstar e c z
      - Uhat M m N h z + (ε + h) := by
  have hd := del_pos pstar e c he hc z
  have hwz : wp pstar e c z = z + del pstar e c z := rfl
  have hz0 := hz.1
  have hzW : z ≤ (N:ℝ) * h := by linarith
  have hU1 := Uhat_le M m ε N h hv hm hN hh z hz0 hzW
  have hU2 := U_le_u M m ε hε hm z hz
  have hline := Uhat_ge_line M m ε N h hv hm hN hh z hz (wp pstar e c z) (by linarith) hW
  have hx : m.x z ≤ (Uhat M m N h (wp pstar e c z) - Uhat M m N h z + (ε + h)) / del pstar e c z := by
    rw [le_div_iff₀ hd]
    have : wp pstar e c z * m.x z - m.t z = (z * m.x z - m.t z) + m.x z * del pstar e c z := by
      rw [hwz]; ring
    linarith
  have h2 : z * m.x z ≤ z * ((Uhat M m N h (wp pstar e c z) - Uhat M m N h z + (ε + h)) /
      del pstar e c z) := mul_le_mul_of_nonneg_left hx hz0
  rw [mul_div_assoc]
  linarith

lemma rev_bound (hM : M.Standing) (hε : 0 < ε) (hm : m ∈ Mset M ε) (he : 0 < e) (hc : 0 ≤ c)
    (hN : 0 < N) (hh : 0 < h) (hW : ∀ z ∈ Icc 0 M.vbar, wp pstar e c z ≤ (N:ℝ) * h)
    (S : ℝ) (hS : 0 ≤ S) (hLb : ∀ i : ℕ, i < N → Lb M pstar e c ((i:ℝ) * h) ≤ S) :
    revenue M m ≤ S + (ε + h) * ∫ z in (0:ℝ)..M.vbar, M.f z * (z / del pstar e c z + 1) := by
  have hv := hM.1
  set Q := ∫ z in (0:ℝ)..M.vbar, M.f z * (z / del pstar e c z + 1) with hQdef
  have hdc : Continuous (del pstar e c) := del_cont pstar e c
  have hdne : ∀ z, del pstar e c z ≠ 0 := fun z => (del_pos pstar e c he hc z).ne'
  have hQ0 : 0 ≤ Q := by
    apply intervalIntegral.integral_nonneg hv.le
    intro z hz
    apply mul_nonneg (hM.2.1 z)
    have := del_pos pstar e c he hc z
    have : 0 ≤ z / del pstar e c z := div_nonneg hz.1 this.le
    linarith
  have hεh : 0 ≤ ε + h := by linarith
  by_cases hint : IntervalIntegrable (fun v => m.t v * M.f v) volume 0 M.vbar
  swap
  · unfold revenue
    rw [intervalIntegral.integral_undef hint]
    positivity
  set Uh := Uhat M m N h with hUh
  have hUc : Continuous Uh := Uhat_cont M m N h
  set G : ℝ → ℝ := fun z => z * (Uh (wp pstar e c z) - Uh z + (ε + h)) / del pstar e c z
      - Uh z + (ε + h) with hGdef
  have hGc : Continuous G := by
    simp only [hGdef]
    apply Continuous.add _ continuous_const
    apply Continuous.sub _ hUc
    apply Continuous.div _ hdc hdne
    exact continuous_id.mul (((hUc.comp (wp_cont pstar e c)).sub hUc).add continuous_const)
  have step1 : revenue M m ≤ ∫ z in (0:ℝ)..M.vbar, M.f z * G z := by
    unfold revenue
    apply intervalIntegral.integral_mono_on hv.le hint
      ((f_ii M hM 0 M.vbar).mul_continuousOn hGc.continuousOn)
    intro z hz
    have := t_bound M m ε pstar e c N h hv hε.le hm he hc hN hh z hz (hW z hz)
    have hf := hM.2.1 z
    calc m.t z * M.f z = M.f z * m.t z := mul_comm _ _
      _ ≤ M.f z * G z := mul_le_mul_of_nonneg_left this hf
  -- decomposition of the integrand
  set σ := sig M m h with hσ
  set F : ℕ → ℝ → ℝ := fun i z => M.f z * bp pstar e c ((i:ℝ) * h) z with hF
  have hFii : ∀ i a b, IntervalIntegrable (F i) volume a b := fun i a b =>
    Fp_ii M hM pstar e c _ he hc a b
  have hident : ∀ z, M.f z * G z =
      (∑ i ∈ Finset.range N, σ i * (F i z - F (i + 1) z)) - Uf M m 0 * M.f z
        + (ε + h) * (M.f z * (z / del pstar e c z + 1)) := by
    intro z
    have hsum : ∑ i ∈ Finset.range N, σ i * (F i z - F (i + 1) z) =
        M.f z * (z * ((∑ i ∈ Finset.range N, σ i * (hinge ((i:ℝ) * h) (wp pstar e c z) -
          hinge (((i:ℝ) + 1) * h) (wp pstar e c z))) -
          ∑ i ∈ Finset.range N, σ i * (hinge ((i:ℝ) * h) z - hinge (((i:ℝ) + 1) * h) z)) /
            del pstar e c z - ∑ i ∈ Finset.range N, σ i * (hinge ((i:ℝ) * h) z -
              hinge (((i:ℝ) + 1) * h) z)) := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib,
        Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [hF, bp]
      push_cast
      ring
    rw [hsum]
    simp only [hGdef, hUh, Uhat]
    ring
  have step2 : ∫ z in (0:ℝ)..M.vbar, M.f z * G z =
      (∑ i ∈ Finset.range N, σ i * (Lb M pstar e c ((i:ℝ) * h) - Lb M pstar e c (((i + 1 : ℕ):ℝ) * h)))
        - Uf M m 0 * 1 + (ε + h) * Q := by
    rw [intervalIntegral.integral_congr (fun z _ => hident z)]
    have hA : IntervalIntegrable (fun z => ∑ i ∈ Finset.range N, σ i * (F i z - F (i + 1) z))
        volume 0 M.vbar := by
      have := IntervalIntegrable.sum (μ := volume) (a := 0) (b := M.vbar) (Finset.range N)
        (f := fun i z => σ i * (F i z - F (i + 1) z))
        (fun i _ => ((hFii i 0 M.vbar).sub (hFii (i+1) 0 M.vbar)).const_mul (σ i))
      have e : (∑ i ∈ Finset.range N, fun z => σ i * (F i z - F (i + 1) z)) =
          fun z => ∑ i ∈ Finset.range N, σ i * (F i z - F (i + 1) z) := by
        funext z; simp [Finset.sum_apply]
      rw [e] at this; exact this
    have hB' : IntervalIntegrable (fun z => Uf M m 0 * M.f z) volume 0 M.vbar :=
      (f_ii M hM 0 M.vbar).const_mul _
    have hC : IntervalIntegrable (fun z => (ε + h) * (M.f z * (z / del pstar e c z + 1)))
        volume 0 M.vbar := by
      apply IntervalIntegrable.const_mul
      apply (f_ii M hM 0 M.vbar).mul_continuousOn
      exact ((continuous_id.div hdc hdne).add continuous_const).continuousOn
    rw [intervalIntegral.integral_add (hA.sub hB') hC, intervalIntegral.integral_sub hA hB',
      intervalIntegral.integral_finset_sum (fun i _ =>
        ((hFii i 0 M.vbar).sub (hFii (i+1) 0 M.vbar)).const_mul (σ i))]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hM.2.2.2.2]
    congr 2
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hFii i 0 M.vbar)
      (hFii (i+1) 0 M.vbar)]
    rfl
  have step3 : (∑ i ∈ Finset.range N, σ i * (Lb M pstar e c ((i:ℝ) * h) -
      Lb M pstar e c (((i + 1 : ℕ):ℝ) * h))) ≤ S := by
    apply abel_le σ (fun i => Lb M pstar e c ((i:ℝ) * h)) S N
      (sig_nonneg M m ε h hv hm hh) (sig_le_one M m ε h hv hm hh) (sig_mono M m ε h hv hm hh)
      hLb (Lb_nonneg M hM pstar e c _ he hc (by positivity)) hS
  have hU0 := U_nonneg M m ε hv hm 0
  rw [step2] at step1
  nlinarith

end Rev

end AIC1T1

-- ===== part E =====

open MeasureTheory Set ApproxIC.UpperBound

namespace AIC1T1

/-- the posted price `p⋆` (ties broken against selling) -/
noncomputable def postMech (pstar : ℝ) : Mech :=
  ⟨fun v => if pstar < v then 1 else 0, fun v => if pstar < v then pstar else 0⟩

lemma rev_le_vbar (M : Model) (hM : M.Standing) (ε : ℝ) (m : Mech) (hm : m ∈ Mset M ε) :
    revenue M m ≤ M.vbar := by
  have hv := hM.1
  unfold revenue
  by_cases hint : IntervalIntegrable (fun v => m.t v * M.f v) volume 0 M.vbar
  · have h1 : ∫ v in (0:ℝ)..M.vbar, m.t v * M.f v ≤ ∫ v in (0:ℝ)..M.vbar, M.vbar * M.f v := by
      apply intervalIntegral.integral_mono_on hv.le hint ((f_ii M hM 0 M.vbar).const_mul _)
      intro v hv'
      have hIR := hm.2.1 v hv'
      have hx := hm.1.2.2 v hv'
      have : m.t v ≤ M.vbar := by nlinarith [hx.1, hx.2, hv'.1, hv'.2]
      exact mul_le_mul_of_nonneg_right this (hM.2.1 v)
    rw [intervalIntegral.integral_const_mul, hM.2.2.2.2, mul_one] at h1
    exact h1
  · rw [intervalIntegral.integral_undef hint]; exact hv.le

lemma opt_ge (M : Model) (hM : M.Standing) (pstar : ℝ) (hp : pstar ∈ Icc 0 M.vbar) :
    R M pstar ≤ optRev M 0 := by
  have hmem : postMech pstar ∈ Mset M 0 := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
    · exact Measurable.ite measurableSet_Ioi measurable_const measurable_const
    · intro v _
      simp only [postMech]
      split_ifs <;> simp
    · intro v _
      simp only [postMech]
      split_ifs with h
      · linarith
      · simp
    · intro v _ v' _
      simp only [postMech]
      split_ifs with h1 h2 h2 <;> linarith
  have hrev : revenue M (postMech pstar) = R M pstar := by
    unfold revenue
    have hg : ∀ a b, IntervalIntegrable (fun v => (postMech pstar).t v * M.f v) volume a b := by
      intro a b
      have : (fun v => (postMech pstar).t v * M.f v) =
          fun v => M.f v * (if pstar < v then pstar else 0) := by
        funext v; simp only [postMech]; ring
      rw [this]
      have hb : IntervalIntegrable (fun v => M.f v * pstar) volume a b :=
        (f_ii M hM a b).mul_const pstar
      refine hb.mono_fun ?_ ?_
      · have hm' : Measurable (fun v : ℝ => if pstar < v then pstar else (0:ℝ)) :=
          Measurable.ite measurableSet_Ioi measurable_const measurable_const
        exact (intervalIntegrable_iff.mp (f_ii M hM a b)).aestronglyMeasurable.mul
          hm'.aestronglyMeasurable
      · refine Filter.Eventually.of_forall (fun v => ?_)
        simp only [norm_mul, Real.norm_eq_abs]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        split_ifs <;> simp [abs_nonneg]
    rw [← intervalIntegral.integral_add_adjacent_intervals (hg 0 pstar) (hg pstar M.vbar)]
    have h1 : ∫ v in (0:ℝ)..pstar, (postMech pstar).t v * M.f v = 0 := by
      have : ∫ v in (0:ℝ)..pstar, (postMech pstar).t v * M.f v = ∫ v in (0:ℝ)..pstar, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hp.1] at hv
        simp only [postMech, if_neg (not_lt.mpr hv.2), zero_mul]
      rw [this]; simp
    have h2 : ∫ v in pstar..M.vbar, (postMech pstar).t v * M.f v =
        ∫ v in pstar..M.vbar, pstar * M.f v := by
      apply intervalIntegral.integral_congr_ae
      refine Filter.Eventually.of_forall (fun v hv => ?_)
      rw [uIoc_of_le hp.2] at hv
      simp only [postMech, if_pos hv.1]
    rw [h1, h2, intervalIntegral.integral_const_mul, ← cdfBar_eq M hM]
    unfold R; ring
  have hbdd : BddAbove (revenue M '' Mset M 0) := by
    refine ⟨M.vbar, ?_⟩
    rintro r ⟨m, hm, rfl⟩
    exact rev_le_vbar M hM 0 m hm
  rw [← hrev]
  exact le_csSup hbdd ⟨_, hmem, rfl⟩

/-- the key pointwise estimate on the dual value of each posted price -/
lemma price_bound (M : Model) (hM : M.Standing) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) (A : ℝ) (hA : 0 ≤ A) (c0 : ℝ)
    (hfar : ∀ p, 0 ≤ p → p ∉ Ioo (pstar - ℓ) (pstar + ℓ) → R M p ≤ R M pstar - c0)
    (W : ℝ) (τ : ℝ) (hτ : 0 < τ) (hsmall : A * (τ ^ α + τ ^ α / τ * W) ≤ c0)
    (p : ℝ) (hp0 : 0 ≤ p) (hpW : |p - pstar| ≤ W) :
    R M p + A * del pstar (τ ^ α) (τ ^ α / τ) p ≤
      R M pstar + A * τ ^ α + A * (A / κL) ^ (1 / (α - 1)) * τ ^ α := by
  have hα : 1 < α := hD.2.2.2.1
  have hκL : 0 < κL := hD.2.2.2.2.1
  have hdrop := R_drop M hM pstar α κL κU ℓ hD
  set e := τ ^ α with he
  set c := τ ^ α / τ with hc
  have he0 : 0 < e := Real.rpow_pos_of_pos hτ α
  have hc0 : 0 < c := div_pos he0 hτ
  set T := (A / κL) ^ (1 / (α - 1)) with hT
  have hT0 : 0 ≤ T := Real.rpow_nonneg (div_nonneg hA hκL.le) _
  set d := |p - pstar| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  unfold del
  rw [← hd]
  have hAT : 0 ≤ A * T * e := by positivity
  by_cases hN : p ∈ Ioo (pstar - ℓ) (pstar + ℓ)
  · have h1 := hdrop p hN
    rw [← hd] at h1
    -- show A c d ≤ κL d^α + A T e
    have key : A * (c * d) ≤ κL * d ^ α + A * T * e := by
      by_cases hdT : d ≤ T * τ
      · have : c * d ≤ c * (T * τ) := mul_le_mul_of_nonneg_left hdT hc0.le
        have hce : c * (T * τ) = T * e := by
          rw [hc, he]; field_simp
        have := mul_le_mul_of_nonneg_left this hA
        have : 0 ≤ κL * d ^ α := mul_nonneg hκL.le (Real.rpow_nonneg hd0 _)
        nlinarith
      · push_neg at hdT
        have hdpos : 0 < d := lt_of_le_of_lt (by positivity) hdT
        have hα1 : 0 ≤ α - 1 := by linarith
        have h2 : (T * τ) ^ (α - 1) ≤ d ^ (α - 1) :=
          Real.rpow_le_rpow (by positivity) hdT.le hα1
        have h3 : (T * τ) ^ (α - 1) = A / κL * c := by
          rw [Real.mul_rpow hT0 hτ.le, hT, ← Real.rpow_mul (div_nonneg hA hκL.le)]
          rw [show 1 / (α - 1) * (α - 1) = 1 by
            have : α - 1 ≠ 0 := by linarith
            field_simp, Real.rpow_one,
            Real.rpow_sub_one hτ.ne']
        have h4 : d ^ α = d ^ (α - 1) * d := by
          rw [Real.rpow_sub_one hdpos.ne']; field_simp
        rw [h3] at h2
        have h5 : A * c ≤ κL * d ^ (α - 1) := by
          have := mul_le_mul_of_nonneg_left h2 hκL.le
          rw [show κL * (A / κL * c) = A * c by field_simp] at this
          exact this
        have h6 : A * c * d ≤ κL * d ^ (α - 1) * d := mul_le_mul_of_nonneg_right h5 hd0
        rw [h4]
        nlinarith
    nlinarith
  · have h1 := hfar p hp0 hN
    have : A * (e + c * d) ≤ A * (e + c * W) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hA
    have : 0 ≤ A * e := by positivity
    nlinarith

lemma Q_bound (M : Model) (hM : M.Standing) (B : ℝ) (hB : ∀ v, M.f v ≤ B) (pstar e c : ℝ)
    (he : 0 < e) (hc : 0 < c) (hp : pstar ∈ Icc 0 M.vbar) :
    ∫ z in (0:ℝ)..M.vbar, M.f z * (z / del pstar e c z + 1) ≤
      1 + B * M.vbar * (2 * (c⁻¹ * Real.log ((e + c * M.vbar) / e))) := by
  have hv := hM.1
  have hB0 : 0 ≤ B := (hM.2.1 0).trans (hB 0)
  have hdc := del_cont pstar e c
  have hdne : ∀ z, del pstar e c z ≠ 0 := fun z => (del_pos pstar e c he hc.le z).ne'
  have hinv : Continuous (fun z => (del pstar e c z)⁻¹) := hdc.inv₀ hdne
  have h1 : ∫ z in (0:ℝ)..M.vbar, M.f z * (z / del pstar e c z + 1) ≤
      ∫ z in (0:ℝ)..M.vbar, (B * M.vbar * (del pstar e c z)⁻¹ + M.f z) := by
    apply intervalIntegral.integral_mono_on hv.le
    · apply (f_ii M hM 0 M.vbar).mul_continuousOn
      exact ((continuous_id.div hdc hdne).add continuous_const).continuousOn
    · exact ((hinv.const_mul _).intervalIntegrable _ _).add (f_ii M hM 0 M.vbar)
    intro z hz
    have hd := del_pos pstar e c he hc.le z
    have hf := hM.2.1 z
    have h2 : M.f z * (z / del pstar e c z) ≤ B * M.vbar * (del pstar e c z)⁻¹ := by
      rw [div_eq_mul_inv]
      have : M.f z * z ≤ B * M.vbar := mul_le_mul (hB z) hz.2 hz.1 hB0
      have := mul_le_mul_of_nonneg_right this (inv_nonneg.mpr hd.le)
      linarith [mul_assoc (M.f z) z (del pstar e c z)⁻¹]
    nlinarith
  rw [intervalIntegral.integral_add ((hinv.const_mul _).intervalIntegrable _ _)
    (f_ii M hM 0 M.vbar), intervalIntegral.integral_const_mul, hM.2.2.2.2] at h1
  have h3 := int_inv_del pstar e c M.vbar he hc hp.1 hp.2
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ B * M.vbar)
  linarith

/-- The core estimate, parametrized by `τ` (with `ε ≤ τ^{2α-1}`). -/
lemma core (M : Model) (hM : M.Assumption1) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) :
    ∃ K > 0, ∃ τ0 > 0, ∀ τ : ℝ, 0 < τ → τ ≤ τ0 → ∀ ε : ℝ, 0 < ε → ε ≤ τ ^ α * (τ ^ α / τ) →
      ∀ m ∈ Mset M ε, revenue M m ≤ R M pstar + τ ^ α * (K + K * Real.log (1 + M.vbar / τ)) := by
  have hMs := hM.1
  have hv := hMs.1
  have hα : 1 < α := hD.2.2.2.1
  have hκL : 0 < κL := hD.2.2.2.2.1
  have hpI : pstar ∈ Icc 0 M.vbar := ⟨hD.1.1.le, hD.1.2.le⟩
  obtain ⟨B, hB0, hB⟩ := f_bdd M hM
  obtain ⟨c0, hc0, hfar⟩ := far_gap M hMs pstar α κL κU ℓ hD
  set A := 2 * M.vbar * B with hA
  have hA0 : 0 < A := by positivity
  set W := M.vbar + 1 with hW
  set M0 := A * (A / κL) ^ (1 / (α - 1)) with hM0
  have hM00 : 0 ≤ M0 := by positivity
  set κs := min (1 / 2) (min (1 / (1 + M.vbar)) (c0 / (A * (1 + W)))) with hκs
  have hκs0 : 0 < κs := by positivity
  set τ0 := min 1 (κs ^ (1 / (α - 1))) with hτ0
  have hτ00 : 0 < τ0 := lt_min one_pos (Real.rpow_pos_of_pos hκs0 _)
  set K := max (A + M0 + 1) (4 * B * M.vbar) with hK
  have hK0 : 0 < K := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  refine ⟨K, hK0, τ0, hτ00, ?_⟩
  intro τ hτ hττ0 ε hε hετ m hm
  set e := τ ^ α with he
  set c := τ ^ α / τ with hc
  have he0 : 0 < e := Real.rpow_pos_of_pos hτ α
  have hc0' : 0 < c := div_pos he0 hτ
  have hτ1 : τ ≤ 1 := hττ0.trans (min_le_left _ _)
  have hcpow : c = τ ^ (α - 1) := by rw [hc, Real.rpow_sub_one hτ.ne']
  have hcκ : c ≤ κs := by
    rw [hcpow]
    have h1 : τ ^ (α - 1) ≤ (κs ^ (1 / (α - 1))) ^ (α - 1) :=
      Real.rpow_le_rpow hτ.le (hττ0.trans (min_le_right _ _)) (by linarith)
    rw [← Real.rpow_mul hκs0.le, show 1 / (α - 1) * (α - 1) = 1 by
            have : α - 1 ≠ 0 := by linarith
            field_simp,
      Real.rpow_one] at h1
    exact h1
  have hec : e ≤ c := by
    have : e = c * τ := by rw [hc, he]; field_simp
    rw [this]; nlinarith
  have hc2 : c ≤ 1 / 2 := hcκ.trans (min_le_left _ _)
  have hc3 : c ≤ 1 / (1 + M.vbar) := hcκ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc4 : c ≤ c0 / (A * (1 + W)) := hcκ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc3' : c * (1 + M.vbar) ≤ 1 := by
    rw [le_div_iff₀ (by positivity)] at hc3; linarith
  have hc4' : c * (A * (1 + W)) ≤ c0 := by
    rw [le_div_iff₀ (by positivity)] at hc4; linarith
  have hsmall : A * (e + c * W) ≤ c0 := by nlinarith
  -- grid
  set N := ⌈W / ε⌉₊ with hNdef
  have hWε : 0 < W / ε := div_pos (by positivity) hε
  have hN : 0 < N := Nat.ceil_pos.mpr hWε
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  set h := W / N with hhdef
  have hh : 0 < h := div_pos (by positivity) hNr
  have hNh : (N:ℝ) * h = W := by simp only [hhdef]; field_simp
  have hhε : h ≤ ε := by
    simp only [hhdef]
    rw [div_le_iff₀ hNr]
    have := Nat.le_ceil (W / ε)
    rw [div_le_iff₀ hε] at this
    linarith
  have hWz : ∀ z ∈ Icc 0 M.vbar, wp pstar e c z ≤ (N:ℝ) * h := by
    intro z hz
    rw [hNh]
    unfold wp del
    have : |z - pstar| ≤ M.vbar := by
      rw [abs_le]; constructor <;> linarith [hz.1, hz.2, hpI.1, hpI.2]
    have : c * |z - pstar| ≤ c * M.vbar := mul_le_mul_of_nonneg_left this hc0'.le
    nlinarith [hz.2]
  set S := R M pstar + A * e + M0 * e with hSdef
  have hS0 : 0 ≤ S := by
    have := R_nonneg M hMs pstar hpI.1; positivity
  have hLb : ∀ i : ℕ, i < N → Lb M pstar e c ((i:ℝ) * h) ≤ S := by
    intro i hi
    have hp0 : 0 ≤ (i:ℝ) * h := by positivity
    have hpW' : (i:ℝ) * h ≤ W := by
      rw [← hNh]; apply mul_le_mul_of_nonneg_right _ hh.le; exact_mod_cast hi.le
    have h1 := Lb_le M hMs B hB pstar e c he0 hc0'.le hc2 _ hp0
    have hpW : |(i:ℝ) * h - pstar| ≤ W := by
      rw [abs_le]; constructor <;> linarith [hpI.1, hpI.2]
    have h2 := price_bound M hMs pstar α κL κU ℓ hD A hA0.le c0 hfar W τ hτ hsmall _ hp0 hpW
    simp only [hSdef, hM0]
    have : 2 * M.vbar * B * del pstar e c ((i:ℝ) * h) = A * del pstar e c ((i:ℝ) * h) := by
      simp only [hA]
    rw [this] at h1
    linarith
  have hrev := rev_bound M m ε pstar e c N h hMs hε hm he0 hc0'.le hN hh hWz S hS0 hLb
  have hQ := Q_bound M hMs B hB pstar e c he0 hc0' hpI
  have hlog : (e + c * M.vbar) / e = 1 + M.vbar / τ := by
    rw [hc, he]; field_simp
  rw [hlog] at hQ
  set L := Real.log (1 + M.vbar / τ) with hL
  have hL0 : 0 ≤ L := by
    apply Real.log_nonneg
    have : 0 ≤ M.vbar / τ := by positivity
    linarith
  -- combine
  have hεh : ε + h ≤ 2 * ε := by linarith
  have hQ0 : 0 ≤ ∫ z in (0:ℝ)..M.vbar, M.f z * (z / del pstar e c z + 1) := by
    apply intervalIntegral.integral_nonneg hv.le
    intro z hz
    apply mul_nonneg (hMs.2.1 z)
    have := del_pos pstar e c he0 hc0'.le z
    have : 0 ≤ z / del pstar e c z := div_nonneg hz.1 this.le
    linarith
  have step : (ε + h) * ∫ z in (0:ℝ)..M.vbar, M.f z * (z / del pstar e c z + 1) ≤
      (2 * ε) * (1 + B * M.vbar * (2 * (c⁻¹ * L))) :=
    mul_le_mul hεh hQ hQ0 (by positivity)
  have hεc : 2 * ε * (1 + B * M.vbar * (2 * (c⁻¹ * L))) ≤ e + 4 * B * M.vbar * e * L := by
    have hετ' : ε ≤ e * c := hετ
    have h1 : ε * c⁻¹ ≤ e := by
      have : ε * c⁻¹ ≤ (e * c) * c⁻¹ := mul_le_mul_of_nonneg_right hετ' (inv_nonneg.mpr hc0'.le)
      rwa [mul_assoc, mul_inv_cancel₀ hc0'.ne', mul_one] at this
    have h2 : 2 * ε ≤ e := by
      have := mul_le_mul_of_nonneg_left hc2 he0.le
      linarith
    have h3 : 0 ≤ B * M.vbar * L := by positivity
    have : 2 * ε * (1 + B * M.vbar * (2 * (c⁻¹ * L))) =
        2 * ε + 4 * (B * M.vbar * L) * (ε * c⁻¹) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 4 * (B * M.vbar * L))
    linarith
  have hK1 : A + M0 + 1 ≤ K := le_max_left _ _
  have hK2 : 4 * B * M.vbar ≤ K := le_max_right _ _
  have : e * (A + M0 + 1) + e * (4 * B * M.vbar * L) ≤ e * (K + K * L) := by
    have h5 := mul_le_mul_of_nonneg_right hK2 hL0
    have h6 : e * (A + M0 + 1) ≤ e * K := mul_le_mul_of_nonneg_left hK1 he0.le
    have h7 : e * (4 * B * M.vbar * L) ≤ e * (K * L) := mul_le_mul_of_nonneg_left h5 he0.le
    linarith
  calc revenue M m ≤ S + (ε + h) * ∫ z in (0:ℝ)..M.vbar, M.f z * (z / del pstar e c z + 1) := hrev
    _ ≤ S + (2 * ε) * (1 + B * M.vbar * (2 * (c⁻¹ * L))) := by linarith [step]
    _ ≤ S + (e + 4 * B * M.vbar * e * L) := by linarith [hεc]
    _ = R M pstar + (e * (A + M0 + 1) + e * (4 * B * M.vbar * L)) := by
      simp only [hSdef]; ring
    _ ≤ R M pstar + e * (K + K * L) := by linarith [this]

end AIC1T1

-- ===== part F =====

open MeasureTheory Set ApproxIC.UpperBound

theorem solution (M : Model) (hM : M.Assumption1) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ)
    (hinf : ∃ η > 0, ∀ p ∈ Set.Icc 0 M.vbar \ Set.Ioo (pstar - ℓ) (pstar + ℓ), η ≤ |Rdot M p|) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0, ∀ m ∈ Mset M ε,
      revenue M m - optRev M 0 ≤ C * ε ^ (α / (2 * α - 1)) * Real.log (1 / ε) := by
  obtain ⟨K, hK, τ0, hτ0, hcore⟩ := AIC1T1.core M hM pstar α κL κU ℓ hD
  have hα : 1 < α := hD.2.2.2.1
  have hv := hM.1.1
  set q := 2 * α - 1 with hq
  have hq0 : 0 < q := by linarith
  set τ1 := min 1 τ0 with hτ1
  have hτ10 : 0 < τ1 := lt_min one_pos hτ0
  set ε0 := min (Real.exp (-1)) (τ1 ^ q) with hε0
  have hε00 : 0 < ε0 := lt_min (Real.exp_pos _) (Real.rpow_pos_of_pos hτ10 _)
  have hlv : 0 ≤ Real.log (1 + M.vbar) := Real.log_nonneg (by linarith)
  refine ⟨K + K * Real.log (1 + M.vbar) + K * (1 / q), by positivity, ε0, hε00, ?_⟩
  rintro ε ⟨hε, hεε0⟩ m hm
  set τ := ε ^ (1 / q) with hτdef
  have hτ : 0 < τ := Real.rpow_pos_of_pos hε _
  have hτle : τ ≤ τ1 := by
    have h1 : ε ≤ τ1 ^ q := hεε0.trans (min_le_right _ _)
    have h2 : ε ^ (1 / q) ≤ (τ1 ^ q) ^ (1 / q) :=
      Real.rpow_le_rpow hε.le h1 (by positivity)
    rw [← Real.rpow_mul hτ10.le, show q * (1 / q) = 1 by field_simp, Real.rpow_one] at h2
    exact h2
  have hτ1' : τ ≤ 1 := hτle.trans (min_le_left _ _)
  have hτεq : τ ^ q = ε := by
    rw [hτdef, ← Real.rpow_mul hε.le, show 1 / q * q = 1 by field_simp, Real.rpow_one]
  have hετ : ε ≤ τ ^ α * (τ ^ α / τ) := by
    rw [← Real.rpow_sub_one hτ.ne', ← Real.rpow_add hτ]
    have : α + (α - 1) = q := by rw [hq]; ring
    rw [this, hτεq]
  have hrev := hcore τ hτ (hτle.trans (min_le_right _ _)) ε hε hετ m hm
  have hopt := AIC1T1.opt_ge M hM.1 pstar ⟨hD.1.1.le, hD.1.2.le⟩
  have hτα : τ ^ α = ε ^ (α / q) := by
    rw [hτdef, ← Real.rpow_mul hε.le]; congr 1; ring
  set l1 := Real.log (1 / ε) with hl1
  have hl1' : l1 = -Real.log ε := by rw [hl1, one_div, Real.log_inv]
  have hl1ge : 1 ≤ l1 := by
    have h1 : Real.log ε ≤ -1 := by
      have := Real.log_le_log hε (hεε0.trans (min_le_left _ _))
      rwa [Real.log_exp] at this
    rw [hl1']; linarith
  have hL : Real.log (1 + M.vbar / τ) ≤ Real.log (1 + M.vbar) + (1 / q) * l1 := by
    have h1 : 1 + M.vbar / τ ≤ (1 + M.vbar) / τ := by
      rw [add_div]
      have : 1 ≤ 1 / τ := by rw [le_div_iff₀ hτ]; linarith
      linarith
    have h2 : Real.log (1 + M.vbar / τ) ≤ Real.log ((1 + M.vbar) / τ) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_div (by linarith) hτ.ne', hτdef, Real.log_rpow hε] at h2
    rw [hl1']
    linarith
  have hγ0 : 0 ≤ ε ^ (α / q) := Real.rpow_nonneg hε.le _
  have hbig : K + K * Real.log (1 + M.vbar / τ) ≤
      (K + K * Real.log (1 + M.vbar) + K * (1 / q)) * l1 := by
    have h1 : K * Real.log (1 + M.vbar / τ) ≤ K * (Real.log (1 + M.vbar) + (1 / q) * l1) :=
      mul_le_mul_of_nonneg_left hL hK.le
    have h2 : K + K * Real.log (1 + M.vbar) ≤ (K + K * Real.log (1 + M.vbar)) * l1 := by
      have : 0 ≤ K + K * Real.log (1 + M.vbar) := by positivity
      nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_left hbig hγ0
  rw [hτα] at hrev
  calc revenue M m - optRev M 0 ≤ revenue M m - R M pstar := by linarith
    _ ≤ ε ^ (α / q) * (K + K * Real.log (1 + M.vbar / τ)) := by linarith
    _ ≤ ε ^ (α / q) * ((K + K * Real.log (1 + M.vbar) + K * (1 / q)) * l1) := this
    _ = (K + K * Real.log (1 + M.vbar) + K * (1 / q)) * ε ^ (α / q) * l1 := by ring
