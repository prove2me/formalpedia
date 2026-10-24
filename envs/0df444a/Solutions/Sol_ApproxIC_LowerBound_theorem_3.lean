-- Prove2me | solution 1 for ApproxIC.LowerBound.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T07:56:55.586355+00:00
-- url     : https://prove2.me/submissions/8d6016b7-92a8-4974-997f-ab9bf3158616

import Mathlib
import Definitions.Def_ApproxIC_UpperBound_Setting
import Definitions.Def_ApproxIC_LowerBound_Setting

set_option autoImplicit false

open MeasureTheory Set

namespace P1ae1

open ApproxIC.UpperBound

lemma fub (f x q : ℝ → ℝ) (vb B : ℝ) (hf : IntegrableOn f (Ioc 0 vb)) (hx : Measurable x)
    (hq : Measurable q) (hqB : ∀ θ, |q θ| ≤ B) :
    IntegrableOn (fun v => (∫ θ in Ioc (0:ℝ) 1, if θ ≤ x v then q θ else 0) * f v) (Ioc 0 vb) ∧
    IntegrableOn (fun θ => q θ * ∫ v in Ioc 0 vb, (if θ ≤ x v then f v else 0)) (Ioc (0:ℝ) 1) ∧
    ∫ v in Ioc 0 vb, (∫ θ in Ioc (0:ℝ) 1, if θ ≤ x v then q θ else 0) * f v
      = ∫ θ in Ioc (0:ℝ) 1, q θ * ∫ v in Ioc 0 vb, (if θ ≤ x v then f v else 0) := by
  set μ := volume.restrict (Ioc (0:ℝ) vb) with hμ
  set ν := volume.restrict (Ioc (0:ℝ) 1) with hν
  have : IsFiniteMeasure ν := by
    rw [hν]; exact isFiniteMeasure_restrict.2 (by simp)
  let G : ℝ × ℝ → ℝ := fun z => if z.2 ≤ x z.1 then q z.2 else 0
  have hGm : Measurable G :=
    Measurable.ite (measurableSet_le measurable_snd (hx.comp measurable_fst))
      (hq.comp measurable_snd) measurable_const
  have hI : Integrable (fun z : ℝ × ℝ => f z.1 * (1:ℝ)) (μ.prod ν) :=
    Integrable.mul_prod (μ := μ) (ν := ν) hf (integrable_const (1:ℝ))
  have hB0 : 0 ≤ B := (abs_nonneg (q 0)).trans (hqB 0)
  have hH : Integrable (fun z : ℝ × ℝ => G z * (f z.1 * 1)) (μ.prod ν) := by
    refine hI.bdd_mul hGm.aestronglyMeasurable (c := B) (Filter.Eventually.of_forall ?_)
    intro z
    simp only [G, Real.norm_eq_abs]
    split_ifs
    · exact hqB _
    · simpa using hB0
  have hsw := integral_integral_swap (f := fun v θ => G (v, θ) * (f v * 1)) hH
  have h1 : ∀ v, (∫ θ, G (v, θ) * (f v * 1) ∂ν)
      = (∫ θ in Ioc (0:ℝ) 1, if θ ≤ x v then q θ else 0) * f v := by
    intro v
    simp only [mul_one]
    rw [integral_mul_const]
  have h2 : ∀ θ, (∫ v, G (v, θ) * (f v * 1) ∂μ)
      = q θ * ∫ v in Ioc 0 vb, (if θ ≤ x v then f v else 0) := by
    intro θ
    rw [← integral_const_mul]
    congr 1; ext v
    simp only [G, mul_one]
    split_ifs <;> ring
  refine ⟨?_, ?_, ?_⟩
  · have := hH.integral_prod_left
    simp only [h1] at this
    exact this
  · have := hH.integral_prod_right
    simp only [h2] at this
    exact this
  · simp only [h1, h2] at hsw
    exact hsw

/-- the threshold price at level `θ` of an allocation `x` -/
noncomputable def qf (vb : ℝ) (x : ℝ → ℝ) (θ : ℝ) : ℝ :=
  sInf (insert vb {s | s ∈ Icc 0 vb ∧ θ ≤ x s})

lemma qf_bdd (vb : ℝ) (x : ℝ → ℝ) (θ : ℝ) (hvb : 0 ≤ vb) :
    BddBelow (insert vb {s | s ∈ Icc 0 vb ∧ θ ≤ x s}) :=
  ⟨0, by rintro s (rfl | ⟨⟨h0, _⟩, _⟩) <;> assumption⟩

lemma qf_mem (vb : ℝ) (x : ℝ → ℝ) (θ : ℝ) (hvb : 0 ≤ vb) : qf vb x θ ∈ Icc 0 vb :=
  ⟨le_csInf (insert_nonempty _ _) (by rintro s (rfl | ⟨⟨h0, _⟩, _⟩) <;> assumption),
    csInf_le (qf_bdd vb x θ hvb) (mem_insert _ _)⟩

lemma qf_mono (vb : ℝ) (x : ℝ → ℝ) (hvb : 0 ≤ vb) : Monotone (qf vb x) := fun θ θ' h =>
  csInf_le_csInf (qf_bdd vb x θ hvb) (insert_nonempty _ _)
    (insert_subset_insert (fun s ⟨hs, hθ⟩ => ⟨hs, h.trans hθ⟩))

lemma qf_le (vb : ℝ) (x : ℝ → ℝ) (θ : ℝ) (hvb : 0 ≤ vb) {s : ℝ} (hs : s ∈ Icc 0 vb)
    (hθ : θ ≤ x s) : qf vb x θ ≤ s :=
  csInf_le (qf_bdd vb x θ hvb) (mem_insert_of_mem _ ⟨hs, hθ⟩)

lemma qf_ge (vb : ℝ) (x : ℝ → ℝ) (θ : ℝ) {s0 : ℝ} (hs0 : s0 ≤ vb)
    (h : ∀ s ∈ Icc 0 vb, θ ≤ x s → s0 < s) : s0 ≤ qf vb x θ :=
  le_csInf (insert_nonempty _ _) (by
    rintro s (rfl | ⟨hs, hθ⟩)
    exacts [hs0, (h s hs hθ).le])

lemma int_ite (q : ℝ → ℝ) (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) :
    ∫ θ in (0:ℝ)..r, q θ = ∫ θ in Ioc (0:ℝ) 1, if θ ≤ r then q θ else 0 := by
  have : (fun θ => if θ ≤ r then q θ else 0) = (Iic r).indicator q := by
    ext θ; simp [Set.indicator, Set.mem_Iic]
  rw [this, setIntegral_indicator measurableSet_Iic, Set.Ioc_inter_Iic,
    min_eq_right hr.2, intervalIntegral.integral_of_le hr.1]

theorem myerson_pointwise (M : Model) (m : Mech) (hm : m ∈ Mset M 0) (hvb : 0 < M.vbar) :
    ∀ v ∈ Icc 0 M.vbar, m.t v ≤ ∫ θ in (0:ℝ)..(m.x v), qf M.vbar m.x θ := by
  obtain ⟨⟨_, _, hx01⟩, hIR, hIC⟩ := hm
  set vb := M.vbar with hvbdef
  have hmono : ∀ w ∈ Icc 0 vb, ∀ v ∈ Icc 0 vb, w ≤ v → m.x w ≤ m.x v := by
    intro w hw v hv hwv
    rcases eq_or_lt_of_le hwv with rfl | hlt
    · exact le_rfl
    by_contra hc
    push Not at hc
    have h1 := hIC v hv w hw
    have h2 := hIC w hw v hv
    nlinarith [mul_pos (sub_pos.2 hlt) (sub_pos.2 hc)]
  have hstep : ∀ w ∈ Icc 0 vb, ∀ v ∈ Icc 0 vb, m.t v ≤ m.t w + v * (m.x v - m.x w) := by
    intro w hw v hv
    have := hIC v hv w hw
    linarith
  have ht0 : m.t 0 ≤ 0 := by
    have := hIR 0 ⟨le_rfl, hvb.le⟩
    simp at this; linarith
  have hqint : ∀ a b, IntervalIntegrable (qf vb m.x) volume a b :=
    fun a b => (qf_mono vb m.x hvb.le).intervalIntegrable
  intro v hv
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨n, hn⟩ := exists_nat_gt (vb / η)
  have hnpos : (0:ℝ) < n := lt_of_le_of_lt (div_nonneg hvb.le hη.le) hn
  set δ := v / n with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hv.1 hnpos.le
  have hnδ : (n:ℝ) * δ = v := by rw [hδ]; field_simp
  let s : ℕ → ℝ := fun k => (k:ℝ) * δ
  have hsS : ∀ k, k ≤ n → s k ∈ Icc 0 vb := by
    intro k hk
    refine ⟨mul_nonneg (Nat.cast_nonneg _) hδ0, ?_⟩
    have : (k:ℝ) * δ ≤ n * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hδ0
    simp only [s]; linarith [hv.2]
  have claim : ∀ k, k ≤ n → m.t (s k) ≤ m.t 0 + (∫ θ in (m.x 0)..(m.x (s k)), qf vb m.x θ)
      + δ * (m.x (s k) - m.x 0) := by
    intro k
    induction k with
    | zero => intro _; simp [s]
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hsk := hsS k hk'
      have hsk1 := hsS (k+1) hk
      have hss : s (k+1) = s k + δ := by simp only [s]; push_cast; ring
      have e1 := hstep (s k) hsk (s (k+1)) hsk1
      have hxle : m.x (s k) ≤ m.x (s (k+1)) :=
        hmono (s k) hsk (s (k+1)) hsk1 (by rw [hss]; linarith)
      have hint : s k * (m.x (s (k+1)) - m.x (s k))
          ≤ ∫ θ in (m.x (s k))..(m.x (s (k+1))), qf vb m.x θ := by
        rw [intervalIntegral.integral_of_le hxle]
        have := setIntegral_ge_of_const_le_real (μ := volume) (c := s k) measurableSet_Ioc
          (by simp) (fun θ hθ => qf_ge vb m.x θ hsk.2 (fun s' hs' hθs' => by
            by_contra hc
            push Not at hc
            have := hmono s' hs' (s k) hsk hc
            linarith [hθ.1]))
          (hqint (m.x (s k)) (m.x (s (k+1)))).1
        rw [Real.volume_real_Ioc_of_le hxle] at this
        linarith
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        (hqint (m.x 0) (m.x (s k))) (hqint (m.x (s k)) (m.x (s (k+1))))
      have ih' := ih hk'
      rw [← hsplit]
      have : s (k+1) * (m.x (s (k+1)) - m.x (s k))
          = s k * (m.x (s (k+1)) - m.x (s k)) + δ * (m.x (s (k+1)) - m.x (s k)) := by
        rw [hss]; ring
      linarith
  have hfin := claim n le_rfl
  have hsn : s n = v := by simp only [s]; exact hnδ
  rw [hsn] at hfin
  have hx0 := hx01 0 ⟨le_rfl, hvb.le⟩
  have hxv := hx01 v hv
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hqint 0 (m.x 0)) (hqint (m.x 0) (m.x v))
  have hnn : 0 ≤ ∫ θ in (0:ℝ)..(m.x 0), qf vb m.x θ :=
    intervalIntegral.integral_nonneg hx0.1 (fun θ _ => (qf_mem vb m.x θ hvb.le).1)
  have hδη : δ ≤ η := by
    rw [hδ, div_le_iff₀ hnpos]
    rw [div_lt_iff₀ hη] at hn
    nlinarith [hv.2]
  have : δ * (m.x v - m.x 0) ≤ η := by
    have : m.x v - m.x 0 ≤ 1 := by linarith [hxv.2, hx0.1]
    nlinarith
  linarith

lemma f_int (M : Model) (hS : M.Standing) : Integrable M.f := by
  have hfeq : M.f = (Icc 0 M.vbar).indicator M.f := by
    ext v
    by_cases hv : v ∈ Icc 0 M.vbar
    · simp [hv]
    · simp [hv, hS.2.2.1 v hv]
  rw [hfeq]
  exact (integrable_indicator_iff measurableSet_Icc).2 hS.2.2.2.1

lemma f_ii (M : Model) (hS : M.Standing) (a b : ℝ) : IntervalIntegrable M.f volume a b :=
  (f_int M hS).intervalIntegrable

lemma cdfBar_eq (M : Model) (hS : M.Standing) (q : ℝ) :
    cdfBar M q = ∫ v in q..M.vbar, M.f v := by
  unfold cdfBar cdf
  rw [← hS.2.2.2.2, ← intervalIntegral.integral_add_adjacent_intervals (f_ii M hS 0 q)
    (f_ii M hS q M.vbar)]
  ring

lemma cdf_cont (M : Model) (hS : M.Standing) : Continuous (cdf M) :=
  intervalIntegral.continuous_primitive (fun a b => f_ii M hS a b) 0

theorem myerson (M : Model) (hS : M.Standing) (pstar : ℝ)
    (hmax : IsMaxOn (R M) (Icc 0 M.vbar) pstar) (m : Mech) (hm : m ∈ Mset M 0) :
    revenue M m ≤ R M pstar := by
  have hvb := hS.1
  set vb := M.vbar with hvbdef
  have hf0 : ∀ v, 0 ≤ M.f v := hS.2.1
  have hR0 : 0 ≤ R M pstar := by
    have := isMaxOn_iff.1 hmax 0 ⟨le_rfl, hvb.le⟩
    simpa [R] using this
  have hxm := hm.1.1
  have hx01 := hm.1.2.2
  have hfS : IntegrableOn M.f (Ioc 0 vb) := hS.2.2.2.1.mono_set Ioc_subset_Icc_self
  set q := qf vb m.x with hqdef
  have hqm : Measurable q := (qf_mono vb m.x hvb.le).measurable
  have hqB : ∀ θ, |q θ| ≤ vb := fun θ => by
    have := qf_mem vb m.x θ hvb.le
    rw [abs_of_nonneg this.1]; exact this.2
  obtain ⟨hI1, hI2, hEq⟩ := fub M.f m.x q vb vb hfS hxm hqm hqB
  have hpt : ∀ v ∈ Icc 0 vb, m.t v ≤ ∫ θ in Ioc (0:ℝ) 1, if θ ≤ m.x v then q θ else 0 := by
    intro v hv
    rw [← int_ite q (m.x v) (hx01 v hv)]
    exact myerson_pointwise M m hm hvb v hv
  by_cases hint : IntervalIntegrable (fun v => m.t v * M.f v) volume 0 vb
  · have hI1' : IntervalIntegrable
        (fun v => (∫ θ in Ioc (0:ℝ) 1, if θ ≤ m.x v then q θ else 0) * M.f v) volume 0 vb :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hvb.le).2 hI1
    calc revenue M m = ∫ v in (0:ℝ)..vb, m.t v * M.f v := rfl
      _ ≤ ∫ v in (0:ℝ)..vb, (∫ θ in Ioc (0:ℝ) 1, if θ ≤ m.x v then q θ else 0) * M.f v :=
          intervalIntegral.integral_mono_on hvb.le hint hI1'
            (fun v hv => mul_le_mul_of_nonneg_right (hpt v hv) (hf0 v))
      _ = ∫ θ in Ioc (0:ℝ) 1, q θ * ∫ v in Ioc 0 vb, (if θ ≤ m.x v then M.f v else 0) := by
          rw [intervalIntegral.integral_of_le hvb.le]; exact hEq
      _ ≤ ∫ θ in Ioc (0:ℝ) 1, R M pstar := by
          refine setIntegral_mono_on hI2 (integrableOn_const (by simp)) measurableSet_Ioc ?_
          intro θ _
          have hqθ := qf_mem vb m.x θ hvb.le
          have hind : (fun v => if θ ≤ m.x v then M.f v else 0)
              = {v | θ ≤ m.x v}.indicator M.f := by
            ext v; simp [Set.indicator]
          have hin : ∫ v in Ioc 0 vb, (if θ ≤ m.x v then M.f v else 0) ≤ cdfBar M (q θ) := by
            rw [hind, setIntegral_indicator (measurableSet_le measurable_const hxm),
              cdfBar_eq M hS, intervalIntegral.integral_of_le hqθ.2, ← integral_Icc_eq_integral_Ioc]
            refine setIntegral_mono_set (hS.2.2.2.1.mono_set (Icc_subset_Icc hqθ.1 le_rfl))
              (Filter.Eventually.of_forall hf0) (LE.le.eventuallyLE ?_)
            rintro v ⟨hv, hθv⟩
            exact ⟨qf_le vb m.x θ hvb.le ⟨hv.1.le, hv.2⟩ hθv, hv.2⟩
          calc q θ * ∫ v in Ioc 0 vb, (if θ ≤ m.x v then M.f v else 0)
              ≤ q θ * cdfBar M (q θ) := mul_le_mul_of_nonneg_left hin hqθ.1
            _ = R M (q θ) := rfl
            _ ≤ R M pstar := isMaxOn_iff.1 hmax _ hqθ
      _ = R M pstar := by simp
  · rw [revenue, intervalIntegral.integral_undef hint]; exact hR0

theorem optRev0_le (M : Model) (hS : M.Standing) (pstar : ℝ)
    (hmax : IsMaxOn (R M) (Icc 0 M.vbar) pstar) : optRev M 0 ≤ R M pstar := by
  apply csSup_le
  · exact ⟨_, ⟨⟨fun _ => 0, fun _ => 0⟩, ⟨⟨measurable_const, measurable_const,
      fun v _ => by simp⟩, fun v _ => by simp, fun v _ w _ => by simp⟩, rfl⟩⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact myerson M hS pstar hmax m hm

lemma R_ftc (M : Model) (hS : M.Standing) (a b : ℝ) (hab : a ≤ b) :
    R M b - R M a = ∫ v in a..b, Rdot M v := by
  have hfi := f_ii M hS
  set A := min 0 a with hA
  set B := max 0 b with hB
  have h0 : (0:ℝ) ∈ uIcc A B := Set.mem_uIcc.2 (Or.inl ⟨min_le_left _ _, le_max_left _ _⟩)
  have hsub : uIcc a b ⊆ uIcc A B := by
    apply uIcc_subset_uIcc
    · exact Set.mem_uIcc.2 (Or.inl ⟨min_le_right _ _, hab.trans (le_max_right _ _)⟩)
    · exact Set.mem_uIcc.2 (Or.inl ⟨(min_le_right _ _).trans hab, le_max_right _ _⟩)
  have hACF : AbsolutelyContinuousOnInterval (cdf M) a b :=
    ((hfi A B).absolutelyContinuousOnInterval_intervalIntegral h0).mono hsub
  have hACR : AbsolutelyContinuousOnInterval (R M) a b := by
    have h1 : AbsolutelyContinuousOnInterval (fun x : ℝ => x) a b :=
      (LipschitzWith.id.lipschitzOnWith).absolutelyContinuousOnInterval
    have h2 : AbsolutelyContinuousOnInterval (fun x => 1 - cdf M x) a b :=
      ((LipschitzWith.const (1:ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval).sub hACF
    have := h1.mul h2
    convert this using 1
    funext y
    simp [R, cdfBar]
  have hderiv := (hfi A B).ae_hasDerivAt_integral
  rw [← hACR.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hderiv] with x hx hxab
  have hxAB : x ∈ uIcc A B := hsub (uIoc_subset_uIcc hxab)
  have hF : HasDerivAt (cdf M) (M.f x) x := hx hxAB 0 h0
  have hR : HasDerivAt (R M) (Rdot M x) x := by
    have := (hasDerivAt_id x).mul ((hasDerivAt_const x (1:ℝ)).sub hF)
    have e1 : R M = fun y => id y * (1 - cdf M y) := by funext y; simp [R, cdfBar]
    rw [e1]
    refine this.congr_deriv ?_
    unfold Rdot cdfBar
    simp only [id_eq, Pi.sub_apply]
    ring
  exact hR.deriv

lemma R_lower (M : Model) (hS : M.Standing) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) (p : ℝ) (hp1 : pstar ≤ p) (hp2 : p < pstar + ℓ) :
    R M pstar - κU * (p - pstar) ^ α ≤ R M p := by
  obtain ⟨_, _, _, hα, _, _, _, _, henv⟩ := hD
  have hftc := R_ftc M hS pstar p hp1
  have hcont : Continuous (fun v : ℝ => (v - pstar) ^ (α - 1)) :=
    (continuous_id.sub continuous_const).rpow_const (fun _ => Or.inr (by linarith))
  have hRdi : IntervalIntegrable (Rdot M) volume pstar p := by
    have h1 : IntervalIntegrable (cdfBar M) volume pstar p :=
      (continuous_const.sub (cdf_cont M hS)).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun v => v * M.f v) volume pstar p :=
      (f_ii M hS pstar p).continuousOn_mul continuousOn_id
    exact h1.sub h2
  have hlow : ∫ v in pstar..p, -(κU * α * (v - pstar) ^ (α - 1)) ≤ ∫ v in pstar..p, Rdot M v := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hp1
      ((hcont.intervalIntegrable _ _).const_mul _).neg hRdi ?_
    intro v hv
    have hvN : v ∈ Ioo (pstar - ℓ) (pstar + ℓ) := ⟨by linarith [hv.1], by linarith [hv.2]⟩
    have hU := (henv v hvN).2
    have hd : 0 < v - pstar := by linarith [hv.1]
    rw [abs_of_pos hd] at hU
    have hpow : (v - pstar) ^ α = (v - pstar) ^ (α - 1) * (v - pstar) := by
      rw [Real.rpow_sub_one hd.ne']; field_simp
    rw [hpow] at hU
    have hE : 0 ≤ (v - pstar) ^ (α - 1) := Real.rpow_nonneg hd.le _
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc hd]
  have hcalc : ∫ v in pstar..p, -(κU * α * (v - pstar) ^ (α - 1)) = -(κU * (p - pstar) ^ α) := by
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun v => v ^ (α - 1)),
      integral_rpow (Or.inl (by linarith))]
    have hα0 : α ≠ 0 := by linarith
    simp only [sub_self, sub_add_cancel]
    rw [Real.zero_rpow hα0, sub_zero]
    field_simp
  linarith

lemma Rdot_nonpos (M : Model) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) (v : ℝ) (hv1 : pstar < v) (hv2 : v < pstar + ℓ) :
    cdfBar M v ≤ v * M.f v := by
  obtain ⟨_, _, _, hα, hκL, _, _, _, henv⟩ := hD
  have hvN : v ∈ Ioo (pstar - ℓ) (pstar + ℓ) := ⟨by linarith, hv2⟩
  have hL := (henv v hvN).1
  have h0 : 0 ≤ κL * α * |v - pstar| ^ α :=
    mul_nonneg (mul_nonneg hκL.le (by linarith)) (Real.rpow_nonneg (abs_nonneg _) _)
  have : Rdot M v ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos (sub_pos.2 hv1) hc]
  unfold Rdot at this
  linarith

lemma alg0 (y r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    r * y - r ^ 2 / 2 ≤ (min (max y 0) 1) * y - (min (max y 0) 1) ^ 2 / 2 := by
  rcases le_total y 0 with hy | hy
  · rw [max_eq_right hy, min_eq_left zero_le_one]; nlinarith
  rcases le_total y 1 with hy1 | hy1
  · rw [max_eq_left hy, min_eq_left hy1]; nlinarith [sq_nonneg (y - r)]
  · rw [max_eq_left hy, min_eq_right hy1]; nlinarith [mul_nonneg (sub_nonneg.2 hr1) (sub_nonneg.2 hy1)]

lemma alg1 (h c ε y r : ℝ) (hh : 0 < h) (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (hce : c ^ 2 * h ≤ 2 * ε)
    (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2) :
    h * c * (y - r) - ε ≤
      h * ((min (max y 0) 1) * y - (min (max y 0) 1) ^ 2 / 2 - (r * y - r ^ 2 / 2)) := by
  have hε : 0 ≤ ε := by nlinarith [sq_nonneg c]
  rcases le_total y r with hyr | hyr
  · have := alg0 y r hr0 (by linarith)
    nlinarith [mul_nonneg hh.le (sub_nonneg.2 this), mul_nonneg (mul_nonneg hh.le hc0) (sub_nonneg.2 hyr)]
  have hy : 0 ≤ y := hr0.trans hyr
  rcases le_total y 1 with hy1 | hy1
  · rw [max_eq_left hy, min_eq_left hy1]
    nlinarith [mul_nonneg hh.le (sq_nonneg (y - r - c))]
  · rw [max_eq_left hy, min_eq_right hy1]
    nlinarith [mul_nonneg hh.le (sq_nonneg (1 - r - c)),
      mul_nonneg (mul_nonneg hh.le (show 0 ≤ 1 - r - c by linarith)) (sub_nonneg.2 hy1)]

set_option maxHeartbeats 1000000 in
lemma mech_bound (M : Model) (hS : M.Standing) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) (h c ε : ℝ) (hh : 0 < h) (hhl : h < ℓ)
    (hc0 : 0 ≤ c) (hc : c ≤ 1 / 2) (hce : c ^ 2 * h ≤ 2 * ε)
    (hκh : κU * h ^ α ≤ R M pstar / 2) :
    ∃ m ∈ Mset M ε,
      R M pstar - κU * h ^ α + c * h * (R M pstar / (4 * M.vbar)) ≤ revenue M m := by
  have hD' := hD
  obtain ⟨hps, hmax, _, hα, _, hκU, hℓ, hsub, _⟩ := hD'
  have hvb := hS.1
  have hf0 : ∀ v, 0 ≤ M.f v := hS.2.1
  have hε : 0 ≤ ε := by nlinarith [sq_nonneg c]
  have hph : pstar + h < M.vbar := (hsub ⟨by linarith, by linarith⟩).2
  have hp0 : 0 < pstar := hps.1
  have hRs0 : 0 ≤ R M pstar := by
    have := isMaxOn_iff.1 hmax 0 ⟨le_rfl, hvb.le⟩
    simpa [R] using this
  set p2 := pstar + h / 2 with hp2
  let r : ℝ → ℝ := fun v => min (max ((v - pstar) / h) 0) 1
  have hr_def : ∀ v, r v = min (max ((v - pstar) / h) 0) 1 := fun v => rfl
  let e : ℝ → ℝ := fun v => if v ∈ Ioc pstar p2 then c else 0
  let T0 : ℝ → ℝ := fun v => pstar * r v + h * r v ^ 2 / 2
  let m : Mech := ⟨fun v => r v + e v, fun v => T0 v + v * e v⟩
  have hrc : Continuous r := by
    simp only [r]; fun_prop
  have hem : Measurable e := Measurable.ite measurableSet_Ioc measurable_const measurable_const
  have hr01 : ∀ v, 0 ≤ r v ∧ r v ≤ 1 := fun v =>
    ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
  have hre : ∀ v, v ∈ Ioc pstar p2 →
      r v = (v - pstar) / h ∧ (v - pstar) / h ≤ 1 / 2 ∧ 0 ≤ (v - pstar) / h := by
    intro v hv
    have h1 : 0 ≤ (v - pstar) / h := div_nonneg (by linarith [hv.1]) hh.le
    have h2 : (v - pstar) / h ≤ 1 / 2 := by
      rw [div_le_iff₀ hh]; linarith [hv.2]
    refine ⟨?_, h2, h1⟩
    rw [hr_def, max_eq_left h1, min_eq_left (by linarith)]
  have hU : ∀ v, v * m.x v - m.t v = h * (r v * ((v - pstar) / h) - r v ^ 2 / 2) := by
    intro v
    simp only [m, T0]
    have : v - pstar = h * ((v - pstar) / h) := by field_simp
    linear_combination (r v) * this
  have hdev : ∀ v w, v * m.x w - m.t w
      = h * (r w * ((v - pstar) / h) - r w ^ 2 / 2) + (v - w) * e w := by
    intro v w
    simp only [m, T0]
    have : v - pstar = h * ((v - pstar) / h) := by field_simp
    linear_combination (r w) * this
  have hmem : m ∈ Mset M ε := by
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · exact hrc.measurable.add hem
    · have hrm := hrc.measurable
      exact ((hrm.const_mul pstar).add ((hrm.pow_const 2).const_mul h |>.div_const 2)).add
        (measurable_id.mul hem)
    · intro v _
      show r v + e v ∈ Icc (0:ℝ) 1
      by_cases hv : v ∈ Ioc pstar p2
      · obtain ⟨h1, h2, h3⟩ := hre v hv
        have : e v = c := if_pos hv
        rw [this, h1]; constructor <;> linarith
      · have : e v = 0 := if_neg hv
        rw [this, add_zero]; exact hr01 v
    · intro v _
      rw [hU]
      have h0 := alg0 ((v - pstar) / h) 0 le_rfl zero_le_one
      rw [← hr_def] at h0
      have : 0 ≤ r v * ((v - pstar) / h) - r v ^ 2 / 2 := by linarith
      exact mul_nonneg hh.le this
    · intro v _ w _
      rw [hU, hdev]
      by_cases hw : w ∈ Ioc pstar p2
      · obtain ⟨h1, h2, h3⟩ := hre w hw
        have hew : e w = c := if_pos hw
        have hvw : v - w = h * ((v - pstar) / h - (w - pstar) / h) := by field_simp; ring
        rw [hew, hvw, h1, hr_def v]
        have := alg1 h c ε ((v - pstar) / h) ((w - pstar) / h) hh hc0 hc hce h3 h2
        linear_combination this
      · have hew : e w = 0 := if_neg hw
        rw [hew, mul_zero, add_zero]
        have := alg0 ((v - pstar) / h) (r w) (hr01 w).1 (hr01 w).2
        rw [← hr_def] at this
        have := mul_le_mul_of_nonneg_left this hh.le
        linarith
  refine ⟨m, hmem, ?_⟩
  -- the integrand
  have hfS : IntegrableOn M.f (Ioc 0 M.vbar) := hS.2.2.2.1.mono_set Ioc_subset_Icc_self
  have hT0c : Continuous T0 := by simp only [T0]; fun_prop
  have hTint : IntegrableOn (fun v => T0 v * M.f v) (Ioc 0 M.vbar) :=
    ((f_ii M hS 0 M.vbar).continuousOn_mul hT0c.continuousOn).1
  have hgint : IntegrableOn (fun v => v * M.f v) (Ioc 0 M.vbar) :=
    ((f_ii M hS 0 M.vbar).continuousOn_mul continuousOn_id).1
  have hsplit : (fun v => m.t v * M.f v)
      = fun v => T0 v * M.f v + c * (Ioc pstar p2).indicator (fun v => v * M.f v) v := by
    funext v
    show (T0 v + v * e v) * M.f v = _
    by_cases hv : v ∈ Ioc pstar p2
    · have : e v = c := if_pos hv
      rw [this]; simp only [Set.indicator, hv, if_true]; ring
    · have : e v = 0 := if_neg hv
      rw [this]; simp only [Set.indicator, hv, if_false]; ring
  have hrev : revenue M m = (∫ v in Ioc 0 M.vbar, T0 v * M.f v)
      + c * ∫ v in Ioc 0 M.vbar, (Ioc pstar p2).indicator (fun v => v * M.f v) v := by
    rw [revenue, intervalIntegral.integral_of_le hvb.le, hsplit,
      integral_add hTint ((hgint.indicator measurableSet_Ioc).const_mul c), integral_const_mul]
  -- gain part
  have hgain : h / 2 * (R M pstar / (2 * M.vbar))
      ≤ ∫ v in Ioc 0 M.vbar, (Ioc pstar p2).indicator (fun v => v * M.f v) v := by
    rw [setIntegral_indicator measurableSet_Ioc, Set.Ioc_inter_Ioc, max_eq_right hp0.le,
      min_eq_right (by linarith), ← intervalIntegral.integral_of_le (by linarith)]
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith : pstar ≤ p2)
      (intervalIntegrable_const (c := R M pstar / (2 * M.vbar)))
      ((f_ii M hS pstar p2).continuousOn_mul continuousOn_id) (fun v hv => by
        have hv0 : 0 < v := by linarith [hv.1]
        have hvle : v ≤ M.vbar := by linarith [hv.2]
        have h1 := Rdot_nonpos M pstar α κL κU ℓ hD v hv.1 (by linarith [hv.2])
        have h2 := R_lower M hS pstar α κL κU ℓ hD v hv.1.le (by linarith [hv.2])
        have h3 : (v - pstar) ^ α ≤ h ^ α :=
          Real.rpow_le_rpow (by linarith [hv.1]) (by linarith [hv.2]) (by linarith)
        have h4 : R M pstar / 2 ≤ v * cdfBar M v := by
          have : R M v = v * cdfBar M v := rfl
          nlinarith [mul_le_mul_of_nonneg_left h3 hκU.le]
        have hcb : 0 ≤ cdfBar M v := by
          by_contra hneg
          push Not at hneg
          nlinarith [mul_neg_of_pos_of_neg hv0 hneg]
        show R M pstar / (2 * M.vbar) ≤ v * M.f v
        rw [div_le_iff₀ (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hvle hcb, mul_le_mul_of_nonneg_left h1 hvb.le])
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    have : p2 - pstar = h / 2 := by rw [hp2]; ring
    rw [this] at hmono
    exact hmono
  -- lottery part
  let q : ℝ → ℝ := fun θ => pstar + (min (max θ 0) 1) * h
  have hqm : Measurable q := by simp only [q]; fun_prop
  have hqB : ∀ θ, |q θ| ≤ pstar + h := by
    intro θ
    have h01 : 0 ≤ min (max θ 0) 1 ∧ min (max θ 0) 1 ≤ 1 :=
      ⟨le_min (le_max_right _ _) zero_le_one, min_le_right _ _⟩
    have : 0 ≤ q θ := by simp only [q]; nlinarith
    rw [abs_of_nonneg this]; simp only [q]; nlinarith
  have hT0eq : ∀ v, T0 v = ∫ θ in Ioc (0:ℝ) 1, if θ ≤ r v then q θ else 0 := by
    intro v
    rw [← int_ite q (r v) ⟨(hr01 v).1, (hr01 v).2⟩]
    have : ∫ θ in (0:ℝ)..r v, q θ = ∫ θ in (0:ℝ)..r v, (pstar + θ * h) := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      rw [uIcc_of_le (hr01 v).1] at hθ
      simp only [q]
      rw [max_eq_left hθ.1, min_eq_left (hθ.2.trans (hr01 v).2)]
    rw [this, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun θ => pstar * θ + h * θ ^ 2 / 2) (fun θ _ => ?_)
      ((by fun_prop : Continuous fun θ : ℝ => pstar + θ * h).intervalIntegrable _ _)]
    · simp only [T0]; ring
    · refine (((hasDerivAt_id' θ).const_mul pstar).add
        (((hasDerivAt_pow 2 θ).const_mul h).div_const 2)).congr_deriv ?_
      rw [show (2:ℕ) - 1 = 1 from rfl, pow_one]; push_cast; ring
  obtain ⟨_, hI2, hEq⟩ := fub M.f r q M.vbar (pstar + h) hfS hrc.measurable hqm hqB
  have hlot : R M pstar - κU * h ^ α ≤ ∫ v in Ioc 0 M.vbar, T0 v * M.f v := by
    have hfun : (fun v => T0 v * M.f v)
        = fun v => (∫ θ in Ioc (0:ℝ) 1, if θ ≤ r v then q θ else 0) * M.f v :=
      funext fun v => by rw [hT0eq v]
    rw [hfun, hEq]
    have hc1 : ∫ θ in Ioc (0:ℝ) 1, (R M pstar - κU * h ^ α) = R M pstar - κU * h ^ α := by simp
    rw [← hc1]
    refine setIntegral_mono_on (integrableOn_const (by simp)) hI2 measurableSet_Ioc ?_
    intro θ hθ
    have hq : q θ = pstar + θ * h := by
      simp only [q]; rw [max_eq_left hθ.1.le, min_eq_left hθ.2]
    have hθ0 : 0 ≤ θ * h := mul_nonneg hθ.1.le hh.le
    have hθh : θ * h ≤ h := by nlinarith [hθ.2]
    set c0 := pstar + θ * h with hc0def
    have hc0sub : c0 - pstar = θ * h := by rw [hc0def]; ring
    have hc0pos : 0 < c0 := by linarith
    have hc0le : c0 ≤ M.vbar := by linarith
    have hiff : ∀ v, θ ≤ r v ↔ c0 ≤ v := by
      intro v
      rw [hr_def, le_min_iff, le_max_iff, le_div_iff₀ hh]
      constructor
      · rintro ⟨h1 | h1, -⟩
        · linarith
        · linarith [hθ.1]
      · intro h1
        exact ⟨Or.inl (by linarith), hθ.2⟩
    have hin : ∫ v in Ioc 0 M.vbar, (if θ ≤ r v then M.f v else 0) = cdfBar M c0 := by
      have hind : (fun v => if θ ≤ r v then M.f v else 0) = (Ici c0).indicator M.f := by
        ext v; simp only [Set.indicator, mem_Ici, hiff v]
      have hset : Ioc 0 M.vbar ∩ Ici c0 = Icc c0 M.vbar := by
        ext v
        simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
      rw [hind, setIntegral_indicator measurableSet_Ici, hset, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hc0le, cdfBar_eq M hS]
    rw [hin, hq]
    have hRl := R_lower M hS pstar α κL κU ℓ hD c0 (by linarith) (by linarith)
    have hpow : (c0 - pstar) ^ α ≤ h ^ α :=
      Real.rpow_le_rpow (by rw [hc0sub]; exact hθ0) (by rw [hc0sub]; exact hθh) (by linarith)
    have : R M c0 = c0 * cdfBar M c0 := rfl
    have hk := mul_le_mul_of_nonneg_left hpow hκU.le
    linarith
  rw [hrev]
  have := mul_le_mul_of_nonneg_left hgain hc0
  have e2 : c * (h / 2 * (R M pstar / (2 * M.vbar))) = c * h * (R M pstar / (4 * M.vbar)) := by
    field_simp; ring
  linarith

end P1ae1

set_option maxHeartbeats 1000000 in
open ApproxIC.UpperBound in
theorem solution (M : Model) (hM : M.Assumption1) (pstar α κL κU ℓ : ℝ)
    (hD : LocalPowerEnvelope M pstar α κL κU ℓ) :
    ∃ C > 0, ∃ ε0 > 0, ∀ ε ∈ Set.Ioc (0 : ℝ) ε0, ∃ m ∈ Mset M ε,
      optRev M 0 + C * ε ^ (α / (2 * α - 1)) ≤ revenue M m := by
  have hS := hM.1
  have hD' := hD
  obtain ⟨hps, hmax, huniq, hα, hκL, hκU, hℓ, hsub, henv⟩ := hD'
  have hvb := hS.1
  obtain ⟨Rs, hRsdef⟩ : ∃ x, x = R M pstar := ⟨_, rfl⟩
  have hRs : 0 < Rs := by
    have h0 := isMaxOn_iff.1 hmax 0 ⟨le_rfl, hvb.le⟩
    have hR00 : R M 0 = 0 := by simp [R]
    by_contra hle
    push Not at hle
    have heq : R M 0 = R M pstar := by rw [hR00]; linarith
    have := huniq 0 ⟨le_rfl, hvb.le⟩ heq
    linarith [hps.1]
  obtain ⟨K1, hK1def⟩ : ∃ x, x = Rs / (4 * M.vbar) := ⟨_, rfl⟩
  have hK1 : 0 < K1 := by rw [hK1def]; positivity
  obtain ⟨m0, hm0def⟩ : ∃ x, x = min (min 1 (ℓ / 2)) (min (K1 / (2 * κU)) (Rs / (2 * κU))) :=
    ⟨_, rfl⟩
  have hm0 : 0 < m0 := by
    rw [hm0def]
    exact lt_min (lt_min one_pos (by linarith)) (lt_min (by positivity) (by positivity))
  have hm1 : m0 ≤ 1 := by rw [hm0def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : m0 ≤ ℓ / 2 := by rw [hm0def]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : m0 ≤ K1 / (2 * κU) := by rw [hm0def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hm4 : m0 ≤ Rs / (2 * κU) := by rw [hm0def]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hm3' : κU * m0 ≤ K1 / 2 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * κU)).1 hm3
    linarith
  have hm4' : κU * m0 ≤ Rs / 2 := by
    have := (le_div_iff₀ (by positivity : (0:ℝ) < 2 * κU)).1 hm4
    linarith
  have h2α : 1 < 2 * α - 1 := by linarith
  obtain ⟨s, hsdef⟩ : ∃ x, x = 1 / (2 * α - 1) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsdef]; apply div_pos one_pos; linarith
  have hs1 : s < 1 := by rw [hsdef, div_lt_one (by linarith)]; exact h2α
  obtain ⟨γ, hγdef⟩ : ∃ x, x = (1 - s) / 2 := ⟨_, rfl⟩
  have hγ : 0 < γ := by rw [hγdef]; linarith
  have hβ : γ + s = α / (2 * α - 1) := by
    rw [hγdef, hsdef]; field_simp; ring
  have hsα : s * α = α / (2 * α - 1) := by
    rw [hsdef]; field_simp
  have h2γ : γ * ((2:ℕ):ℝ) + s = 1 := by rw [hγdef]; push_cast; ring
  refine ⟨K1 * m0 / 2, by positivity, min 1 ((m0 / 2) ^ γ⁻¹),
    lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  rintro ε ⟨hε0, hεle⟩
  have hε1 : ε ≤ 1 := hεle.trans (min_le_left _ _)
  have hε2 : ε ≤ (m0 / 2) ^ γ⁻¹ := hεle.trans (min_le_right _ _)
  have hεs : 0 < ε ^ s := Real.rpow_pos_of_pos hε0 _
  have hεs1 : ε ^ s ≤ 1 := Real.rpow_le_one hε0.le hε1 hs0.le
  obtain ⟨h, hhdef⟩ : ∃ x, x = m0 ^ 2 * ε ^ s := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ x, x = ε ^ γ / m0 := ⟨_, rfl⟩
  have hh : 0 < h := by rw [hhdef]; positivity
  have hhm : h ≤ m0 := by
    rw [hhdef]
    have : m0 ^ 2 ≤ m0 := by nlinarith
    nlinarith
  have hhl : h < ℓ := by linarith
  have hεγ : ε ^ γ ≤ m0 / 2 := by
    calc ε ^ γ ≤ ((m0 / 2) ^ γ⁻¹) ^ γ := Real.rpow_le_rpow hε0.le hε2 hγ.le
      _ = m0 / 2 := Real.rpow_inv_rpow (by positivity) hγ.ne'
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hc : c ≤ 1 / 2 := by
    rw [hcdef, div_le_iff₀ hm0]; linarith
  have hce : c ^ 2 * h ≤ 2 * ε := by
    have e1 : (ε ^ γ) ^ 2 * ε ^ s = ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε0.le, ← Real.rpow_add hε0, h2γ, Real.rpow_one]
    have e2 : c ^ 2 * h = (ε ^ γ) ^ 2 * ε ^ s * (m0 ^ 2 / m0 ^ 2) := by
      rw [hcdef, hhdef]; ring
    rw [e2, div_self (pow_ne_zero 2 hm0.ne'), mul_one, e1]
    linarith
  have hκh : κU * h ^ α ≤ R M pstar / 2 := by
    have h1 : h ^ α ≤ h := by
      calc h ^ α ≤ h ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge hh (by linarith) hα.le
        _ = h := Real.rpow_one h
    have := mul_le_mul_of_nonneg_left (h1.trans hhm) hκU.le
    rw [← hRsdef]; linarith
  obtain ⟨m, hm, hrev⟩ := P1ae1.mech_bound M hS pstar α κL κU ℓ hD h c ε hh hhl hc0 hc hce hκh
  refine ⟨m, hm, ?_⟩
  have hopt := P1ae1.optRev0_le M hS pstar hmax
  rw [← hRsdef] at hrev hopt
  rw [← hK1def] at hrev
  have hch : c * h = m0 * ε ^ (α / (2 * α - 1)) := by
    rw [hcdef, hhdef, ← hβ, Real.rpow_add hε0]; field_simp
  have hhα : h ^ α ≤ m0 ^ 2 * ε ^ (α / (2 * α - 1)) := by
    have hm0sq : m0 ^ 2 ≤ 1 := by nlinarith
    calc h ^ α = (m0 ^ 2) ^ α * ε ^ (α / (2 * α - 1)) := by
          rw [hhdef, Real.mul_rpow (by positivity) hεs.le, ← Real.rpow_mul hε0.le, hsα]
      _ ≤ m0 ^ 2 * ε ^ (α / (2 * α - 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc (m0 ^ 2) ^ α ≤ (m0 ^ 2) ^ (1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_ge (by positivity) hm0sq hα.le
            _ = m0 ^ 2 := Real.rpow_one _
  have hεβ : 0 ≤ ε ^ (α / (2 * α - 1)) := by positivity
  have a1 := mul_le_mul_of_nonneg_left hhα hκU.le
  have a2 : κU * (m0 ^ 2 * ε ^ (α / (2 * α - 1))) ≤ K1 / 2 * (m0 * ε ^ (α / (2 * α - 1))) := by
    calc κU * (m0 ^ 2 * ε ^ (α / (2 * α - 1)))
        = (κU * m0) * (m0 * ε ^ (α / (2 * α - 1))) := by ring
      _ ≤ K1 / 2 * (m0 * ε ^ (α / (2 * α - 1))) :=
          mul_le_mul_of_nonneg_right hm3' (by positivity)
  have a3 : c * h * K1 = K1 * (m0 * ε ^ (α / (2 * α - 1))) := by rw [hch]; ring
  nlinarith [a1, a2, a3, hrev, hopt]
