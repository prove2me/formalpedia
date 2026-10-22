-- Prove2me | solution 1 for AccelScal.UCRace.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T03:56:18.363499+00:00
-- url     : https://prove2.me/submissions/3b893ff4-f07a-4f65-858f-250b56b106ba

import Mathlib
import Definitions.Def_AccelScal_UCRace_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace D4dc

lemma inner_int (r τ : ℝ) (hr : 0 < r) :
    ∫ t in (0 : ℝ)..τ, Real.exp (-r * t) = (1 - Real.exp (-r * τ)) / r := by
  have hd : ∀ x ∈ uIcc (0 : ℝ) τ, HasDerivAt (fun t => -Real.exp (-r * t) / r) (Real.exp (-r * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t => -r * t) (-r) x := by
      simpa using (hasDerivAt_id x).const_mul (-r)
    have h2 := (h1.exp.neg).div_const r
    have hr0 : r ≠ 0 := ne_of_gt hr
    refine h2.congr_deriv ?_
    rw [mul_neg, neg_neg, mul_div_assoc, div_self hr0, mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp only [mul_zero, Real.exp_zero]
    field_simp
    ring
  · exact (by fun_prop : Continuous fun t => Real.exp (-r * t)).intervalIntegrable _ _

lemma exp_moment (lam a b c : ℝ) (hlam : 0 < lam) (hc : 0 < c) :
    ∫ τ, (a * Real.exp (-c * τ) + b) ∂(expMeasure lam) = a * lam / (lam + c) + b := by
  have hE : expMeasure lam = volume.withDensity (exponentialPDF lam) := rfl
  have hmeas : Measurable (exponentialPDF lam) := (measurable_exponentialPDFReal lam).ennreal_ofReal
  rw [hE, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  have hpt : ∀ x : ℝ, (exponentialPDF lam x).toReal • (a * Real.exp (-c * x) + b) =
      (Ici (0 : ℝ)).indicator (fun x => (a * lam) * Real.exp ((-(lam + c)) * x)
        + (b * lam) * Real.exp ((-lam) * x)) x := by
    intro x
    rw [exponentialPDF_eq]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, indicator_of_mem (by simpa using hx), ENNReal.toReal_ofReal (by positivity),
        smul_eq_mul]
      have : Real.exp ((-(lam + c)) * x) = Real.exp (-(lam * x)) * Real.exp (-c * x) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      have : Real.exp ((-lam) * x) = Real.exp (-(lam * x)) := by ring_nf
      rw [this]; ring
    · rw [if_neg hx, indicator_of_notMem (by simpa using hx)]
      simp
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  have hi1 : IntegrableOn (fun x : ℝ => Real.exp ((-(lam + c)) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  have hi2 : IntegrableOn (fun x : ℝ => Real.exp ((-lam) * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by linarith) 0
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_mul_Ioi (by linarith) 0, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  have h1 : lam + c ≠ 0 := by linarith
  have h2 : lam ≠ 0 := by linarith
  field_simp

open AccelScal.UCMonopoly in
lemma closed_form (T : Tech) (r R : ℝ) (hr : 0 < r) (hη : 0 < T.η) (hR : 0 < R) :
    ucPayoff T r R = (T.A * T.η * R ^ (T.β + T.γ) - R) / (T.η * R ^ T.γ + r) := by
  have hlam : 0 < T.lam R := by unfold Tech.lam; positivity
  unfold ucPayoff
  have hpt : ∀ τ : ℝ, (Real.exp (-r * τ) * T.u R - R * ∫ t in (0 : ℝ)..τ, Real.exp (-r * t)) =
      (T.u R + R / r) * Real.exp (-r * τ) + (-(R / r)) := by
    intro τ; rw [inner_int r τ hr]; field_simp; ring
  simp_rw [hpt]
  rw [exp_moment _ _ _ _ hlam hr]
  have hupow : T.u R * T.lam R = T.A * T.η * R ^ (T.β + T.γ) := by
    unfold Tech.u Tech.lam; rw [Real.rpow_add hR]; ring
  have h1 : T.lam R + r ≠ 0 := by linarith
  have hl : T.lam R = T.η * R ^ T.γ := rfl
  rw [← hupow, ← hl]
  field_simp
  ring


lemma rb_facts (K s : ℝ) (hK : 1 < K) (hs1 : s < 1) :
    1 < K ^ (1 / (1 - s)) ∧ K * (K ^ (1 / (1 - s))) ^ s = K ^ (1 / (1 - s)) ∧
      ∀ R : ℝ, 1 ≤ R → R < K ^ (1 / (1 - s)) → R < K * R ^ s := by
  have h1s : 0 < 1 - s := by linarith
  have hK0 : 0 < K := by linarith
  have hb1 : 1 < K ^ (1 / (1 - s)) := Real.one_lt_rpow hK (by positivity)
  have hbpos : 0 < K ^ (1 / (1 - s)) := by linarith
  have hbK : (K ^ (1 / (1 - s))) ^ (1 - s) = K := by
    rw [← Real.rpow_mul hK0.le, one_div, inv_mul_cancel₀ h1s.ne', Real.rpow_one]
  have hsplit : ∀ R : ℝ, 0 < R → R = R ^ (1 - s) * R ^ s := fun R hR => by
    rw [← Real.rpow_add hR, sub_add_cancel, Real.rpow_one]
  refine ⟨hb1, ?_, ?_⟩
  · have := hsplit _ hbpos
    rw [hbK] at this
    linarith
  · intro R hR1 hRb
    have hR0 : 0 < R := by linarith
    have h := Real.rpow_lt_rpow hR0.le hRb h1s
    rw [hbK] at h
    have hRs : 0 < R ^ s := Real.rpow_pos_of_pos hR0 s
    calc R = R ^ (1 - s) * R ^ s := hsplit R hR0
      _ < K * R ^ s := mul_lt_mul_of_pos_right h hRs

lemma hasDerivAt_N (K s R : ℝ) (hR : 0 < R) :
    HasDerivAt (fun R : ℝ => K * R ^ s - R) (K * (s * R ^ (s - 1)) - 1) R :=
  ((Real.hasDerivAt_rpow_const (Or.inl hR.ne')).const_mul K).sub (hasDerivAt_id' R)

lemma hasDerivAt_D (η γ c R : ℝ) (hR : 0 < R) :
    HasDerivAt (fun R : ℝ => η * R ^ γ + c) (η * (γ * R ^ (γ - 1))) R :=
  ((Real.hasDerivAt_rpow_const (Or.inl hR.ne')).const_mul η).add_const c

lemma rpow_sub_one_mul' (R s : ℝ) (hR : 0 < R) : R ^ (s - 1) * R = R ^ s := by
  rw [Real.rpow_sub_one hR.ne']; field_simp

open AccelScal.UCMonopoly in
lemma diff_V (T : Tech) (r x : ℝ) (hr : 0 < r) (hη : 0 < T.η) (hx : 0 < x) :
    DifferentiableAt ℝ (ucPayoff T r) x := by
  have hN := hasDerivAt_N (T.A * T.η) (T.β + T.γ) x hx
  have hD := hasDerivAt_D T.η T.γ r x hx
  have hDpos : T.η * x ^ T.γ + r ≠ 0 := by
    have := Real.rpow_pos_of_pos hx T.γ
    positivity
  have := (hN.div hD hDpos).differentiableAt
  refine this.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with R hR using closed_form T r R hr hη hR

lemma above (V W ρ ρ' : ℝ → ℝ) (b b' : ℝ) (hb1 : 1 < b) (hbb : b ≤ b')
    (hVpos : ∀ R, 1 ≤ R → R < b → 0 < V R) (hVb : V b ≤ 0)
    (hW : ∀ R, 1 ≤ R → R < b → W R = ρ R * V R)
    (hρpos : ∀ R, 1 ≤ R → R < b → 0 < ρ R)
    (hρd : ∀ R, 1 ≤ R → R < b → HasDerivAt ρ (ρ' R) R)
    (hρ' : ∀ R, 1 < R → R < b → 0 < ρ' R)
    (hVd : ∀ R, 1 < R → R < b → DifferentiableAt ℝ V R) :
    AccelScal.UCMonopoly.OrderedAbove {R | R ∈ Icc 1 b ∧ ∀ R' ∈ Icc 1 b, V R' ≤ V R}
      {R | R ∈ Icc 1 b' ∧ ∀ R' ∈ Icc 1 b', W R' ≤ W R} := by
  intro x hx y hy
  have hxb : x < b := by
    rcases lt_or_eq_of_le hx.1.2 with h | h
    · exact h
    · exfalso
      have h1 := hx.2 1 ⟨le_rfl, hb1.le⟩
      have h2 := hVpos 1 le_rfl hb1
      rw [h] at h1
      linarith
  have hmono : StrictMonoOn ρ (Ico 1 b) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico 1 b)
    · intro z hz
      exact (hρd z hz.1 hz.2).continuousAt.continuousWithinAt
    · intro z hz
      rw [interior_Ico] at hz
      rw [(hρd z hz.1.le hz.2).deriv]
      exact hρ' z hz.1 hz.2
  have hle : x ≤ y := by
    by_contra hlt'
    have hlt : y < x := lt_of_not_ge hlt'
    have hy1 : 1 ≤ y := hy.1.1
    have hyb : y < b := lt_trans hlt hxb
    have hVyx : V y ≤ V x := hx.2 y ⟨hy1, hyb.le⟩
    have hWxy : W x ≤ W y := hy.2 x ⟨hx.1.1, hxb.le.trans hbb⟩
    rw [hW x hx.1.1 hxb, hW y hy1 hyb] at hWxy
    have hρ : ρ y < ρ x := hmono ⟨hy1, hyb⟩ ⟨hx.1.1, hxb⟩ hlt
    have h1 := hρpos y hy1 hyb
    have h2 := hVpos x hx.1.1 hxb
    have h3 : ρ y * V y ≤ ρ y * V x := mul_le_mul_of_nonneg_left hVyx h1.le
    have h4 : ρ y * V x < ρ x * V x := mul_lt_mul_of_pos_right hρ h2
    linarith
  refine ⟨hle, fun h1x => ?_⟩
  rcases lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    subst h
    have hnhds : Ioo 1 b ∈ nhds x := Ioo_mem_nhds h1x hxb
    have hmaxV : IsLocalMax V x :=
      Filter.mem_of_superset hnhds (fun z hz => hx.2 z ⟨hz.1.le, hz.2.le⟩)
    have hmaxW : IsLocalMax W x :=
      Filter.mem_of_superset hnhds (fun z hz => hy.2 z ⟨hz.1.le, hz.2.le.trans hbb⟩)
    have hVd' := (hVd x h1x hxb).hasDerivAt
    have hV0 := hmaxV.hasDerivAt_eq_zero hVd'
    have hWd : HasDerivAt W (ρ' x * V x + ρ x * deriv V x) x := by
      have := (hρd x h1x.le hxb).mul hVd'
      apply this.congr_of_eventuallyEq
      filter_upwards [hnhds] with z hz using hW z hz.1.le hz.2
    have hW0 := hmaxW.hasDerivAt_eq_zero hWd
    rw [hV0, mul_zero, add_zero] at hW0
    have := mul_pos (hρ' x h1x hxb) (hVpos x h1x.le hxb)
    linarith

lemma rhoK_deriv (K K' s c R : ℝ) (hR : 0 < R) (hN : K * R ^ s - R ≠ 0) :
    HasDerivAt (fun R : ℝ => c * ((K' * R ^ s - R) / (K * R ^ s - R)))
      (c * (((K' * (s * R ^ (s - 1)) - 1) * (K * R ^ s - R)
        - (K' * R ^ s - R) * (K * (s * R ^ (s - 1)) - 1)) / (K * R ^ s - R) ^ 2)) R :=
  ((hasDerivAt_N K' s R hR).div (hasDerivAt_N K s R hR) hN).const_mul c

lemma rhoK_pos (K K' s c R : ℝ) (hR : 0 < R) (hKK : K < K') (hs1 : s < 1) (hc : 0 < c)
    (hN : K * R ^ s - R ≠ 0) :
    0 < c * (((K' * (s * R ^ (s - 1)) - 1) * (K * R ^ s - R)
        - (K' * R ^ s - R) * (K * (s * R ^ (s - 1)) - 1)) / (K * R ^ s - R) ^ 2) := by
  have hpt := rpow_sub_one_mul' R s hR
  have ht : 0 < R ^ s := Real.rpow_pos_of_pos hR s
  have hnum : ((K' * (s * R ^ (s - 1)) - 1) * (K * R ^ s - R)
        - (K' * R ^ s - R) * (K * (s * R ^ (s - 1)) - 1)) = (K' - K) * (1 - s) * R ^ s := by
    linear_combination (-(K' - K) * s) * hpt
  rw [hnum]
  have h1 : 0 < K' - K := by linarith
  have h2 : 0 < 1 - s := by linarith
  have h3 : 0 < (K * R ^ s - R) ^ 2 := by positivity
  positivity

lemma rhoB_deriv (K s s' R : ℝ) (hR : 0 < R) (hN : K * R ^ s - R ≠ 0) :
    HasDerivAt (fun R : ℝ => (K * R ^ s' - R) / (K * R ^ s - R))
      (((K * (s' * R ^ (s' - 1)) - 1) * (K * R ^ s - R)
        - (K * R ^ s' - R) * (K * (s * R ^ (s - 1)) - 1)) / (K * R ^ s - R) ^ 2) R :=
  (hasDerivAt_N K s' R hR).div (hasDerivAt_N K s R hR) hN

lemma rhoB_pos (K s s' R : ℝ) (hR1 : 1 < R) (hK : 0 < K) (hss : s < s') (hs1 : s < 1)
    (hlt : R < K * R ^ s) :
    0 < (((K * (s' * R ^ (s' - 1)) - 1) * (K * R ^ s - R)
        - (K * R ^ s' - R) * (K * (s * R ^ (s - 1)) - 1)) / (K * R ^ s - R) ^ 2) := by
  have hR : 0 < R := by linarith
  have hpt := rpow_sub_one_mul' R s hR
  have hpt' := rpow_sub_one_mul' R s' hR
  have hp : 0 < R ^ (s - 1) := Real.rpow_pos_of_pos hR _
  have ht' : 0 < R ^ s' := Real.rpow_pos_of_pos hR _
  have htt : R ^ s < R ^ s' := Real.rpow_lt_rpow_of_exponent_lt hR1 hss
  have hnum : ((K * (s' * R ^ (s' - 1)) - 1) * (K * R ^ s - R)
        - (K * R ^ s' - R) * (K * (s * R ^ (s - 1)) - 1)) =
        K ^ 2 * (s' - s) * R ^ (s - 1) * R ^ s' + K * (1 - s') * R ^ s' - K * (1 - s) * R ^ s := by
    linear_combination (-K ^ 2 * s' * R ^ (s' - 1) + K * s) * hpt
      + (K ^ 2 * s' * R ^ (s - 1) - K * s') * hpt'
  rw [hnum]
  have hKp : 1 < K * R ^ (s - 1) := by
    have : R * 1 < R * (K * R ^ (s - 1)) := by
      have : R * (K * R ^ (s - 1)) = K * (R ^ (s - 1) * R) := by ring
      rw [this, hpt]; linarith
    exact lt_of_mul_lt_mul_left this hR.le
  have e1 : 0 ≤ K * (s' - s) * R ^ s' * (K * R ^ (s - 1) - 1) := by
    have : 0 < s' - s := by linarith
    have : 0 < K * R ^ (s - 1) - 1 := by linarith
    positivity
  have e2 : 0 < K * (1 - s) * (R ^ s' - R ^ s) := by
    have : 0 < 1 - s := by linarith
    have : 0 < R ^ s' - R ^ s := by linarith
    positivity
  have hden : 0 < (K * R ^ s - R) ^ 2 := by
    have : 0 < K * R ^ s - R := by linarith
    positivity
  apply div_pos _ hden
  nlinarith [e1, e2]

lemma rhoR_deriv (η γ r r' R : ℝ) (hR : 0 < R) (hD : η * R ^ γ + r' ≠ 0) :
    HasDerivAt (fun R : ℝ => (η * R ^ γ + r) / (η * R ^ γ + r'))
      (((η * (γ * R ^ (γ - 1))) * (η * R ^ γ + r') - (η * R ^ γ + r) * (η * (γ * R ^ (γ - 1))))
        / (η * R ^ γ + r') ^ 2) R :=
  (hasDerivAt_D η γ r R hR).div (hasDerivAt_D η γ r' R hR) hD

lemma rhoR_pos (η γ r r' R : ℝ) (hR : 0 < R) (hη : 0 < η) (hγ : 0 < γ) (hrr : r < r')
    (hD : 0 < η * R ^ γ + r') :
    0 < (((η * (γ * R ^ (γ - 1))) * (η * R ^ γ + r') - (η * R ^ γ + r) * (η * (γ * R ^ (γ - 1))))
        / (η * R ^ γ + r') ^ 2) := by
  have hnum : ((η * (γ * R ^ (γ - 1))) * (η * R ^ γ + r') - (η * R ^ γ + r) * (η * (γ * R ^ (γ - 1))))
      = η * γ * R ^ (γ - 1) * (r' - r) := by ring
  rw [hnum]
  have : 0 < R ^ (γ - 1) := Real.rpow_pos_of_pos hR _
  have : 0 < r' - r := by linarith
  positivity

end D4dc

namespace D4dc
open AccelScal.UCMonopoly

lemma base_facts (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) :
    1 < T.Rbar ∧ (∀ R, 1 ≤ R → R < T.Rbar → 0 < ucPayoff T r R) ∧ ucPayoff T r T.Rbar ≤ 0 ∧
      (∀ R, 1 ≤ R → R < T.Rbar → R < T.A * T.η * R ^ (T.β + T.γ)) := by
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hs, hK⟩ := hT
  obtain ⟨hb1, hKb, hlt⟩ := rb_facts (T.A * T.η) (T.β + T.γ) hK hs
  have hRb : T.Rbar = (T.A * T.η) ^ (1 / (1 - (T.β + T.γ))) := rfl
  rw [hRb]
  refine ⟨hb1, ?_, ?_, hlt⟩
  · intro R h1 h2
    rw [closed_form T r R hr hη (by linarith)]
    have := hlt R h1 h2
    have : 0 < R ^ T.γ := Real.rpow_pos_of_pos (by linarith) _
    apply div_pos (by linarith) (by positivity)
  · rw [closed_form T r _ hr hη (by linarith), hKb, sub_self, zero_div]

lemma nonempty_R (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) : (RstarUC T r).Nonempty := by
  obtain ⟨hb1, -, -, -⟩ := base_facts T hT r hr
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hs, hK⟩ := hT
  have hcont : ContinuousOn (ucPayoff T r) (Icc 1 T.Rbar) := by
    have hg : ContinuousOn (fun R : ℝ => (T.A * T.η * R ^ (T.β + T.γ) - R) / (T.η * R ^ T.γ + r))
        (Icc 1 T.Rbar) := by
      apply ContinuousOn.div
      · exact ((continuous_const.mul (Real.continuous_rpow_const (by linarith))).sub
          continuous_id).continuousOn
      · exact ((continuous_const.mul (Real.continuous_rpow_const hγ0)).add
          continuous_const).continuousOn
      · intro R hR
        have := Real.rpow_pos_of_pos (by linarith [hR.1] : (0 : ℝ) < R) T.γ
        positivity
    exact hg.congr (fun R hR => closed_form T r R hr hη (by linarith [hR.1]))
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hb1.le) hcont
  exact ⟨x, hx, fun R' hR' => isMaxOn_iff.mp hmax R' hR'⟩
lemma clauseR (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (hγ : 0 < T.γ) (r' : ℝ)
    (hrr : r < r') : OrderedAbove (RstarUC T r) (RstarUC T r') := by
  obtain ⟨hb1, hVpos, hVb, hlt⟩ := base_facts T hT r hr
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hs, hK⟩ := hT
  have hr' : 0 < r' := by linarith
  refine above (ucPayoff T r) (ucPayoff T r')
    (fun R => (T.η * R ^ T.γ + r) / (T.η * R ^ T.γ + r'))
    (fun R => (((T.η * (T.γ * R ^ (T.γ - 1))) * (T.η * R ^ T.γ + r')
        - (T.η * R ^ T.γ + r) * (T.η * (T.γ * R ^ (T.γ - 1)))) / (T.η * R ^ T.γ + r') ^ 2))
    T.Rbar T.Rbar hb1 le_rfl hVpos hVb ?_ ?_ ?_ ?_ ?_
  · intro R h1 h2
    have hN0 := (sub_pos.mpr (hlt R h1 h2)).ne'
    rw [closed_form T r' R hr' hη (by linarith), closed_form T r R hr hη (by linarith)]
    have : 0 < R ^ T.γ := Real.rpow_pos_of_pos (by linarith) _
    have hD : T.η * R ^ T.γ + r ≠ 0 := by positivity
    have hD' : T.η * R ^ T.γ + r' ≠ 0 := by positivity
    field_simp
  · intro R h1 h2
    have : 0 < R ^ T.γ := Real.rpow_pos_of_pos (by linarith) _
    show 0 < _ / _
    positivity
  · intro R h1 h2
    have : 0 < R ^ T.γ := Real.rpow_pos_of_pos (by linarith) _
    exact rhoR_deriv T.η T.γ r r' R (by linarith) (by positivity)
  · intro R h1 h2
    have : 0 < R ^ T.γ := Real.rpow_pos_of_pos (by linarith) _
    exact rhoR_pos T.η T.γ r r' R (by linarith) hη hγ hrr (by positivity)
  · intro R h1 h2
    exact diff_V T r R hr hη (by linarith)


end D4dc

namespace P7a

lemma wd_rw (lam : ℝ) (f : ℝ → ℝ) :
    ∫ x, f x ∂(expMeasure lam) = ∫ x, (exponentialPDF lam x).toReal • f x := by
  have hE : expMeasure lam = volume.withDensity (exponentialPDF lam) := rfl
  have hmeas : Measurable (exponentialPDF lam) := (measurable_exponentialPDFReal lam).ennreal_ofReal
  rw [hE, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]

lemma int_congr_nonneg (lam : ℝ) (f g : ℝ → ℝ) (h : ∀ x, 0 ≤ x → f x = g x) :
    ∫ x, f x ∂(expMeasure lam) = ∫ x, g x ∂(expMeasure lam) := by
  rw [wd_rw, wd_rw]
  congr 1
  funext x
  by_cases hx : 0 ≤ x
  · rw [h x hx]
  · rw [exponentialPDF_eq, if_neg hx]
    simp

lemma tail_int (lam c p q x : ℝ) (hlam : 0 < lam) (hc : 0 < lam + c) (hx : 0 ≤ x) :
    ∫ y, (if x < y then p * Real.exp (-c * y) + q else 0) ∂(expMeasure lam)
      = p * lam / (lam + c) * Real.exp (-(lam + c) * x) + q * Real.exp (-lam * x) := by
  rw [wd_rw]
  have hpt : ∀ y : ℝ, (exponentialPDF lam y).toReal • (if x < y then p * Real.exp (-c * y) + q else 0)
      = (Ioi x).indicator (fun y => (p * lam) * Real.exp ((-(lam + c)) * y)
        + (q * lam) * Real.exp ((-lam) * y)) y := by
    intro y
    by_cases hy : x < y
    · have hy0 : 0 ≤ y := by linarith
      rw [if_pos hy, indicator_of_mem (by simpa using hy), exponentialPDF_eq, if_pos hy0,
        ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
      have : Real.exp ((-(lam + c)) * y) = Real.exp (-(lam * y)) * Real.exp (-c * y) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      have : Real.exp ((-lam) * y) = Real.exp (-(lam * y)) := by ring_nf
      rw [this]; ring
    · rw [if_neg hy, indicator_of_notMem (by simpa using hy)]
      simp
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Ioi]
  have hi1 : IntegrableOn (fun y : ℝ => Real.exp ((-(lam + c)) * y)) (Ioi x) :=
    integrableOn_exp_mul_Ioi (by linarith) x
  have hi2 : IntegrableOn (fun y : ℝ => Real.exp ((-lam) * y)) (Ioi x) :=
    integrableOn_exp_mul_Ioi (by linarith) x
  rw [integral_add (hi1.const_mul _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
    integral_exp_mul_Ioi (by linarith) x, integral_exp_mul_Ioi (by linarith) x]
  have h1 : lam + c ≠ 0 := by linarith
  have h2 : lam ≠ 0 := by linarith
  field_simp

lemma exp_integrable (lam c : ℝ) (hlam : 0 < lam) (hc : 0 < c) (a b : ℝ) :
    Integrable (fun y => a * Real.exp (-c * y) + b) (expMeasure lam) := by
  have := isProbabilityMeasure_expMeasure hlam
  have h := D4dc.exp_moment lam 1 0 c hlam hc
  have hne : ∫ τ, (1 * Real.exp (-c * τ) + 0) ∂(expMeasure lam) ≠ 0 := by
    rw [h]; have : 0 < lam + c := by linarith
    positivity
  have hi := Integrable.of_integral_ne_zero hne
  simp only [one_mul, add_zero] at hi
  exact (hi.const_mul a).add (integrable_const b)

lemma race_closed (l1 l2 r U R : ℝ) (h1 : 0 < l1) (h2 : 0 < l2) (hr : 0 < r) :
    ∫ p : ℝ × ℝ, (Real.exp (-r * p.1) * U * (if p.1 < p.2 then 1 else 0)
      - R * ∫ t in (0)..(min p.1 p.2), Real.exp (-r * t)) ∂((expMeasure l1).prod (expMeasure l2))
      = (U * l1 - R) / (r + l1 + l2) := by
  have := isProbabilityMeasure_expMeasure h1
  have := isProbabilityMeasure_expMeasure h2
  set S : Set (ℝ × ℝ) := {p | p.1 < p.2} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_fst measurable_snd
  let A : ℝ → ℝ := fun x => (U + R / r) * Real.exp (-r * x) + (-(R / r))
  let B : ℝ → ℝ := fun y => (R / r) * Real.exp (-r * y) + (-(R / r))
  let F : ℝ × ℝ → ℝ := fun p => S.indicator (fun p => A p.1) p + Sᶜ.indicator (fun p => B p.2) p
  have hpt : ∀ p : ℝ × ℝ, (Real.exp (-r * p.1) * U * (if p.1 < p.2 then 1 else 0)
      - R * ∫ t in (0)..(min p.1 p.2), Real.exp (-r * t)) = F p := by
    intro p
    rw [D4dc.inner_int r _ hr]
    by_cases h : p.1 < p.2
    · have hm : p ∈ S := h
      have hm' : p ∉ Sᶜ := fun h' => h' hm
      simp only [F, A, indicator_of_mem hm, indicator_of_notMem hm', if_pos h, min_eq_left h.le]
      field_simp
      ring
    · have hm : p ∉ S := h
      have hm' : p ∈ Sᶜ := hm
      simp only [F, B, indicator_of_mem hm', indicator_of_notMem hm, if_neg h,
        min_eq_right (not_lt.mp h)]
      field_simp
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have hAi : Integrable A (expMeasure l1) := exp_integrable l1 r h1 hr _ _
  have hBi : Integrable B (expMeasure l2) := exp_integrable l2 r h2 hr _ _
  have hF : Integrable F ((expMeasure l1).prod (expMeasure l2)) :=
    ((hAi.comp_fst _).indicator hSm).add ((hBi.comp_snd _).indicator hSm.compl)
  rw [integral_prod F hF]
  have hin : ∀ x : ℝ, 0 ≤ x → ∫ y, F (x, y) ∂(expMeasure l2) =
      ((U + R / r) - (R / r) * l2 / (l2 + r)) * Real.exp (-(l2 + r) * x)
        + ((R / r) * l2 / (l2 + r) - R / r) := by
    intro x hx
    have hsplit : ∀ y : ℝ, F (x, y) = (if x < y then (-(R / r)) * Real.exp (-r * y) + (A x + R / r)
        else 0) + ((R / r) * Real.exp (-r * y) + (-(R / r))) := by
      intro y
      by_cases h : x < y
      · have hm : (x, y) ∈ S := h
        have hm' : (x, y) ∉ Sᶜ := fun h' => h' hm
        simp only [F, B, indicator_of_mem hm, indicator_of_notMem hm', if_pos h]
        ring
      · have hm : (x, y) ∉ S := h
        have hm' : (x, y) ∈ Sᶜ := hm
        simp only [F, B, indicator_of_mem hm', indicator_of_notMem hm, if_neg h]
    simp_rw [hsplit]
    have hI1 : Integrable (fun y : ℝ => if x < y then (-(R / r)) * Real.exp (-r * y) + (A x + R / r)
        else 0) (expMeasure l2) := by
      have := (exp_integrable l2 r h2 hr (-(R / r)) (A x + R / r)).indicator
        (measurableSet_Ioi (a := x))
      refine this.congr (Filter.Eventually.of_forall (fun y => ?_))
      by_cases h : x < y
      · simp [h]
      · simp [h]
    rw [integral_add hI1 (exp_integrable l2 r h2 hr _ _),
      tail_int l2 r _ _ x h2 (by linarith) hx, D4dc.exp_moment l2 _ _ r h2 hr]
    have hex : Real.exp (-r * x) * Real.exp (-l2 * x) = Real.exp (-(l2 + r) * x) := by
      rw [← Real.exp_add]; ring_nf
    simp only [A]
    have hl2r : l2 + r ≠ 0 := by linarith
    rw [← hex]
    field_simp
    ring
  rw [int_congr_nonneg l1 _ _ hin, D4dc.exp_moment l1 _ _ (l2 + r) h1 (by linarith)]
  have hl2r : l2 + r ≠ 0 := by linarith
  have hall : r + l1 + l2 ≠ 0 := by linarith
  have hall' : l1 + (l2 + r) ≠ 0 := by linarith
  have hr0 : r ≠ 0 := hr.ne'
  field_simp
  ring

open AccelScal.UCRace

def mono (T : AccelScal.UCRace.Tech) : AccelScal.UCMonopoly.Tech := ⟨T.A, T.β, T.η, T.γ⟩

lemma mono_standing (T : AccelScal.UCRace.Tech) (h : T.Standing) : (mono T).Standing := h

lemma mono_Rbar (T : AccelScal.UCRace.Tech) : (mono T).Rbar = T.Rbar := rfl

lemma lam_pos (T : AccelScal.UCRace.Tech) (h : T.Standing) (R : ℝ) (hR : 0 < R) :
    0 < T.lam R := by
  have := h.2.1
  unfold Tech.lam
  have := Real.rpow_pos_of_pos hR T.γ
  positivity

lemma payoff1_eq (T1 T2 : AccelScal.UCRace.Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r R1 R2 : ℝ) (hr : 0 < r) (hR1 : 0 < R1) (hR2 : 0 < R2) :
    payoff1 T1 T2 r R1 R2 = AccelScal.UCMonopoly.ucPayoff (mono T1) (r + T2.lam R2) R1 := by
  have hl1 := lam_pos T1 h1 R1 hR1
  have hl2 := lam_pos T2 h2 R2 hR2
  rw [D4dc.closed_form (mono T1) (r + T2.lam R2) R1 (by linarith) h1.2.1 hR1]
  unfold payoff1 exponentialRace
  rw [race_closed _ _ r _ _ hl1 hl2 hr]
  have hu : T1.u R1 * T1.lam R1 = T1.A * T1.η * R1 ^ (T1.β + T1.γ) := by
    unfold Tech.u Tech.lam; rw [Real.rpow_add hR1]; ring
  have hl : T1.lam R1 = T1.η * R1 ^ T1.γ := rfl
  show _ = (T1.A * T1.η * R1 ^ (T1.β + T1.γ) - R1) / (T1.η * R1 ^ T1.γ + (r + T2.lam R2))
  rw [← hu, ← hl]
  congr 1
  ring

instance sfinite_exp (l : ℝ) : SFinite (expMeasure l) := by
  show SFinite (volume.withDensity (exponentialPDF l))
  infer_instance

lemma payoff2_swap (T1 T2 : AccelScal.UCRace.Tech) (r R1 R2 : ℝ) :
    payoff2 T1 T2 r R1 R2 = payoff1 T2 T1 r R2 R1 := by
  unfold payoff2 payoff1 exponentialRace
  rw [← integral_prod_swap]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap, min_comm]

lemma BR1_eq (T1 T2 : AccelScal.UCRace.Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r R2 : ℝ) (hr : 0 < r) (hR2 : 0 < R2) :
    BR1 T1 T2 r R2 = AccelScal.UCMonopoly.RstarUC (mono T1) (r + T2.lam R2) := by
  ext R
  simp only [BR1, AccelScal.UCMonopoly.RstarUC, mem_ofPred_eq, mono_Rbar]
  constructor
  · rintro ⟨hR, hmax⟩
    refine ⟨hR, fun R' hR' => ?_⟩
    have := hmax R' hR'
    rwa [payoff1_eq T1 T2 h1 h2 r R' R2 hr (by linarith [hR'.1]) hR2,
      payoff1_eq T1 T2 h1 h2 r R R2 hr (by linarith [hR.1]) hR2] at this
  · rintro ⟨hR, hmax⟩
    refine ⟨hR, fun R' hR' => ?_⟩
    rw [payoff1_eq T1 T2 h1 h2 r R' R2 hr (by linarith [hR'.1]) hR2,
      payoff1_eq T1 T2 h1 h2 r R R2 hr (by linarith [hR.1]) hR2]
    exact hmax R' hR'

lemma BR2_eq (T1 T2 : AccelScal.UCRace.Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r R1 : ℝ) (hr : 0 < r) (hR1 : 0 < R1) :
    BR2 T1 T2 r R1 = AccelScal.UCMonopoly.RstarUC (mono T2) (r + T1.lam R1) := by
  ext R
  simp only [BR2, AccelScal.UCMonopoly.RstarUC, mem_ofPred_eq, mono_Rbar, payoff2_swap]
  constructor
  · rintro ⟨hR, hmax⟩
    refine ⟨hR, fun R' hR' => ?_⟩
    have := hmax R' hR'
    rwa [payoff1_eq T2 T1 h2 h1 r R' R1 hr (by linarith [hR'.1]) hR1,
      payoff1_eq T2 T1 h2 h1 r R R1 hr (by linarith [hR.1]) hR1] at this
  · rintro ⟨hR, hmax⟩
    refine ⟨hR, fun R' hR' => ?_⟩
    rw [payoff1_eq T2 T1 h2 h1 r R' R1 hr (by linarith [hR'.1]) hR1,
      payoff1_eq T2 T1 h2 h1 r R R1 hr (by linarith [hR.1]) hR1]
    exact hmax R' hR'

lemma fixed (Φ : ℝ → Set ℝ) (b : ℝ) (hb : 1 ≤ b) (hne : ∀ x ∈ Icc 1 b, (Φ x).Nonempty)
    (hsub : ∀ x ∈ Icc 1 b, Φ x ⊆ Icc 1 b)
    (hmono : ∀ x x', x ∈ Icc 1 b → x' ∈ Icc 1 b → x < x' → ∀ y ∈ Φ x, ∀ w ∈ Φ x', y ≤ w) :
    ∃ R, R ∈ Φ R := by
  let S : Set ℝ := {x | x ∈ Icc 1 b ∧ ∃ y ∈ Φ x, x ≤ y}
  have h1I : (1 : ℝ) ∈ Icc 1 b := ⟨le_rfl, hb⟩
  have h1S : (1 : ℝ) ∈ S := by
    obtain ⟨y, hy⟩ := hne 1 h1I
    exact ⟨h1I, y, hy, (hsub 1 h1I hy).1⟩
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  obtain ⟨s, hs⟩ : ∃ s, s = sSup S := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := hs ▸ le_csSup hbdd h1S
  have hsb : s ≤ b := hs ▸ csSup_le ⟨1, h1S⟩ (fun x hx => hx.1.2)
  have hsI : s ∈ Icc 1 b := ⟨hs1, hsb⟩
  obtain ⟨z, hz, hsz⟩ : ∃ z ∈ Φ s, s ≤ z := by
    by_cases hsS : s ∈ S
    · exact hsS.2
    · obtain ⟨z, hz⟩ := hne s hsI
      refine ⟨z, hz, hs ▸ csSup_le ⟨1, h1S⟩ (fun x hx => ?_)⟩
      have hxs : x < s := lt_of_le_of_ne (hs ▸ le_csSup hbdd hx) (fun h => hsS (h ▸ hx))
      obtain ⟨y, hy, hxy⟩ := hx.2
      exact hxy.trans (hmono x s hx.1 hsI hxs y hy z hz)
  rcases eq_or_lt_of_le hsz with h | h
  · subst h
    exact ⟨s, hz⟩
  · exfalso
    have hzI : z ∈ Icc 1 b := hsub s hsI hz
    obtain ⟨w, hw⟩ := hne z hzI
    have hzS : z ∈ S := ⟨hzI, w, hw, hmono s z hsI hzI h z hz w hw⟩
    have : z ≤ s := hs ▸ le_csSup hbdd hzS
    linarith

lemma lam_zero (T : AccelScal.UCRace.Tech) (hγ : T.γ = 0) (R : ℝ) : T.lam R = T.η := by
  unfold Tech.lam; rw [hγ, Real.rpow_zero, mul_one]

lemma lam_lt (T : AccelScal.UCRace.Tech) (h : T.Standing) (hγ : 0 < T.γ) (R R' : ℝ)
    (hR : 0 < R) (hRR : R < R') : T.lam R < T.lam R' := by
  unfold Tech.lam
  exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow hR.le hRR hγ) h.2.1

end P7a

open AccelScal.UCRace in
theorem solution (T1 T2 : Tech) (h1 : T1.Standing) (h2 : T2.Standing)
    (r : ℝ) (hr : 0 < r) :
    (∀ R2, 0 < R2 → (BR1 T1 T2 r R2).Nonempty) ∧
    (∀ R1, 0 < R1 → (BR2 T1 T2 r R1).Nonempty) ∧
    (0 < T1.γ → 0 < T2.γ →
      (∀ R2 R2', 0 < R2 → R2 < R2' →
        AccelScal.UCMonopoly.OrderedAbove (BR1 T1 T2 r R2) (BR1 T1 T2 r R2')) ∧
      (∀ R1 R1', 0 < R1 → R1 < R1' →
        AccelScal.UCMonopoly.OrderedAbove (BR2 T1 T2 r R1) (BR2 T1 T2 r R1'))) ∧
    (T1.γ = 0 → T2.γ = 0 →
      (∀ R2 R2', 0 < R2 → 0 < R2' → BR1 T1 T2 r R2 = BR1 T1 T2 r R2') ∧
      (∀ R1 R1', 0 < R1 → 0 < R1' → BR2 T1 T2 r R1 = BR2 T1 T2 r R1')) ∧
    (T1 = T2 → ∃ R, IsNash T1 T2 r R R) := by
  refine ⟨fun R2 hR2 => ?_, fun R1 hR1 => ?_, fun hg1 hg2 => ⟨fun R2 R2' hR2 hlt => ?_,
    fun R1 R1' hR1 hlt => ?_⟩, fun hg1 hg2 => ⟨fun R2 R2' hR2 hR2' => ?_,
    fun R1 R1' hR1 hR1' => ?_⟩, fun hT => ?_⟩
  · rw [P7a.BR1_eq T1 T2 h1 h2 r R2 hr hR2]
    exact D4dc.nonempty_R _ (P7a.mono_standing T1 h1) _ (by linarith [P7a.lam_pos T2 h2 R2 hR2])
  · rw [P7a.BR2_eq T1 T2 h1 h2 r R1 hr hR1]
    exact D4dc.nonempty_R _ (P7a.mono_standing T2 h2) _ (by linarith [P7a.lam_pos T1 h1 R1 hR1])
  · rw [P7a.BR1_eq T1 T2 h1 h2 r R2 hr hR2, P7a.BR1_eq T1 T2 h1 h2 r R2' hr (by linarith)]
    exact D4dc.clauseR _ (P7a.mono_standing T1 h1) _ (by linarith [P7a.lam_pos T2 h2 R2 hR2]) hg1
      _ (by linarith [P7a.lam_lt T2 h2 hg2 R2 R2' hR2 hlt])
  · rw [P7a.BR2_eq T1 T2 h1 h2 r R1 hr hR1, P7a.BR2_eq T1 T2 h1 h2 r R1' hr (by linarith)]
    exact D4dc.clauseR _ (P7a.mono_standing T2 h2) _ (by linarith [P7a.lam_pos T1 h1 R1 hR1]) hg2
      _ (by linarith [P7a.lam_lt T1 h1 hg1 R1 R1' hR1 hlt])
  · rw [P7a.BR1_eq T1 T2 h1 h2 r R2 hr hR2, P7a.BR1_eq T1 T2 h1 h2 r R2' hr hR2',
      P7a.lam_zero T2 hg2, P7a.lam_zero T2 hg2]
  · rw [P7a.BR2_eq T1 T2 h1 h2 r R1 hr hR1, P7a.BR2_eq T1 T2 h1 h2 r R1' hr hR1',
      P7a.lam_zero T1 hg1, P7a.lam_zero T1 hg1]
  · subst hT
    have hb := (D4dc.base_facts _ (P7a.mono_standing T1 h1) r hr).1
    rw [P7a.mono_Rbar] at hb
    let Φ : ℝ → Set ℝ := fun x => AccelScal.UCMonopoly.RstarUC (P7a.mono T1) (r + T1.lam x)
    have hrl : ∀ x ∈ Icc 1 T1.Rbar, 0 < r + T1.lam x := fun x hx => by
      linarith [P7a.lam_pos T1 h1 x (by linarith [hx.1])]
    have hne : ∀ x ∈ Icc 1 T1.Rbar, (Φ x).Nonempty := fun x hx =>
      D4dc.nonempty_R _ (P7a.mono_standing T1 h1) _ (hrl x hx)
    have hsub : ∀ x ∈ Icc 1 T1.Rbar, Φ x ⊆ Icc 1 T1.Rbar := fun x _ y hy => hy.1
    have key : ∃ R, R ∈ Φ R := by
      rcases eq_or_lt_of_le h1.2.2.2.2.1 with hg | hg
      · obtain ⟨R, hR⟩ := hne 1 ⟨le_rfl, hb.le⟩
        refine ⟨R, ?_⟩
        show R ∈ AccelScal.UCMonopoly.RstarUC (P7a.mono T1) (r + T1.lam R)
        rw [P7a.lam_zero T1 hg.symm]
        rw [show Φ 1 = AccelScal.UCMonopoly.RstarUC (P7a.mono T1) (r + T1.lam 1) from rfl,
          P7a.lam_zero T1 hg.symm] at hR
        exact hR
      · refine P7a.fixed Φ T1.Rbar hb.le hne hsub ?_
        intro x x' hx hx' hxx' y hy w hw
        have hO := D4dc.clauseR _ (P7a.mono_standing T1 h1) _ (hrl x hx) hg (r + T1.lam x')
          (by linarith [P7a.lam_lt T1 h1 hg x x' (by linarith [hx.1]) hxx'])
        exact (hO y hy w hw).1
    obtain ⟨R, hR⟩ := key
    have hR0 : 0 < R := by linarith [(hsub R (hR.1) hR).1]
    refine ⟨R, ?_, ?_⟩
    · rw [P7a.BR1_eq T1 T1 h1 h1 r R hr hR0]; exact hR
    · rw [P7a.BR2_eq T1 T1 h1 h1 r R hr hR0]; exact hR
