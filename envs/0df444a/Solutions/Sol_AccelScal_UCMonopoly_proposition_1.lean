-- Prove2me | solution 1 for AccelScal.UCMonopoly.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T12:43:51.645386+00:00
-- url     : https://prove2.me/submissions/677cb4cd-134a-473c-8785-f5662f15b432

import Mathlib
import Definitions.Def_AccelScal_UCMonopoly_Setting

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

lemma clause2 (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (hβ : T.β = 0) (hγ : T.γ = 0) :
    RstarUC T r = {1} := by
  obtain ⟨hb1, -, -, -⟩ := base_facts T hT r hr
  have hη := hT.2.1
  have hcf : ∀ R : ℝ, 0 < R → ucPayoff T r R = (T.A * T.η - R) / (T.η + r) := by
    intro R hR
    rw [closed_form T r R hr hη hR, hβ, hγ, add_zero, Real.rpow_zero, mul_one, mul_one]
  have hD : 0 < T.η + r := by linarith
  ext R
  simp only [RstarUC, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨⟨h1, -⟩, hmax⟩
    have := hmax 1 ⟨le_rfl, hb1.le⟩
    rw [hcf 1 one_pos, hcf R (by linarith)] at this
    have := (div_le_div_iff_of_pos_right hD).1 this
    linarith
  · rintro rfl
    refine ⟨⟨le_rfl, hb1.le⟩, fun R' hR' => ?_⟩
    rw [hcf 1 one_pos, hcf R' (by linarith [hR'.1])]
    apply div_le_div_of_nonneg_right _ hD.le
    linarith [hR'.1]

lemma clauseA (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (A' : ℝ) (hA' : T.A < A') :
    OrderedAbove (RstarUC T r) (RstarUC { T with A := A' } r) := by
  obtain ⟨hb1, hVpos, hVb, hlt⟩ := base_facts T hT r hr
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hs, hK⟩ := hT
  have hcf' : ∀ R : ℝ, 0 < R → ucPayoff { T with A := A' } r R =
      (A' * T.η * R ^ (T.β + T.γ) - R) / (T.η * R ^ T.γ + r) :=
    fun R hR => closed_form { T with A := A' } r R hr hη hR
  have hbb : T.Rbar ≤ Tech.Rbar { T with A := A' } := by
    show (T.A * T.η) ^ (1 / (1 - (T.β + T.γ))) ≤ (A' * T.η) ^ (1 / (1 - (T.β + T.γ)))
    have : 0 < 1 - (T.β + T.γ) := by linarith
    apply Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
  have hKK : T.A * T.η < A' * T.η := mul_lt_mul_of_pos_right hA' hη
  refine above (ucPayoff T r) (ucPayoff { T with A := A' } r)
    (fun R => 1 * ((A' * T.η * R ^ (T.β + T.γ) - R) / (T.A * T.η * R ^ (T.β + T.γ) - R)))
    (fun R => 1 * (((A' * T.η * ((T.β + T.γ) * R ^ ((T.β + T.γ) - 1)) - 1)
        * (T.A * T.η * R ^ (T.β + T.γ) - R) - (A' * T.η * R ^ (T.β + T.γ) - R)
        * (T.A * T.η * ((T.β + T.γ) * R ^ ((T.β + T.γ) - 1)) - 1))
        / (T.A * T.η * R ^ (T.β + T.γ) - R) ^ 2))
    T.Rbar _ hb1 hbb hVpos hVb ?_ ?_ ?_ ?_ ?_
  · intro R h1 h2
    have hN0 := (sub_pos.mpr (hlt R h1 h2)).ne'
    rw [hcf' R (by linarith), closed_form T r R hr hη (by linarith)]
    have : 0 < R ^ T.γ := Real.rpow_pos_of_pos (by linarith) _
    have hD : T.η * R ^ T.γ + r ≠ 0 := by positivity
    field_simp
    rw [mul_div_cancel_right₀ _ (by intro h; apply hN0; linarith)]
  · intro R h1 h2
    have hN := hlt R h1 h2
    have hp : 0 < R ^ (T.β + T.γ) := Real.rpow_pos_of_pos (by linarith) _
    have h3 : T.A * T.η * R ^ (T.β + T.γ) < A' * T.η * R ^ (T.β + T.γ) :=
      mul_lt_mul_of_pos_right hKK hp
    show 0 < 1 * _
    rw [one_mul]
    exact div_pos (by linarith) (by linarith)
  · intro R h1 h2
    exact rhoK_deriv (T.A * T.η) (A' * T.η) (T.β + T.γ) 1 R (by linarith)
      (sub_pos.mpr (hlt R h1 h2)).ne'
  · intro R h1 h2
    exact rhoK_pos _ _ _ 1 R (by linarith) hKK hs one_pos (sub_pos.mpr (hlt R h1.le h2)).ne'
  · intro R h1 h2
    exact diff_V T r R hr hη (by linarith)

lemma clauseEta (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (hγ : T.γ = 0) (η' : ℝ)
    (hη' : T.η < η') : OrderedAbove (RstarUC T r) (RstarUC { T with η := η' } r) := by
  obtain ⟨hb1, hVpos, hVb, hlt⟩ := base_facts T hT r hr
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hs, hK⟩ := hT
  have hη'0 : 0 < η' := by linarith
  have hcf' : ∀ R : ℝ, 0 < R → ucPayoff { T with η := η' } r R =
      (T.A * η' * R ^ (T.β + T.γ) - R) / (η' * R ^ T.γ + r) :=
    fun R hR => closed_form { T with η := η' } r R hr hη'0 hR
  have hbb : T.Rbar ≤ Tech.Rbar { T with η := η' } := by
    show (T.A * T.η) ^ (1 / (1 - (T.β + T.γ))) ≤ (T.A * η') ^ (1 / (1 - (T.β + T.γ)))
    have : 0 < 1 - (T.β + T.γ) := by linarith
    apply Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
  have hKK : T.A * T.η < T.A * η' := mul_lt_mul_of_pos_left hη' hA
  have hc : 0 < (T.η + r) / (η' + r) := by positivity
  refine above (ucPayoff T r) (ucPayoff { T with η := η' } r)
    (fun R => (T.η + r) / (η' + r) *
      ((T.A * η' * R ^ (T.β + T.γ) - R) / (T.A * T.η * R ^ (T.β + T.γ) - R)))
    (fun R => (T.η + r) / (η' + r) * (((T.A * η' * ((T.β + T.γ) * R ^ ((T.β + T.γ) - 1)) - 1)
        * (T.A * T.η * R ^ (T.β + T.γ) - R) - (T.A * η' * R ^ (T.β + T.γ) - R)
        * (T.A * T.η * ((T.β + T.γ) * R ^ ((T.β + T.γ) - 1)) - 1))
        / (T.A * T.η * R ^ (T.β + T.γ) - R) ^ 2))
    T.Rbar _ hb1 hbb hVpos hVb ?_ ?_ ?_ ?_ ?_
  · intro R h1 h2
    have hN0 := (sub_pos.mpr (hlt R h1 h2)).ne'
    have h0 : R ^ T.γ = 1 := by rw [hγ, Real.rpow_zero]
    rw [hcf' R (by linarith), closed_form T r R hr hη (by linarith), h0, mul_one, mul_one]
    have hD : T.η + r ≠ 0 := by positivity
    have hD' : η' + r ≠ 0 := by positivity
    field_simp
    rw [mul_div_cancel_right₀ _ (by intro h; apply hN0; linarith)]
  · intro R h1 h2
    have hN := hlt R h1 h2
    have hp : 0 < R ^ (T.β + T.γ) := Real.rpow_pos_of_pos (by linarith) _
    have h3 : T.A * T.η * R ^ (T.β + T.γ) < T.A * η' * R ^ (T.β + T.γ) :=
      mul_lt_mul_of_pos_right hKK hp
    show 0 < _ * _
    exact mul_pos hc (div_pos (by linarith) (by linarith))
  · intro R h1 h2
    exact rhoK_deriv (T.A * T.η) (T.A * η') (T.β + T.γ) _ R (by linarith)
      (sub_pos.mpr (hlt R h1 h2)).ne'
  · intro R h1 h2
    exact rhoK_pos _ _ _ _ R (by linarith) hKK hs hc (sub_pos.mpr (hlt R h1.le h2)).ne'
  · intro R h1 h2
    exact diff_V T r R hr hη (by linarith)

lemma clauseBeta (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (β' : ℝ) (hββ : T.β < β')
    (hβ' : β' + T.γ < 1) : OrderedAbove (RstarUC T r) (RstarUC { T with β := β' } r) := by
  obtain ⟨hb1, hVpos, hVb, hlt⟩ := base_facts T hT r hr
  obtain ⟨hA, hη, hβ0, hβ1, hγ0, hγ1, hs, hK⟩ := hT
  have hcf' : ∀ R : ℝ, 0 < R → ucPayoff { T with β := β' } r R =
      (T.A * T.η * R ^ (β' + T.γ) - R) / (T.η * R ^ T.γ + r) :=
    fun R hR => closed_form { T with β := β' } r R hr hη hR
  have hbb : T.Rbar ≤ Tech.Rbar { T with β := β' } := by
    show (T.A * T.η) ^ (1 / (1 - (T.β + T.γ))) ≤ (T.A * T.η) ^ (1 / (1 - (β' + T.γ)))
    exact Real.rpow_le_rpow_of_exponent_le hK.le
      (one_div_le_one_div_of_le (by linarith) (by linarith))
  have hK0 : 0 < T.A * T.η := by linarith
  refine above (ucPayoff T r) (ucPayoff { T with β := β' } r)
    (fun R => (T.A * T.η * R ^ (β' + T.γ) - R) / (T.A * T.η * R ^ (T.β + T.γ) - R))
    (fun R => (((T.A * T.η * ((β' + T.γ) * R ^ ((β' + T.γ) - 1)) - 1)
        * (T.A * T.η * R ^ (T.β + T.γ) - R) - (T.A * T.η * R ^ (β' + T.γ) - R)
        * (T.A * T.η * ((T.β + T.γ) * R ^ ((T.β + T.γ) - 1)) - 1))
        / (T.A * T.η * R ^ (T.β + T.γ) - R) ^ 2))
    T.Rbar _ hb1 hbb hVpos hVb ?_ ?_ ?_ ?_ ?_
  · intro R h1 h2
    have hN0 := (sub_pos.mpr (hlt R h1 h2)).ne'
    rw [hcf' R (by linarith), closed_form T r R hr hη (by linarith)]
    have : 0 < R ^ T.γ := Real.rpow_pos_of_pos (by linarith) _
    have hD : T.η * R ^ T.γ + r ≠ 0 := by positivity
    field_simp
  · intro R h1 h2
    have hN := hlt R h1 h2
    have hle : R ^ (T.β + T.γ) ≤ R ^ (β' + T.γ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    have h3 : T.A * T.η * R ^ (T.β + T.γ) ≤ T.A * T.η * R ^ (β' + T.γ) :=
      mul_le_mul_of_nonneg_left hle hK0.le
    show 0 < _ / _
    exact div_pos (by linarith) (by linarith)
  · intro R h1 h2
    exact rhoB_deriv (T.A * T.η) (T.β + T.γ) (β' + T.γ) R (by linarith)
      (sub_pos.mpr (hlt R h1 h2)).ne'
  · intro R h1 h2
    exact rhoB_pos _ _ _ R h1 hK0 (by linarith) hs (hlt R h1.le h2)
  · intro R h1 h2
    exact diff_V T r R hr hη (by linarith)

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

lemma clauseR0 (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) (hγ : T.γ = 0) (r' : ℝ)
    (hr' : 0 < r') : RstarUC T r' = RstarUC T r := by
  have hη := hT.2.1
  have hc : 0 < (T.η + r) / (T.η + r') := by positivity
  have hscale : ∀ R : ℝ, 0 < R → ucPayoff T r' R = (T.η + r) / (T.η + r') * ucPayoff T r R := by
    intro R hR
    have h0 : R ^ T.γ = 1 := by rw [hγ, Real.rpow_zero]
    rw [closed_form T r' R hr' hη hR, closed_form T r R hr hη hR, h0, mul_one]
    have hD : T.η + r ≠ 0 := by positivity
    have hD' : T.η + r' ≠ 0 := by positivity
    field_simp
  ext R
  simp only [RstarUC, mem_setOf_eq]
  constructor
  · rintro ⟨hR, hmax⟩
    refine ⟨hR, fun R' hR' => ?_⟩
    have := hmax R' hR'
    rw [hscale R' (by linarith [hR'.1]), hscale R (by linarith [hR.1])] at this
    exact le_of_mul_le_mul_left this hc
  · rintro ⟨hR, hmax⟩
    refine ⟨hR, fun R' hR' => ?_⟩
    have := hmax R' hR'
    rw [hscale R' (by linarith [hR'.1]), hscale R (by linarith [hR.1])]
    exact mul_le_mul_of_nonneg_left this hc.le

end D4dc

open AccelScal.UCMonopoly in
theorem solution (T : Tech) (hT : T.Standing) (r : ℝ) (hr : 0 < r) :
    (RstarUC T r).Nonempty ∧
    (T.β = 0 → T.γ = 0 → RstarUC T r = {1}) ∧
    ((0 < T.β ∨ 0 < T.γ) → ∀ A' : ℝ, T.A < A' →
        OrderedAbove (RstarUC T r) (RstarUC { T with A := A' } r)) ∧
    (0 < T.β → ∀ β' : ℝ, T.β < β' → β' + T.γ < 1 →
        OrderedAbove (RstarUC T r) (RstarUC { T with β := β' } r)) ∧
    (T.γ = 0 → 0 < T.β → ∀ η' : ℝ, T.η < η' →
        OrderedAbove (RstarUC T r) (RstarUC { T with η := η' } r)) ∧
    (T.γ = 0 → ∀ r' : ℝ, 0 < r' → RstarUC T r' = RstarUC T r) ∧
    (0 < T.γ → ∀ r' : ℝ, r < r' → OrderedAbove (RstarUC T r) (RstarUC T r')) := by
  refine ⟨D4dc.nonempty_R T hT r hr, fun hβ hγ => D4dc.clause2 T hT r hr hβ hγ,
    fun _ A' hA' => D4dc.clauseA T hT r hr A' hA',
    fun _ β' h1 h2 => D4dc.clauseBeta T hT r hr β' h1 h2,
    fun hγ _ η' h => D4dc.clauseEta T hT r hr hγ η' h,
    fun hγ r' hr' => D4dc.clauseR0 T hT r hr hγ r' hr',
    fun hγ r' h => D4dc.clauseR T hT r hr hγ r' h⟩
