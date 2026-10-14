-- Prove2me | solution 1 for ActuarialValuation.srRuinProbBy_Lundberg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T20:33:46.001847+00:00
-- url     : https://prove2.me/submissions/0967bfd4-ec2b-4a21-871d-f7ae6a4247b7

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Definitions.Def_actuarial_srRuinProbabilityBy
import Definitions.Def_actuarial_srLundbergBound
import Definitions.Def_actuarial_srStoppedExp
import Definitions.Def_actuarial_srStoppedMoment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (R u c : ℝ) (W Y : ℕ → Ω → ℝ) (N : ℕ)
    (hR : 0 < R) (hW : ∀ j, Measurable (W j))
    (hY : ∀ j, Measurable (Y j))
    (hint : MeasureTheory.Integrable (srStoppedExp R u c W Y N) μ)
    (hstop : srStoppedMoment μ R u c W Y N ≤ 1) :
    srRuinProbabilityBy μ u c W Y N ≤ srLundbergBound R u := by
  classical
  have hpoint (ω : Ω) (hr : srRuinBy u c W Y N ω) :
      Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω := by
    have hruin : srRuinBy u c W Y N ω := hr
    rcases hr with ⟨n, hnN, hn⟩
    let hex : ∃ j : ℕ, srRuinAt u c W Y j ω := ⟨n, hn⟩
    have hk_le_n : Nat.find hex ≤ n := by
      by_contra hnot
      exact Nat.find_min hex (lt_of_not_ge hnot) hn
    let k : ℕ := Nat.find hex
    have hkN : k ≤ N := le_trans hk_le_n hnN
    have hkFirst : srFirstHit u c W Y k ω := by
      constructor
      · exact Nat.find_spec hex
      · intro j hj
        exact Nat.find_min hex hj
    have hnet : u < srNetLoss c W Y k ω := by
      have hneg : srRuinAt u c W Y k ω := hkFirst.1
      change srSurplus u c W Y k ω < 0 at hneg
      unfold srSurplus at hneg
      linarith
    have hExp : Real.exp (R * u) ≤ srExpLoss R c W Y k ω := by
      unfold srExpLoss
      exact le_of_lt ((Real.exp_lt_exp).2 (mul_lt_mul_of_pos_left hnet hR))
    have hterm_nonneg (j : ℕ) :
        0 ≤ (if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0) := by
      by_cases hj : srFirstHit u c W Y j ω
      · simp only [if_pos hj]
        unfold srExpLoss
        exact (Real.exp_pos _).le
      · simp [hj]
    have hsum :
        (if srFirstHit u c W Y k ω then srExpLoss R c W Y k ω else 0) ≤
          ∑ j ∈ Finset.range (N + 1),
            if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0 := by
      exact Finset.single_le_sum
        (s := Finset.range (N + 1))
        (f := fun j => if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0)
        (a := k)
        (fun j _ => hterm_nonneg j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hkN))
    have hterm : Real.exp (R * u) ≤
        (if srFirstHit u c W Y k ω then srExpLoss R c W Y k ω else 0) := by
      simpa only [if_pos hkFirst] using hExp
    calc
      Real.exp (R * u) ≤
          (if srFirstHit u c W Y k ω then srExpLoss R c W Y k ω else 0) := hterm
      _ ≤ ∑ j ∈ Finset.range (N + 1),
            if srFirstHit u c W Y j ω then srExpLoss R c W Y j ω else 0 := hsum
      _ = srStoppedExp R u c W Y N ω := by
        simp [srStoppedExp, hruin]
  have hnonneg (ω : Ω) : 0 ≤ srStoppedExp R u c W Y N ω := by
    dsimp [srStoppedExp, srExpLoss]
    positivity
  have hf_nonneg : 0 ≤ᵐ[μ] srStoppedExp R u c W Y N :=
    Filter.Eventually.of_forall hnonneg
  have hmarkov :
      Real.exp (R * u) *
          (μ {ω | Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω}).toReal ≤
      srStoppedMoment μ R u c W Y N := by
    have hmarkovraw :=
      MeasureTheory.mul_meas_ge_le_integral_of_nonneg
        (μ := μ) (f := srStoppedExp R u c W Y N)
        hf_nonneg hint (Real.exp (R * u))
    simpa only [srStoppedMoment, MeasureTheory.Measure.real] using hmarkovraw
  have hsub : {ω | srRuinBy u c W Y N ω} ⊆
      {ω | Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω} := by
    intro ω h
    exact hpoint ω h
  have hmeasure : μ {ω | srRuinBy u c W Y N ω} ≤
      μ {ω | Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω} :=
    MeasureTheory.measure_mono hsub
  have hfinite :
      μ {ω | Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω} ≠ ⊤ := by
    have ht :
        μ {ω | Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω} ≤ 1 := by
      calc
        μ {ω | Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω}
            ≤ μ Set.univ := MeasureTheory.measure_mono (Set.subset_univ _)
        _ = 1 := MeasureTheory.measure_univ
    exact ne_of_lt (lt_of_le_of_lt ht (by simp))
  have hmeasure_real :
      (μ {ω | srRuinBy u c W Y N ω}).toReal ≤
      (μ {ω | Real.exp (R * u) ≤ srStoppedExp R u c W Y N ω}).toReal :=
    ENNReal.toReal_mono hfinite hmeasure
  have hεpos : 0 < Real.exp (R * u) := Real.exp_pos _
  have hmul :
      Real.exp (R * u) * (μ {ω | srRuinBy u c W Y N ω}).toReal ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hmeasure_real hεpos.le).trans
      (hmarkov.trans hstop)
  have hdiv : (μ {ω | srRuinBy u c W Y N ω}).toReal ≤
      1 / Real.exp (R * u) :=
    (le_div_iff₀ hεpos).2 (by simpa [mul_comm] using hmul)
  unfold srRuinProbabilityBy srLundbergBound
  calc
    (μ {ω | srRuinBy u c W Y N ω}).toReal
        ≤ 1 / Real.exp (R * u) := hdiv
    _ = Real.exp (-(R * u)) := by simp [Real.exp_neg, one_div]
    _ = Real.exp (-R * u) := by congr 1; ring
