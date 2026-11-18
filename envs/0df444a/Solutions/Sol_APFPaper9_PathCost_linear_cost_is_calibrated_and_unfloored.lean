-- Prove2me | solution 1 for APFPaper9.PathCost.linear_cost_is_calibrated_and_unfloored
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:55:10.226206+00:00
-- url     : https://prove2.me/submissions/c8f66ec3-8740-4d58-8b33-9f39b5dd4caa

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not built on the build machine)
name: APFPaper9_a_calibrated_path_cost_is_unfloored
title: A cost that is bounded above and below by multiples of the displacement takes positive values below every floor; so a cost with a floor on every displacement has no such bound, and a cost whose nonzero values all sit at or above a floor vanishes on every small displacement where the upper bound holds
inputs_revision: 2026-11-14.1 (the occupant statement is NOT installed)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-16 09:51 HST: "Yes", to opening Paper 3 on the time point; and 09:52 HST:
 "Also need to look at paper 9".
 Consulted before writing. Paper 9 v3.8: 572-584 (comparison continuation: it "carries a probe's held
 continuation profile from x to y, preserves its complete contextual identity class along the way, and
 establishes endpoint correspondence"; its ledger is a sum of a transport, an identity and a
 correspondence term), 586-604 (directed comparison cost as an infimum; the direct local comparison
 germ, the limit of cost over displacement "Whenever the refinement limit exists"), 801-832 (physical
 interaction-ledger rate; the theorem "Calibrated ledger realization": constants 0 < a <= b with the
 ledger rate between a and b times the response gauge give a path cost between a and b times the
 response distance), 837-839 (the warning: "Fixed setup burdens, packet thresholds, indivisible tokens,
 saturation, and history-dependent hysteresis can make physical cost fail local one-homogeneity or
 refinement additivity"), 412 (non-claims: it "does not turn physical divisibility into the mathematical
 subdivision of a curve"). Paper 1 Supplement v9.28:1899 (P4). Paper 3 v3.23:1559-1605 (the cost-kind
 dichotomy). Codebank apf/operational_completeness.py check_T_ledger_rent_excluded
 ("C(transition) = n*eps"), apf/rent_exclusion_gate.py.
standing: ORDINARY MATHEMATICS. Real arithmetic on a supplied function d of a positive number t. Here t
 stands for a displacement (a response distance) and d t for the least cost of carrying a comparison
 over it. Nothing about Paper 9's quotient, gauge or substrate is typed.
consumes_inputs: none.
statement:
 - (calibrated_cost_goes_below_every_floor) if a t <= d t <= b t for every t > 0, with a and b
   positive, then for every e > 0 some t > 0 has 0 < d t < e.
 - (floored_cost_has_no_path_bound) if d t >= e > 0 for every t > 0, no b has d t <= b t for every
   t > 0.
 - (token_cost_under_a_path_bound_vanishes_nearby) if every value of d is either 0 or at least e, and
   d t <= b t for every t > 0, then d t = 0 whenever b t < e.
 - (token_cost_is_not_calibrated) so a cost whose nonzero values all sit at or above e > 0 is not
   bounded below and above by positive multiples of the displacement.
 - (linear_cost_is_calibrated_and_unfloored) the cost c t, with c positive, is so bounded, and goes
   below every floor.
reading: Paper 9's calibrated path ledger needs the cost of carrying a comparison to be positive and as
 small as the displacement is small. A floor on every such carrying (the Supplement's P4 as worded)
 rules that out. So does a cost counted in whole records (epsilon times a count). A cost of carrying
 that is positive and has no floor is what the calibration asks for.
not_claimed: that Paper 9's calibration hypothesis holds; that carrying a held profile makes or does not
 make a record; that a per-activation charge is positive. No lane. No claim that the transfer is forced,
 that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace APFPaper9.PathCost

/-- A cost bounded below and above by positive multiples of the displacement takes positive values below
every floor. -/
theorem calibrated_cost_goes_below_every_floor_p2mProof (d : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hcal : ∀ t, 0 < t → a * t ≤ d t ∧ d t ≤ b * t) (e : ℝ) (he : 0 < e) :
    ∃ t, 0 < t ∧ 0 < d t ∧ d t < e := by
  have ht : 0 < e / (2 * b) := div_pos he (by linarith)
  obtain ⟨hlo, hhi⟩ := hcal (e / (2 * b)) ht
  have hbt : b * (e / (2 * b)) = e / 2 := by
    field_simp
  have hat : 0 < a * (e / (2 * b)) := mul_pos ha ht
  exact ⟨e / (2 * b), ht, by linarith, by linarith⟩

/-- A cost with a floor on every displacement is bounded by no multiple of the displacement. -/
theorem floored_cost_has_no_path_bound_p2mProof (d : ℝ → ℝ) (e : ℝ) (he : 0 < e)
    (hfloor : ∀ t, 0 < t → e ≤ d t) : ¬ ∃ b : ℝ, ∀ t, 0 < t → d t ≤ b * t := by
  rintro ⟨b, hb⟩
  by_cases hb0 : 0 < b
  · have ht : 0 < e / (2 * b) := div_pos he (by linarith)
    have h1 := hb (e / (2 * b)) ht
    have h2 := hfloor (e / (2 * b)) ht
    have hbt : b * (e / (2 * b)) = e / 2 := by
      field_simp
    linarith
  · have h1 := hb 1 one_pos
    have h2 := hfloor 1 one_pos
    have h3 : b ≤ 0 := not_lt.mp hb0
    linarith

/-- A cost whose values are each zero or at least `e`, and which is bounded by `b` times the
displacement, vanishes on every displacement with `b t < e`. -/
theorem token_cost_under_a_path_bound_vanishes_nearby_p2mProof (d : ℝ → ℝ) (e b : ℝ)
    (htoken : ∀ t, 0 < t → d t = 0 ∨ e ≤ d t) (hb : ∀ t, 0 < t → d t ≤ b * t)
    (t : ℝ) (ht : 0 < t) (hsmall : b * t < e) : d t = 0 := by
  rcases htoken t ht with h | h
  · exact h
  · have := hb t ht
    linarith

/-- So a cost whose nonzero values all sit at or above a positive floor is not bounded below and above
by positive multiples of the displacement. -/
theorem token_cost_is_not_calibrated_p2mProof (d : ℝ → ℝ) (e : ℝ) (he : 0 < e)
    (htoken : ∀ t, 0 < t → d t = 0 ∨ e ≤ d t) :
    ¬ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ t, 0 < t → a * t ≤ d t ∧ d t ≤ b * t := by
  rintro ⟨a, b, ha, hb, hcal⟩
  obtain ⟨t, ht, hpos, hlt⟩ := calibrated_cost_goes_below_every_floor_p2mProof d a b ha hb hcal e he
  rcases htoken t ht with h | h
  · rw [h] at hpos
    exact lt_irrefl 0 hpos
  · linarith

/-- The cost `c t`, with `c` positive, is bounded below and above by `c` times the displacement, and
goes below every floor. -/
theorem linear_cost_is_calibrated_and_unfloored_p2mProof (c : ℝ) (hc : 0 < c) :
    (∀ t : ℝ, 0 < t → c * t ≤ c * t ∧ c * t ≤ c * t) ∧
      ∀ e : ℝ, 0 < e → ∃ t : ℝ, 0 < t ∧ 0 < c * t ∧ c * t < e := by
  refine ⟨fun t _ => ⟨le_refl _, le_refl _⟩, fun e he => ?_⟩
  exact calibrated_cost_goes_below_every_floor_p2mProof (fun t => c * t) c c hc hc
    (fun t _ => ⟨le_refl _, le_refl _⟩) e he

end APFPaper9.PathCost


theorem solution :
∀ (c : Real)
  (hc : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) c),
  And
    (∀ (t : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        And
          (@LE.le.{0} Real Real.instLE (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c t)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c t))
          (@LE.le.{0} Real Real.instLE (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c t)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c t)))
    (∀ (e : Real),
      @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) e →
        @Exists.{1} Real fun (t : Real) =>
          And
            (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t)
            (And
              (@LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c t))
              (@LT.lt.{0} Real Real.instLT (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) c t)
                e))) := by
  exact @APFPaper9.PathCost.linear_cost_is_calibrated_and_unfloored_p2mProof
