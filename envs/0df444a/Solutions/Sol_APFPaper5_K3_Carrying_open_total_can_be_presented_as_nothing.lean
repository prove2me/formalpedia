-- Prove2me | solution 1 for APFPaper5.K3.Carrying.open_total_can_be_presented_as_nothing
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-17T04:31:46.843212+00:00
-- url     : https://prove2.me/submissions/4e448179-1e8f-4846-a0aa-0799cf575259

import Definitions.Def_APFPaper5_K3_what_a_charge_on_carrying_does_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not built on the build machine)
name: APFPaper5_K3_what_a_charge_on_carrying_does
title: Three facts about a charge on a way that makes no record. If the charge is booked in a ledger whose value is a function of the state, every step round a closed way is free. If the charge is held as a turn, a turn common to two arms is unseen where they meet and only the turn of one against the other is counted. If the way alternatives are compared from place to place is re-presented, the charge of an open way changes by its two ends only, can be presented as nothing, and the charge round a closed way and the difference between two ways with the same ends do not change
inputs_revision: 2026-11-14.1 (the occupant statement is NOT installed)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-16 10:05 HST: "Let's dig in here and think about the quantum and gauge
 consequences carefully", on the call whether carrying a held profile from place to place is charged.
 Consulted before writing. Paper 5 Supplement v7.33: 3326-3333 (the ruled formulation: "Pricing is
 phase-neutral"; sign and phase moves "are not record-free --- relative, recombination-visible phase
 carries record content"; "Price-blind, not record-blind"; "phase being real but unbillable"),
 1826-1832 ("Only the diagonal common action is record-null"), 1408-1431. Paper 3 v3.23: 1569-1590
 ("Accumulated cost is a state function"; "Everything pays deposits and reading fees"), 1693. Paper 12
 v1.8: 396-401 (raw link variables are "gauge-variant, hence convention, not billed content"), 950-962
 (energy and capacity are "different ledgers"), 1117-1124 (reading R: the records of a gauge interface
 "are exactly its gauge-invariant operators"), 1264 (the U(1) sector "reversible, massless,
 unconfined"), 1314-1330 (the connection is "a gauge-variant convention"; fixing it "requires an
 across-interface frame identification" and "the substrate registers no such primitive"), 1333-1337.
 Paper 9 v3.8: 572-584, 814-839, 2090-2104. Paper 7 v2.16: 394-409. Codebank: apf/photon_masslessness.py
 ("Mass <=> a locked record at the scale; masslessness <=> no record"), apf/gauge_invariant_record.py,
 apf/gauge_quotient_ledger.py (GQL-1, "the NAMED IDENTIFICATION": "a record fact at a gauged interface
 is gauge-invariant"), apf/base_fiber_allocation.py
 (check_T_gauge_connection_is_gauge_variant_convention_P), apf/one_context_one_transport.py (the two
 premises "UNIFORM FRAME COST, ONE GLOBAL eps" and "NATURALITY: U* R U = R"),
 apf/presentation_gauge_forcing.py, apf/operational_completeness.py, apf/rent_exclusion_gate.py,
 apf/cost_energy_identity.py. This seat's Thm_APFPaper5_K3_free_number_on_each_connection (pass 72:
 bill_flat_iff, least_cost_table_unique, count_valued_bill_is_flat).
standing: ORDINARY MATHEMATICS ON SUPPLIED DATA. The places, the path, the charge per step, the state
 function, the turns and the rule for what is counted where two arms meet are all supplied. The rule
 used where two arms meet is the squared length of the sum, in real form.
consumes_inputs: none.
statement:
 total A p n is the charge of the first n steps of the path p at charge A per step.
 A. Booked charge.
 - (total_of_a_state_function) if the charge of a step is the change of a function E of the state, the
   total is E at the end less E at the start.
 - (booked_total_round_a_loop) so round a closed way the total is nothing.
 - (booked_steps_round_a_loop_are_free) and if no step lowers E, no step of a closed way changes E:
   every step is free.
 B. Held charge, as a turn.
 - (common_turn_is_unseen) turning both arms by the same turn leaves what is counted where they meet
   as it was.
 - (relative_turn_is_counted) turning one arm and not the other is counted: the count is 2 + 2c, where c
   is the first number of the turn.
 - (relative_turn_unseen_iff) it equals the count with no turn exactly when the turn is no turn.
 - (quarter_relative_turn_halves_the_count) at a quarter turn the count is half.
 C. Re-presenting how alternatives are compared from place to place.
 - (represented_total) the total of an open way changes by a term at each of its two ends.
 - (loop_total_is_the_same_under_every_presentation) round a closed way it does not change.
 - (open_total_can_be_presented_as_nothing) the total of a way that does not close can be presented
   as nothing.
 - (difference_of_two_ways_with_the_same_ends) the difference between the totals of two ways with the
   same start and the same end does not change.
reading: a charge on carrying cannot be a booked record-cost and also be positive round a loop. A charge
 on an open carrying is not a fact: it depends on the presentation. What is a fact is the charge round
 a loop, which is the difference between two arms, and that is what a meeting of the arms counts.
not_claimed: that the physical ledger is a state function; that carrying is or is not charged; that the
 rule used where two arms meet is derived; that the presentation freedom here is the physical gauge
 freedom. No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or
 that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace APFPaper5.K3.Carrying

universe u

section Paths
variable {X : Type u}



theorem total_zero (A : X → X → ℝ) (p : ℕ → X) : total A p 0 = 0 := rfl

theorem total_succ (A : X → X → ℝ) (p : ℕ → X) (n : ℕ) :
    total A p (n + 1) = total A p n + A (p n) (p (n + 1)) := rfl

/-! ### A. Booked charge: the ledger is a function of the state -/

/-- If the charge of a step is the change of a function `E` of the state, the total is `E` at the end
less `E` at the start. -/
theorem total_of_a_state_function_p2mProof (E : X → ℝ) (p : ℕ → X) (n : ℕ) :
    total (fun x y => E y - E x) p n = E (p n) - E (p 0) := by
  induction n with
  | zero => rw [total_zero]; ring
  | succ n ih => rw [total_succ, ih]; ring

/-- So round a closed way the booked total is nothing. -/
theorem booked_total_round_a_loop_p2mProof (E : X → ℝ) (p : ℕ → X) (n : ℕ) (hloop : p n = p 0) :
    total (fun x y => E y - E x) p n = 0 := by
  rw [total_of_a_state_function_p2mProof, hloop]; ring

/-- If no step lowers `E`, then `E` does not fall along the way. -/
theorem state_function_does_not_fall (E : X → ℝ) (p : ℕ → X) (n : ℕ)
    (hstep : ∀ i, i < n → E (p i) ≤ E (p (i + 1))) :
    ∀ i j, i ≤ j → j ≤ n → E (p i) ≤ E (p j) := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_refl _
  | succ j hj ih =>
    intro hjn
    exact le_trans (ih (by omega)) (hstep j (by omega))

/-- And if no step lowers `E`, no step of a closed way changes `E`: every step is free. -/
theorem booked_steps_round_a_loop_are_free_p2mProof (E : X → ℝ) (p : ℕ → X) (n : ℕ)
    (hstep : ∀ i, i < n → E (p i) ≤ E (p (i + 1))) (hloop : p n = p 0) :
    ∀ i, i < n → E (p (i + 1)) - E (p i) = 0 := by
  intro i hi
  have h1 := hstep i hi
  have h2 := state_function_does_not_fall E p n hstep (i + 1) n (by omega) (le_refl n)
  have h3 := state_function_does_not_fall E p n hstep 0 i (Nat.zero_le i) (by omega)
  rw [hloop] at h2
  linarith

/-! ### C. Re-presenting how alternatives are compared from place to place -/



/-- The total of an open way changes by a term at each of its two ends, and by nothing else. -/
theorem represented_total_p2mProof (g : X → ℝ) (A : X → X → ℝ) (p : ℕ → X) (n : ℕ) :
    total (represent g A) p n = total A p n + g (p n) - g (p 0) := by
  induction n with
  | zero => rw [total_zero, total_zero]; ring
  | succ n ih =>
    rw [total_succ, total_succ, ih]
    unfold represent
    ring

/-- Round a closed way the total is the same under every presentation. -/
theorem loop_total_is_the_same_under_every_presentation_p2mProof (g : X → ℝ) (A : X → X → ℝ) (p : ℕ → X)
    (n : ℕ) (hloop : p n = p 0) : total (represent g A) p n = total A p n := by
  rw [represented_total_p2mProof, hloop]; ring

/-- The total of a way that does not close can be presented as nothing. -/
theorem open_total_can_be_presented_as_nothing_p2mProof (A : X → X → ℝ) (p : ℕ → X) (n : ℕ)
    (hopen : p n ≠ p 0) : ∃ g : X → ℝ, total (represent g A) p n = 0 := by
  classical
  refine ⟨fun x => if x = p n then -total A p n else 0, ?_⟩
  rw [represented_total_p2mProof]
  have h1 : (if p n = p n then -total A p n else 0) = -total A p n := if_pos rfl
  have h2 : (if p 0 = p n then -total A p n else 0) = 0 := if_neg (fun h => hopen h.symm)
  show total A p n + (if p n = p n then -total A p n else 0) -
    (if p 0 = p n then -total A p n else 0) = 0
  rw [h1, h2]; ring

/-- The difference between the totals of two ways with the same start and the same end is the same
under every presentation. -/
theorem difference_of_two_ways_with_the_same_ends_p2mProof (g : X → ℝ) (A : X → X → ℝ) (p q : ℕ → X)
    (n m : ℕ) (hstart : p 0 = q 0) (hend : p n = q m) :
    total (represent g A) p n - total (represent g A) q m = total A p n - total A q m := by
  rw [represented_total_p2mProof, represented_total_p2mProof, hstart, hend]; ring

end Paths

/-! ### B. Held charge, as a turn: what is counted where two arms meet -/





/-- Turning both arms by the same turn leaves what is counted where they meet as it was. -/
theorem common_turn_is_unseen_p2mProof (c s : ℝ) (hcs : c * c + s * s = 1) (u v : ℝ × ℝ) :
    meet (turnBy c s u) (turnBy c s v) = meet u v := by
  have h : meet (turnBy c s u) (turnBy c s v) = (c * c + s * s) * meet u v := by
    unfold meet turnBy
    ring
  rw [h, hcs, one_mul]

/-- Turning one arm and not the other is counted: the count is `2 + 2c`. -/
theorem relative_turn_is_counted_p2mProof (c s : ℝ) (hcs : c * c + s * s = 1) (u : ℝ × ℝ)
    (hu : u.1 * u.1 + u.2 * u.2 = 1) : meet (turnBy c s u) u = 2 + 2 * c := by
  have h : meet (turnBy c s u) u =
      (c * c + s * s) * (u.1 * u.1 + u.2 * u.2) + (u.1 * u.1 + u.2 * u.2) +
        2 * c * (u.1 * u.1 + u.2 * u.2) := by
    unfold meet turnBy
    ring
  rw [h, hcs, hu]; ring

/-- With no turn the count is 4. -/
theorem no_turn_count (u : ℝ × ℝ) (hu : u.1 * u.1 + u.2 * u.2 = 1) : meet u u = 4 := by
  have h : meet u u = 4 * (u.1 * u.1 + u.2 * u.2) := by
    unfold meet
    ring
  rw [h, hu]; ring

/-- The count with a turn on one arm equals the count with no turn exactly when the turn is no turn. -/
theorem relative_turn_unseen_iff_p2mProof (c s : ℝ) (hcs : c * c + s * s = 1) (u : ℝ × ℝ)
    (hu : u.1 * u.1 + u.2 * u.2 = 1) : meet (turnBy c s u) u = meet u u ↔ c = 1 := by
  rw [relative_turn_is_counted_p2mProof c s hcs u hu, no_turn_count u hu]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- At a quarter turn on one arm the count is half the count with no turn. -/
theorem quarter_relative_turn_halves_the_count_p2mProof (u : ℝ × ℝ) (hu : u.1 * u.1 + u.2 * u.2 = 1) :
    meet (turnBy 0 1 u) u = meet u u / 2 := by
  rw [relative_turn_is_counted_p2mProof 0 1 (by ring) u hu, no_turn_count u hu]; ring

end APFPaper5.K3.Carrying


universe apfNative_u
theorem solution :
∀ {X : Type apfNative_u} (A : X → X → Real) (p : Nat → X) (n : Nat)
  (hopen : @Ne.{apfNative_u + 1} X (p n) (p (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))),
  @Exists.{apfNative_u + 1} (X → Real) fun (g : X → Real) =>
    @Eq.{1} Real
      (@APFPaper5.K3.Carrying.total.{apfNative_u} X (@APFPaper5.K3.Carrying.represent.{apfNative_u} X g A) p n)
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @APFPaper5.K3.Carrying.open_total_can_be_presented_as_nothing_p2mProof
