-- Prove2me | solution 1 for APFPaper5.K1.at_the_eighth_turn_the_pair_number_squared_is_a_half
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-22T03:58:59.759334+00:00
-- url     : https://prove2.me/submissions/82bd8fa2-dbef-4ed7-aec4-829697828f0f

import Theorems.Thm_APFPaper5_K1_additive_nonneg_linear
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Definitions.Def_APFPaper5_K1_PairsAndNothingMore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Order.Ring.Abs
/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_plane_cost_quadratic
title: In the plane of two marks, a nonnegative cost that turns leave unchanged and that adds across unrelated directions is the squared length, and the number between two marks is then the square
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:271-350 (a faithful quadratic ledger and its polarization); the adopted
 continuity hypothesis (turns reach every relation; turns lose nothing); the record clause (cost adds across
 unrelated records). Thm_APFPaper5_K1_additive_nonneg_linear.
consumes_inputs: none as a hypothesis. CONDITIONAL on three clauses about a cost q on the plane:
 hturn (every turn leaves cost unchanged), horth (cost adds across perpendicular directions), hnn (cost is
 nonnegative). hnn is what the ledger's family cost gives by definition. hturn and horth are NOT inputs.
open_hypothesis: hroot, that every nonnegative real is a square with a nonnegative root. A fact of Mathlib
 (Real.sqrt) whose module is not built in the drafting workspace.
statement: (plane_cost_quadratic) under those clauses q x y = q 1 0 * (x * x + y * y).
 (cross_term_of_quadratic) then the cost of the fixed unit direction and the unit direction (u, v) held
 together exceeds the sum of their costs by 2 * q 1 0 * u. (square_of_cross_term) so the normalized cross
 term is u and its square is u * u, the pair number of the two-mark model.
not_claimed: that any interface satisfies hturn or horth; that the cost of a combination is defined on the
 ledger; any statement about more than two marks or about a complex structure. This is a conditional
 statement in a plane. It is not a claim that the probability rule is derived.
-/




set_option autoImplicit false
namespace APFPaper5.K1



theorem cross_term_of_quadratic (q : ℝ → ℝ → ℝ)
    (hq : ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y)) (u v : ℝ) :
    q (1 + u) (0 + v) - q 1 0 - q u v = 2 * q 1 0 * u := by
  rw [hq (1 + u) (0 + v), hq u v]
  ring



end APFPaper5.K1

/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-19; not
 gated, not reviewed, not released, not built on the build machine, in no bundle)
name: APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn
title: In the plane of two marks, a cost of pairs and nothing more that is two-homogeneous, never negative and unchanged by one quarter turn is the squared length
inputs_revision: 2026-11-20.2
restated: 2026-11-21 09:49 HST, for bundle v57, at the author's word of 09:43 HST, "yes", to this seat's question
 "Shall I build v57 as set out, yes or no?"
 (RULING_build_v57_with_the_headers_restated_to_2026-11-20.2_and_stage_the_run_2026-11-21; set out in
 TEE_UP_the_build_run_before_the_upload_bundle_v57_with_headers_restated_to_the_revision_in_force_2026-11-21).
 HEADER ONLY. Every line after this comment is the file as in bundle v56 (sha256
 3626770be8b4390323de20c180b99915ac161579af7223fe1f423dd81339cd98), kept in Old/ as
 Thm_APFPaper5_K1_plane_cost_from_pairs_and_one_quarter_turn_pre-restating_v57_2026-11-21.lean. No
 declaration is changed. THE RESTATED BYTES ARE NOT RELEASED.
 Changed in this header: the revision named on the inputs_revision line, which was 2026-11-18.3, and this
 entry. Nothing else.
 WHAT HAPPENED: since revision 2026-11-18.3, which this header named until now, one revision of
 FOUNDATION_INPUTS was installed. Revision 2026-11-20.2, installed 2026-11-20 at 12:36 HST (sha256
 05c831bf6e786f168d9a9f0bb366b496388bd049960e9df3ca0acad8680d6252;
 INSTALL_RECEIPT_FOUNDATION_INPUTS_2026-11-20.2_2026-11-20): B06 is reduced. After its first four sentences,
 which are unchanged, it now reads: "To draw a distinction is to keep its record: each distinction has one
 record, the same in every protocol, and a protocol draws the distinction exactly when it keeps that record.
 Every record a protocol keeps is the record of some tested distinction or family of tested distinctions,
 and is used for it. Every process pays epsilon for each record it keeps, and nothing else, where epsilon is
 positive and fixed by the context. In every context some protocol draws no distinction. The occupant draws
 exactly its family, and every part of that family is drawn alone by some protocol. A process that keeps no
 record costs nothing. A process that keeps no record changes nothing that is recorded." Against revision
 2026-11-18.3, six sentences are replaced by four and three are kept word for word. The six that are no
 longer sentences of the inputs: "Each record carries a cost. What a set of records is sufficient for does
 not depend on the protocol that keeps it. The occupant holds its distinctions with exactly the records they
 need, and its bill is the cost of those records. The same is true of every part of it: any family of its
 distinctions is held with exactly the records that family needs, at exactly their cost, and there is no
 cheaper way to hold that family. Epsilon is the unit of the occupant: each record it keeps costs epsilon,
 the floor of its context. Holding nothing costs nothing." B03 and B05 are retired as inputs and are kept in
 the inputs file as derived statements. B07a and B07b each gain a note, note_20261120_protocol_binding;
 their wording, scope and forms are unchanged. B01, B02 and B04 are unchanged. The commitments are six: B01,
 B02, B04, B06, B07a, B07b. The gate policy on the build machine is policy_revision 2026-11-20.inputs.1
 (sha256 5e9f3ec3cfa6c9a0a0b28549d13370c31ef78de38272ac6391efeac472f9a4aa) and requires this revision
 (INSTALL_RECEIPT_GATE_POLICY_2026-11-20.inputs.1_2026-11-20).
 HOW TO READ THE REST OF THIS HEADER: it named revision 2026-11-18.3 and is left as written, any earlier
 entries "restated" below included. Where it names revision 2026-11-18.3 or an earlier one as the revision
 in force, that is no longer so: the revision in force is 2026-11-20.2. Where it counts eight commitments,
 eight inputs or eight declared forms: there are now six commitments. The declared forms of B03 and B05 are
 unchanged and are now forms of derived statements. Where it calls B03 or B05 an input, or takes the
 declared form of either as a hypothesis: the installed file says of B03, and in the same words of B05, "A
 dependency on B03 is a dependency on its declared form, which is unchanged. From revision 2026-11-20.2 that
 form is a derived statement and not an input. The derivation is a draft and is not certified: until it is
 admitted through the gate, a node that consumes B03 is conditional on it. Resolve it before foundation
 certification. Do not treat an old use of B03 as a use of B06." Where it speaks of B06 by a count of its
 sentences or by their numbers, of the occupant statement, of the amended B06, or of a sentence of B06 as an
 input: that is B06 as it stood at the revision the header then named, and B06 now reads as quoted above. A
 statement here that takes one of the six replaced sentences as a premise stays true as a conditional;
 whether it follows from the reduced B06 is NOT SAID by this entry (for what used them see
 MEMO_pullbacks_passes119_and_120_what_used_the_dropped_sentences_and_one_world_for_all_eleven_2026-11-18 in
 Notes). Where it says of a sentence that is in B06 as quoted above that it is proposed, a ruling carried as
 a named hypothesis, NOT RULED, not installed or not an input: that is no longer so, for that sentence as
 worded above and for no typing of it. THE NEW SENTENCES OF B06 HAVE NO CERTIFIED LEAN FORM: the forms the
 inputs file names for the reduced B06 are drafts of the two seats, marked PROPOSED_NOT_CERTIFIED, and the
 Lean that derives the declared forms of B03 and B05 is a draft and is not gated. NOTHING in this entry says
 that a theorem of this file follows from the inputs at revision 2026-11-20.2, or that a supplied world of
 this file is a world of them: each theorem stands as before, on its named hypotheses or on its supplied
 world, and a supplied world that breaks a sentence of the inputs at revision 2026-11-20.2 is not a world of
 the inputs at that revision, whatever this header says of an earlier one. The gate policy says of the move
 to this revision: "immutable; dependency compatibility must be established separately; no stale-basis
 waiver". This entry establishes no such compatibility. Proposed revision 2026-11-20.3 (one further note on
 each of B07a and B07b) is NOT installed.
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-19 09:43 HST: "yes" (RULING_where_ways_that_keep_no_record_meet_what_is_counted_is_the_ways_one_at_a_time_and_two_at_a_time_2026-11-19).
 The build named in the tee-up of 09:26 HST, section 10, item 3. Def_APFPaper5_K1_PairsAndNothingMore.
 Consulted before typing (2026-11-19, 09:44 to 09:46 HST).
 - The builder seat's Thm_APFPaper5_K1_plane_cost_quadratic (2026-11-12): the same conclusion from three
   other clauses: every turn of the plane leaves the cost unchanged (hturn), the cost adds across
   perpendicular directions (horth), the cost is never negative; and from hroot, an open hypothesis there.
   Its cross_term_of_quadratic and square_of_cross_term take the conclusion as their hypothesis and are
   used here unchanged.
 - The builder seat's Thm_APFPaper5_K1_additive_nonneg_linear (2026-11-12), used here.
 - Paper 5 Supplement v7.33:246-298: a closed-ledger cost is never negative; "two-homogeneous";
   "parallelogram-complete"; the polarization theorem, cited there as Jordan and von Neumann.
 - The builder seat's TEE_UP_which_ways_meet_same_place_or_same_place_and_heading_2026-11-19, whole.
 - This seat's pass 144.
standing: CONDITIONAL. Ordinary real analysis on a supplied cost. Every hypothesis is a named clause and
 none is discharged from the declared inputs. No declared input is consumed.
 - hpairs is the author's ruling of 09:43 HST, as typed in Def_APFPaper5_K1_PairsAndNothingMore.
 - hhom (two-homogeneous) and hnn (never negative) are Paper 5's clauses. NOT ruled.
 - hquarter (one quarter turn of the plane leaves the cost unchanged) is NOT ruled. Paper 5's K3 lists
   "common-phase record-nullity" to be proved.
what this file says.
 1. additive_with_a_square_bound_is_linear. A function on the reals that adds, and is bounded by a
    multiple of (s squared and one), is a multiple of its argument.
 2. plane_cost_from_pairs_and_one_quarter_turn. Under the four clauses q x y = q 1 0 * (x * x + y * y).
    No turn other than the quarter turn is used. hroot is not used. Adding across perpendicular
    directions is not assumed.
 3. the_cost_adds_across_perpendicular_directions. Under the four clauses the builder seat's horth holds.
 4. every_turn_leaves_the_cost_unchanged. Under the four clauses the builder seat's hturn holds: the
    cost is unchanged by every turn of the plane, though only one quarter turn was assumed.
 5. cross_term_from_pairs_and_one_quarter_turn. Under the four clauses the cost of the unit direction
    and (u, v) together exceeds the sum of their costs by 2 * q 1 0 * u.
 6. at_the_eighth_turn_the_pair_number_squared_is_a_half. Under the four clauses, and the cost of the
    unit direction not nothing: for the direction (u, u) with u * u + u * u = 1, the builder seat's
    normalized cross term, squared, is a half.
 7. parallelogram_gives_pairs_and_nothing_more, pairs_and_reversal_unseen_give_the_parallelogram. On the
    plane, Paper 5's parallelogram clause gives the named clause; the named clause, with the cost of a
    reversed combination the same, gives the parallelogram clause.
 8. the_squared_length_is_such_a_cost. The four clauses can be met together.
 9. Controls. without_the_quarter_turn_the_cost_need_not_be_round: x * x + 2 * y * y meets the other
    three clauses. without_pairs_only_the_cost_need_not_be_round: x * x + y * y + |x * y| meets the
    other three clauses.
what this file does NOT say:
 - That the two remaining clauses, never negative and two-homogeneous, are each needed. No control is
   typed for either.
 - That the foundation's ways are the combinations of this plane, that a hold is the eighth turn of it,
   or that any of the four clauses holds of the ledger.
 - That the cost is a chance. No total is divided by.
 - Anything about more than two marks, a complex structure or two objects.
 - No lane. No claim that the transfer is forced, that the carrier gap is closed or narrowed, or that
   Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/





set_option autoImplicit false
namespace APFPaper5.K1

/-- A function on the reals that adds, and is bounded by a multiple of (s squared and one), is a multiple
of its argument. -/
theorem additive_with_a_square_bound_is_linear_p2mProof (φ : ℝ → ℝ) (K : ℝ)
    (hadd : ∀ s t : ℝ, φ (s + t) = φ s + φ t)
    (hb : ∀ s : ℝ, |φ s| ≤ K * (s * s + 1)) :
    ∀ s : ℝ, φ s = s * φ 1 := by
  have h0 : φ 0 = 0 := by
    have h := hadd 0 0
    rw [add_zero] at h
    linarith
  have hneg : ∀ s : ℝ, φ (-s) = - φ s := by
    intro s
    have h := hadd s (-s)
    rw [add_neg_cancel, h0] at h
    linarith
  have hK : 0 ≤ K := by
    have h := hb 0
    have h' := abs_nonneg (φ 0)
    nlinarith
  have hnat : ∀ (n : ℕ) (s : ℝ), φ ((n : ℝ) * s) = (n : ℝ) * φ s := by
    intro n s
    induction n with
    | zero =>
      rw [Nat.cast_zero, zero_mul, zero_mul]
      exact h0
    | succ k ih =>
      have e : ((k + 1 : ℕ) : ℝ) * s = (k : ℝ) * s + s := by
        rw [Nat.cast_succ]
        ring
      rw [e, hadd, ih, Nat.cast_succ]
      ring
  -- close to nothing the function is bounded by a multiple of its argument
  have hsmall : ∀ s : ℝ, 0 < s → s ≤ 1 → |φ s| ≤ 5 * K * s := by
    intro s hs hs1
    have hpos : 0 ≤ 1 / s := le_of_lt (one_div_pos.mpr hs)
    have hn1 : 1 / s ≤ ((⌈1 / s⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have hn2 : ((⌈1 / s⌉₊ : ℕ) : ℝ) < 1 / s + 1 := Nat.ceil_lt_add_one hpos
    generalize (⌈1 / s⌉₊ : ℕ) = n at hn1 hn2
    have e1 : 1 / s * s = 1 := by
      rw [one_div, inv_mul_cancel₀ (ne_of_gt hs)]
    have m1 : 1 ≤ (n : ℝ) * s := by
      have h := mul_le_mul_of_nonneg_right hn1 (le_of_lt hs)
      rw [e1] at h
      exact h
    have m2 : (n : ℝ) * s < 2 := by
      have h := mul_lt_mul_of_pos_right hn2 hs
      have e2 : (1 / s + 1) * s = 1 + s := by
        rw [add_mul, e1, one_mul]
      rw [e2] at h
      linarith
    have b1 := hb ((n : ℝ) * s)
    rw [hnat n s, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)] at b1
    have b2 : (n : ℝ) * |φ s| ≤ 5 * K := by
      have hsq : (n : ℝ) * s * ((n : ℝ) * s) ≤ 4 := by nlinarith
      nlinarith
    have a1 : 0 ≤ ((n : ℝ) * s - 1) * |φ s| := mul_nonneg (by linarith) (abs_nonneg _)
    have a2 : 0 ≤ (5 * K - (n : ℝ) * |φ s|) * s := mul_nonneg (by linarith) (le_of_lt hs)
    nlinarith
  -- so the function with that multiple added is never negative on what is not negative
  have hf01 : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → 0 ≤ φ s + 5 * K * s := by
    intro s hs hs1
    rcases eq_or_lt_of_le hs with h | h
    · rw [← h, h0]
      linarith
    · have hb' := hsmall s h hs1
      have := neg_abs_le (φ s)
      linarith
  have hfnn : ∀ s : ℝ, 0 ≤ s → 0 ≤ φ s + 5 * K * s := by
    intro s hs
    obtain ⟨n, hn⟩ := exists_nat_ge s
    have hm : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_succ]
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hsm : s ≤ ((n + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_succ]
      linarith
    generalize ((n + 1 : ℕ)) = m at hm hsm
    have ht0 : 0 ≤ s / (m : ℝ) := div_nonneg hs (le_of_lt hm)
    have ht1 : s / (m : ℝ) ≤ 1 := by
      rw [div_le_one hm]
      exact hsm
    have es : (m : ℝ) * (s / (m : ℝ)) = s := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self (ne_of_gt hm), mul_one]
    have h1 := hf01 (s / (m : ℝ)) ht0 ht1
    have h2 := hnat m (s / (m : ℝ))
    rw [es] at h2
    have h3 : φ s + 5 * K * s = (m : ℝ) * (φ (s / (m : ℝ)) + 5 * K * (s / (m : ℝ))) := by
      rw [h2, mul_add]
      have : (m : ℝ) * (5 * K * (s / (m : ℝ))) = 5 * K * ((m : ℝ) * (s / (m : ℝ))) := by ring
      rw [this, es]
    rw [h3]
    exact mul_nonneg (le_of_lt hm) h1
  have hlin := additive_nonneg_linear (fun s => φ s + 5 * K * s)
    (by
      intro s t _ _
      show φ (s + t) + 5 * K * (s + t) = φ s + 5 * K * s + (φ t + 5 * K * t)
      rw [hadd]
      ring)
    hfnn
  have hpos : ∀ s : ℝ, 0 ≤ s → φ s = s * φ 1 := by
    intro s hs
    have h := hlin s hs
    have h' : φ s + 5 * K * s = s * (φ 1 + 5 * K * 1) := h
    linarith
  intro s
  rcases le_total 0 s with hs | hs
  · exact hpos s hs
  · have h := hpos (-s) (by linarith)
    rw [hneg] at h
    linarith

/-- In the plane of two marks, a cost of pairs and nothing more that is two-homogeneous, never negative
and unchanged by one quarter turn is the squared length, times the cost of the unit direction. -/
theorem plane_cost_from_pairs_and_one_quarter_turn_p2mProof (q : ℝ → ℝ → ℝ)
    (hpairs : PairsAndNothingMore q)
    (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hquarter : ∀ x y : ℝ, q (-y) x = q x y) :
    ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y) := by
  have hx0 : ∀ x : ℝ, q x 0 = q 1 0 * (x * x) := by
    intro x
    have h := hhom x 1 0
    rw [mul_one, mul_zero] at h
    rw [h]
    ring
  have h01 : q 0 1 = q 1 0 := by
    have h := hquarter 1 0
    rw [neg_zero] at h
    exact h
  -- what the cost of (s, 1) holds beyond the squared length adds
  have hadd : ∀ s t : ℝ,
      q (s + t) 1 - q 1 0 * ((s + t) * (s + t)) - q 1 0 =
        (q s 1 - q 1 0 * (s * s) - q 1 0) + (q t 1 - q 1 0 * (t * t) - q 1 0) := by
    intro s t
    have h := hpairs s 0 t 0 0 1
    rw [add_zero, add_zero, add_zero, add_zero, zero_add, hx0 (s + t), hx0 s, hx0 t, h01] at h
    rw [h]
    ring
  have hφ0 : q 0 1 - q 1 0 * (0 * 0) - q 1 0 = 0 := by
    rw [h01]
    ring
  have hφneg : ∀ s : ℝ,
      q (-s) 1 - q 1 0 * (-s * -s) - q 1 0 = - (q s 1 - q 1 0 * (s * s) - q 1 0) := by
    intro s
    have h := hadd s (-s)
    rw [add_neg_cancel, hφ0] at h
    linarith
  have hc : 0 ≤ q 1 0 := hnn 1 0
  have hbound : ∀ s : ℝ, |q s 1 - q 1 0 * (s * s) - q 1 0| ≤ q 1 0 * (s * s + 1) := by
    intro s
    rw [abs_le]
    constructor
    · have h := hnn s 1
      nlinarith
    · have h := hnn (-s) 1
      have h' := hφneg s
      nlinarith
  have hlin := additive_with_a_square_bound_is_linear_p2mProof
    (fun s => q s 1 - q 1 0 * (s * s) - q 1 0) (q 1 0) hadd hbound
  -- at (1, 1) the quarter turn makes it nothing
  have h11 : q 1 1 - q 1 0 * (1 * 1) - q 1 0 = 0 := by
    have h := hquarter 1 1
    have h' := hφneg 1
    rw [h] at h'
    linarith
  have hs1 : ∀ s : ℝ, q s 1 = q 1 0 * (s * s + 1) := by
    intro s
    have h := hlin s
    have h' : q s 1 - q 1 0 * (s * s) - q 1 0 = s * (q 1 1 - q 1 0 * (1 * 1) - q 1 0) := h
    rw [h11] at h'
    linarith
  intro x y
  by_cases hy : y = 0
  · rw [hy, hx0 x]
    ring
  · have h := hhom y (x / y) 1
    have e : y * (x / y) = x := by
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hy, mul_one]
    rw [e, mul_one, hs1 (x / y)] at h
    rw [h]
    field_simp

/-- Under the four clauses the cost adds across perpendicular directions. -/
theorem the_cost_adds_across_perpendicular_directions_p2mProof (q : ℝ → ℝ → ℝ)
    (hpairs : PairsAndNothingMore q)
    (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hquarter : ∀ x y : ℝ, q (-y) x = q x y) :
    ∀ x1 y1 x2 y2 : ℝ, x1 * x2 + y1 * y2 = 0 →
      q (x1 + x2) (y1 + y2) = q x1 y1 + q x2 y2 := by
  have hq := plane_cost_from_pairs_and_one_quarter_turn_p2mProof q hpairs hhom hnn hquarter
  intro x1 y1 x2 y2 h
  rw [hq (x1 + x2) (y1 + y2), hq x1 y1, hq x2 y2]
  have e : (x1 + x2) * (x1 + x2) + (y1 + y2) * (y1 + y2) =
      x1 * x1 + y1 * y1 + (x2 * x2 + y2 * y2) + 2 * (x1 * x2 + y1 * y2) := by ring
  rw [e, h]
  ring

/-- Under the four clauses every turn of the plane leaves the cost unchanged. -/
theorem every_turn_leaves_the_cost_unchanged_p2mProof (q : ℝ → ℝ → ℝ)
    (hpairs : PairsAndNothingMore q)
    (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hquarter : ∀ x y : ℝ, q (-y) x = q x y) :
    ∀ a b x y : ℝ, a * a + b * b = 1 → q (a * x - b * y) (b * x + a * y) = q x y := by
  have hq := plane_cost_from_pairs_and_one_quarter_turn_p2mProof q hpairs hhom hnn hquarter
  intro a b x y h
  rw [hq (a * x - b * y) (b * x + a * y), hq x y]
  have e : (a * x - b * y) * (a * x - b * y) + (b * x + a * y) * (b * x + a * y) =
      (a * a + b * b) * (x * x + y * y) := by ring
  rw [e, h, one_mul]

/-- Under the four clauses the cost of the unit direction and (u, v) together exceeds the sum of their
costs by twice the cost of the unit direction times u. -/
theorem cross_term_from_pairs_and_one_quarter_turn_p2mProof (q : ℝ → ℝ → ℝ)
    (hpairs : PairsAndNothingMore q)
    (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hquarter : ∀ x y : ℝ, q (-y) x = q x y) (u v : ℝ) :
    q (1 + u) (0 + v) - q 1 0 - q u v = 2 * q 1 0 * u :=
  cross_term_of_quadratic q
    (plane_cost_from_pairs_and_one_quarter_turn_p2mProof q hpairs hhom hnn hquarter) u v

/-- Under the four clauses, for the direction an eighth of a turn from the unit direction, the pair
number squared is a half. The direction is (u, u) with u * u + u * u = 1; no square root is used. -/
theorem at_the_eighth_turn_the_pair_number_squared_is_a_half_p2mProof (q : ℝ → ℝ → ℝ)
    (hpairs : PairsAndNothingMore q)
    (hhom : ∀ t x y : ℝ, q (t * x) (t * y) = t * t * q x y)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hquarter : ∀ x y : ℝ, q (-y) x = q x y) (hc : q 1 0 ≠ 0) (u : ℝ)
    (hu : u * u + u * u = 1) :
    (q (1 + u) (0 + u) - q 1 0 - q u u) / (2 * q 1 0) *
      ((q (1 + u) (0 + u) - q 1 0 - q u u) / (2 * q 1 0)) = 1 / 2 := by
  rw [square_of_cross_term q
    (plane_cost_from_pairs_and_one_quarter_turn_p2mProof q hpairs hhom hnn hquarter) hc u u]
  linarith

/-- On the plane, Paper 5's parallelogram clause gives the named clause. -/
theorem parallelogram_gives_pairs_and_nothing_more_p2mProof (q : ℝ → ℝ → ℝ)
    (hP : ∀ x1 y1 x2 y2 : ℝ,
      q (x1 + x2) (y1 + y2) + q (x1 - x2) (y1 - y2) = 2 * q x1 y1 + 2 * q x2 y2) :
    PairsAndNothingMore q := by
  intro a1 a2 b1 b2 d1 d2
  have p1 := hP (a1 + b1) (a2 + b2) d1 d2
  have p2 := hP (a1 + d1) (a2 + d2) b1 b2
  have p3 := hP a1 a2 (b1 - d1) (b2 - d2)
  have p4 := hP b1 b2 d1 d2
  have e1 : a1 + d1 + b1 = a1 + b1 + d1 := by ring
  have e2 : a2 + d2 + b2 = a2 + b2 + d2 := by ring
  have e3 : a1 + d1 - b1 = a1 - (b1 - d1) := by ring
  have e4 : a2 + d2 - b2 = a2 - (b2 - d2) := by ring
  have e5 : a1 + (b1 - d1) = a1 + b1 - d1 := by ring
  have e6 : a2 + (b2 - d2) = a2 + b2 - d2 := by ring
  rw [e1, e2, e3, e4] at p2
  rw [e5, e6] at p3
  linarith

/-- On the plane, the named clause gives the parallelogram clause when the cost of a reversed combination
is the same. -/
theorem pairs_and_reversal_unseen_give_the_parallelogram_p2mProof (q : ℝ → ℝ → ℝ)
    (hpairs : PairsAndNothingMore q) (hrev : ∀ x y : ℝ, q (-x) (-y) = q x y) :
    ∀ x1 y1 x2 y2 : ℝ,
      q (x1 + x2) (y1 + y2) + q (x1 - x2) (y1 - y2) = 2 * q x1 y1 + 2 * q x2 y2 := by
  intro x1 y1 x2 y2
  have h00 : q 0 0 = 0 := by
    have h := hpairs 0 0 0 0 0 0
    rw [add_zero, add_zero] at h
    linarith
  have h := hpairs x1 y1 x2 y2 (-x2) (-y2)
  have e1 : x1 + x2 + -x2 = x1 := by ring
  have e2 : y1 + y2 + -y2 = y1 := by ring
  have e3 : x2 + -x2 = 0 := by ring
  have e4 : y2 + -y2 = 0 := by ring
  have e5 : x1 + -x2 = x1 - x2 := by ring
  have e6 : y1 + -y2 = y1 - y2 := by ring
  rw [e1, e2, e3, e4, e5, e6, h00, hrev x2 y2] at h
  linarith

/-- The four clauses can be met together: the squared length, times any number that is not negative,
meets all four. -/
theorem the_squared_length_is_such_a_cost_p2mProof (c : ℝ) (hc : 0 ≤ c) :
    PairsAndNothingMore (fun x y => c * (x * x + y * y)) ∧
      (∀ t x y : ℝ, c * (t * x * (t * x) + t * y * (t * y)) = t * t * (c * (x * x + y * y))) ∧
      (∀ x y : ℝ, 0 ≤ c * (x * x + y * y)) ∧
      (∀ x y : ℝ, c * (-y * -y + x * x) = c * (x * x + y * y)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a1 a2 b1 b2 d1 d2
    show c * ((a1 + b1 + d1) * (a1 + b1 + d1) + (a2 + b2 + d2) * (a2 + b2 + d2)) =
      c * ((a1 + b1) * (a1 + b1) + (a2 + b2) * (a2 + b2))
        + c * ((a1 + d1) * (a1 + d1) + (a2 + d2) * (a2 + d2))
        + c * ((b1 + d1) * (b1 + d1) + (b2 + d2) * (b2 + d2))
        - c * (a1 * a1 + a2 * a2) - c * (b1 * b1 + b2 * b2) - c * (d1 * d1 + d2 * d2)
    ring
  · intro t x y
    ring
  · intro x y
    exact mul_nonneg hc (by nlinarith [mul_self_nonneg x, mul_self_nonneg y])
  · intro x y
    ring

/-- A control. Without the quarter turn the cost need not be round: x * x + 2 * y * y is of pairs and
nothing more, two-homogeneous and never negative, and is not the squared length times its value at the
unit direction. -/
theorem without_the_quarter_turn_the_cost_need_not_be_round_p2mProof :
    PairsAndNothingMore (fun x y : ℝ => x * x + 2 * (y * y)) ∧
      (∀ t x y : ℝ, t * x * (t * x) + 2 * (t * y * (t * y)) = t * t * (x * x + 2 * (y * y))) ∧
      (∀ x y : ℝ, 0 ≤ x * x + 2 * (y * y)) ∧
      ((0 : ℝ) * 0 + 2 * (1 * 1) ≠ (1 * 1 + 2 * (0 * 0)) * (0 * 0 + 1 * 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a1 a2 b1 b2 d1 d2
    show (a1 + b1 + d1) * (a1 + b1 + d1) + 2 * ((a2 + b2 + d2) * (a2 + b2 + d2)) =
      (a1 + b1) * (a1 + b1) + 2 * ((a2 + b2) * (a2 + b2))
        + ((a1 + d1) * (a1 + d1) + 2 * ((a2 + d2) * (a2 + d2)))
        + ((b1 + d1) * (b1 + d1) + 2 * ((b2 + d2) * (b2 + d2)))
        - (a1 * a1 + 2 * (a2 * a2)) - (b1 * b1 + 2 * (b2 * b2)) - (d1 * d1 + 2 * (d2 * d2))
    ring
  · intro t x y
    ring
  · intro x y
    nlinarith [mul_self_nonneg x, mul_self_nonneg y]
  · norm_num

/-- A control. Without "pairs and nothing more" the cost need not be round: x * x + y * y + |x * y| is
two-homogeneous, never negative and unchanged by the quarter turn, and is not the squared length times
its value at the unit direction. -/
theorem without_pairs_only_the_cost_need_not_be_round_p2mProof :
    (∀ t x y : ℝ,
        t * x * (t * x) + t * y * (t * y) + |t * x * (t * y)| = t * t * (x * x + y * y + |x * y|)) ∧
      (∀ x y : ℝ, 0 ≤ x * x + y * y + |x * y|) ∧
      (∀ x y : ℝ, -y * -y + x * x + |-y * x| = x * x + y * y + |x * y|) ∧
      ((1 : ℝ) * 1 + 1 * 1 + |(1 : ℝ) * 1| ≠ (1 * 1 + 0 * 0 + |(1 : ℝ) * 0|) * (1 * 1 + 1 * 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t x y
    have e : t * x * (t * y) = t * t * (x * y) := by ring
    rw [e, abs_mul, abs_of_nonneg (mul_self_nonneg t)]
    ring
  · intro x y
    have := abs_nonneg (x * y)
    nlinarith [mul_self_nonneg x, mul_self_nonneg y]
  · intro x y
    have e : -y * x = -(x * y) := by ring
    rw [e, abs_neg]
    ring
  · norm_num

end APFPaper5.K1


theorem solution :
∀ (q : Real → Real → Real) (hpairs : APFPaper5.K1.PairsAndNothingMore q)
  (hhom :
    ∀ (t x y : Real),
      @Eq.{1} Real
        (q (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t x)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t y))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) t t) (q x y)))
  (hnn :
    ∀ (x y : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (q x y))
  (hquarter : ∀ (x y : Real), @Eq.{1} Real (q (@Neg.neg.{0} Real Real.instNeg y) x) (q x y))
  (hc :
    @Ne.{1} Real
      (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (u : Real)
  (hu :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Eq.{1} Real
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (q
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u))
            (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          (q u u))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))))
      (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (q
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) u)
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) u))
            (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
          (q u u))
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
          (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))))
    (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) := by
  exact @APFPaper5.K1.at_the_eighth_turn_the_pair_number_squared_is_a_half_p2mProof
