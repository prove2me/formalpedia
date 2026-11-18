-- Prove2me | solution 1 for APFPaper5.K3.Connections.flip_connection
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:05:28.103254+00:00
-- url     : https://prove2.me/submissions/b65b894f-114f-4dae-bfb6-8d9752c08cd9

import Definitions.Def_APFPaper5_K3_free_number_on_each_connection_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not bundled, not built on the build machine)
name: APFPaper5_K3_free_number_on_each_connection
title: On a supplied table of real numbers over the alternatives, reading the alternatives one at a time fixes one number for each and leaves one free for each pair; that number is read by the sum and the difference of the pair; a change of sign of one alternative is not seen by the single reads; and for one mark the bill is the same all round the circle exactly when the connection carries no price, while a priced connection has one least-cost table
inputs_revision: 2026-11-14.1 (the occupant statement is NOT installed)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-16 07:31 HST: "Could the continuum circle  be related to the degrees of freedom
 represented by the possible connections of every continuation profile, a permutation of every
 distinctions potential alignment", and 07:36 HST: "Let's dig in and take a closer look - write it up too".
 Consulted before writing. Codebank apf/word_carrier_transfer.py ("carrier graph (vertex set X, edge set =
 available distinctions)"; the argmin transfer prices the diagonal); apf/carrier_elliptope.py ("word-priced
 data determines the diagonal ... and leaves the off-diagonal free"; "The free sector's dimension is
 n(n-1)/2 = |Pairs(X)|"; the missing lemma, localized, not proved); apf/counted_ledger_underdetermination.py
 (the counted ledger fixes only the diagonal; reading on three resolutions "is GIVEN the datum it
 recovers"); apf/one_context_one_transport.py (uniform frame cost, one global eps; survivors with zero
 diagonal); apf/core.py check_L_Pi and check_T_mode_partition_conservation (common mode and difference
 mode of a pair). Paper 1 Supplement v9.28:1803-1806 (the interface-coupling residue, bounded below and
 above), 3585, 3619-3622 (a coupled discriminator with nonadditive cost). This seat:
 Thm_APFPaper1_residue_is_a_count (pass 63), Thm_APFB06_worlds_against_the_occupant_statement (pass 64,
 three signs), Thm_APFPaper1_what_is_kept_depends_on_what_is_held (pass 69). None of these is imported.
standing: ORDINARY MATHEMATICS ON A SUPPLIED MODEL. A table of real numbers over the alternatives is
 supplied; nothing in the declared inputs produces one. The file does not say that a table is the cost of
 anything in a context, that its reads are chances, or that a combination of alternatives is a state.
consumes_inputs: none.
statement:
 For any finite list of alternatives and any table W of real numbers on ordered pairs of them:
 - (read_alt) the read of one alternative alone is its own entry.
 - (single_reads_agree_iff) two tables have the same single reads exactly when their own entries agree.
 - (bump_single_read, bump_connection, bump_ne, bump_symm) adding any number to one connection changes no
   single read, changes that connection by exactly that number, gives a different table when the number
   is not 0, and keeps a symmetric table symmetric.
 - (read_sum, read_difference) for a symmetric table, the read of two alternatives together is their two
   single reads plus twice the connection, and the read of their difference is the two less twice it.
 - (connection_from_sum_and_difference) so four times the connection is the read of the sum less the read
   of the difference.
 - (connection_is_half_the_surplus) and twice the connection is what the pair's read exceeds its two parts
   by.
 - (determined_by_singles_and_pairs) two symmetric tables with the same single reads and the same reads of
   every pair together are the same table.
 - (flip_single_read, flip_connection) a change of sign of some alternatives changes no single read, and
   turns over the connection between two alternatives of opposite sign.
 For one mark, with a place (u, v) on its circle, u*u + v*v = 1, and a cost table with eps on each side
 and k on the connection:
 - (bill_on_the_circle) the bill is eps + 2*k*(u*v).
 - (bill_flat_iff) the bill is the same at every place exactly when k = 0.
 - (count_valued_bill_is_flat) if eps > 0 and the bill at every place is a whole number of eps, then
   k = 0. (rational_place_on_the_circle, rational_place_connection_pos, rational_place_connection_le)
   it uses, for 0 < t < 1, the place ((1 - t*t)/(1 + t*t), 2*t/(1 + t*t)), whose connection is positive
   and at most 2*t.
 - (connection_bounds) u*v lies from -1/2 to 1/2.
 - (priced_bill_ge, priced_bill_eq_iff) for k > 0 the bill is at least eps - k, with equality exactly when
   u + v = 0. (priced_bill_ge_of_neg, priced_bill_eq_iff_of_neg) for k < 0 it is at least eps + k, with
   equality exactly when u = v.
 - (least_cost_table_unique) for k > 0, two places of least bill have the same table.
 - (counted_numbers_leave_a_sign) two places with the same counted numbers have the same connection or
   opposite ones. (same_counts_two_connections) and both happen: (3/5, 4/5) and (3/5, -4/5).
 - (connection_is_counted_a_turn_away, turned_place_on_the_circle) the connection is half the difference
   of the two counted numbers of the place read an eighth of a turn away, and those two numbers total 1.
 Helper statements: pair_alt_alt, pair_add_left, pair_add_right, pair_neg_left, pair_neg_right.
reading: on a supplied table, the single reads fix the alternatives and leave the connections; a
 connection is read only through combinations of its two alternatives; where the connection of a mark
 carries no price the whole circle bills alike, which is a tie, and where it carries a price there is one
 least-cost table; a bill that is a count of whole units cannot follow a priced connection round the
 circle.
not_claimed: that any context supplies a table; that the read of two alternatives together is the cost of
 holding two distinctions (connection_is_half_the_surplus carries that as the hypothesis hpair); that a
 place on a circle is a state; that the bill of a place is a cost in the sense of the declared inputs;
 that the count of connections is typed here as a dimension. No lane. No claim that the transfer is
 forced, that the carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Algebra.Order.Ring.Cast

set_option autoImplicit false

namespace APFPaper5.K3.Connections

open Finset

section Tables

variable {ι : Type*} [Fintype ι] [DecidableEq ι]









theorem pair_alt_alt_p2mProof (W : ι → ι → ℝ) (i j : ι) : pair W (alt i) (alt j) = W i j := by
  unfold pair alt
  simp [Finset.sum_ite_eq', mul_ite]

omit [DecidableEq ι] in
theorem pair_add_left_p2mProof (W : ι → ι → ℝ) (x y z : ι → ℝ) :
    pair W (fun a => x a + y a) z = pair W x z + pair W y z := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [DecidableEq ι] in
theorem pair_add_right_p2mProof (W : ι → ι → ℝ) (x y z : ι → ℝ) :
    pair W x (fun a => y a + z a) = pair W x y + pair W x z := by
  unfold pair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [DecidableEq ι] in
theorem pair_neg_left_p2mProof (W : ι → ι → ℝ) (x z : ι → ℝ) :
    pair W (fun a => -x a) z = -pair W x z := by
  unfold pair
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

omit [DecidableEq ι] in
theorem pair_neg_right_p2mProof (W : ι → ι → ℝ) (x z : ι → ℝ) :
    pair W x (fun a => -z a) = -pair W x z := by
  unfold pair
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- The read of one alternative alone is its own entry. -/
theorem read_alt_p2mProof (W : ι → ι → ℝ) (i : ι) : read W (alt i) = W i i :=
  pair_alt_alt_p2mProof W i i

/-- Two tables have the same single reads exactly when their own entries agree. -/
theorem single_reads_agree_iff_p2mProof (W W' : ι → ι → ℝ) :
    (∀ i, read W (alt i) = read W' (alt i)) ↔ ∀ i, W i i = W' i i := by
  constructor
  · intro h i
    have := h i
    rwa [read_alt_p2mProof, read_alt_p2mProof] at this
  · intro h i
    rw [read_alt_p2mProof, read_alt_p2mProof]
    exact h i



omit [Fintype ι] in
theorem bump_symm_p2mProof (W : ι → ι → ℝ) (hW : IsSymm W) (i j : ι) (t : ℝ) : IsSymm (bump W i j t) := by
  intro a b
  unfold bump
  rw [hW a b]
  have : ((a = i ∧ b = j) ∨ (a = j ∧ b = i)) ↔ ((b = i ∧ a = j) ∨ (b = j ∧ a = i)) := by
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inr ⟨h2, h1⟩
      · exact Or.inl ⟨h2, h1⟩
  simp only [this]

/-- Adding a number to one connection changes no single read. -/
theorem bump_single_read_p2mProof (W : ι → ι → ℝ) {i j : ι} (hij : i ≠ j) (t : ℝ) (k : ι) :
    read (bump W i j t) (alt k) = read W (alt k) := by
  rw [read_alt_p2mProof, read_alt_p2mProof]
  unfold bump
  have : ¬ ((k = i ∧ k = j) ∨ (k = j ∧ k = i)) := by
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact hij (h1.symm.trans h2)
    · exact hij (h2.symm.trans h1)
  simp [this]

omit [Fintype ι] in
/-- It changes that connection by exactly that number. -/
theorem bump_connection_p2mProof (W : ι → ι → ℝ) (i j : ι) (t : ℝ) : bump W i j t i j = W i j + t := by
  unfold bump
  simp

omit [Fintype ι] in
/-- And it gives a different table when the number is not 0. -/
theorem bump_ne_p2mProof (W : ι → ι → ℝ) (i j : ι) {t : ℝ} (ht : t ≠ 0) : bump W i j t ≠ W := by
  intro h
  have h1 := congrFun (congrFun h i) j
  rw [bump_connection_p2mProof] at h1
  exact ht (by linarith)

/-- For a symmetric table, the read of two alternatives together is their two single reads plus twice
the connection. -/
theorem read_sum_p2mProof (W : ι → ι → ℝ) (hW : IsSymm W) (i j : ι) :
    read W (fun a => alt i a + alt j a) = W i i + W j j + 2 * W i j := by
  unfold read
  rw [pair_add_left_p2mProof, pair_add_right_p2mProof, pair_add_right_p2mProof, pair_alt_alt_p2mProof, pair_alt_alt_p2mProof, pair_alt_alt_p2mProof,
    pair_alt_alt_p2mProof, hW j i]
  ring

/-- And the read of their difference is the two single reads less twice the connection. -/
theorem read_difference_p2mProof (W : ι → ι → ℝ) (hW : IsSymm W) (i j : ι) :
    read W (fun a => alt i a + -alt j a) = W i i + W j j - 2 * W i j := by
  unfold read
  rw [pair_add_left_p2mProof, pair_add_right_p2mProof, pair_add_right_p2mProof, pair_neg_left_p2mProof, pair_neg_left_p2mProof, pair_neg_right_p2mProof,
    pair_neg_right_p2mProof, pair_alt_alt_p2mProof, pair_alt_alt_p2mProof, pair_alt_alt_p2mProof, pair_alt_alt_p2mProof, hW j i]
  ring

/-- Four times the connection is the read of the sum less the read of the difference. -/
theorem connection_from_sum_and_difference_p2mProof (W : ι → ι → ℝ) (hW : IsSymm W) (i j : ι) :
    4 * W i j =
      read W (fun a => alt i a + alt j a) - read W (fun a => alt i a + -alt j a) := by
  rw [read_sum_p2mProof W hW, read_difference_p2mProof W hW]
  ring

/-- Twice the connection is what the pair's read exceeds its two parts by. `hpair` names the read of
the two together; nothing here says it is the cost of holding two distinctions. -/
theorem connection_is_half_the_surplus_p2mProof (W : ι → ι → ℝ) (hW : IsSymm W) (i j : ι) (together : ℝ)
    (hpair : read W (fun a => alt i a + alt j a) = together) :
    2 * W i j = together - read W (alt i) - read W (alt j) := by
  rw [← hpair, read_sum_p2mProof W hW, read_alt_p2mProof, read_alt_p2mProof]
  ring

/-- Two symmetric tables with the same single reads and the same reads of every pair together are the
same table. -/
theorem determined_by_singles_and_pairs_p2mProof (W W' : ι → ι → ℝ) (hW : IsSymm W) (hW' : IsSymm W')
    (h1 : ∀ i, read W (alt i) = read W' (alt i))
    (h2 : ∀ i j, i ≠ j →
      read W (fun a => alt i a + alt j a) = read W' (fun a => alt i a + alt j a)) :
    W = W' := by
  have hd : ∀ i, W i i = W' i i := (single_reads_agree_iff_p2mProof W W').mp h1
  funext i j
  by_cases hij : i = j
  · subst hij
    exact hd i
  · have := h2 i j hij
    rw [read_sum_p2mProof W hW, read_sum_p2mProof W' hW', hd i, hd j] at this
    linarith



/-- A change of sign changes no single read. -/
theorem flip_single_read_p2mProof (s : ι → ℝ) (hs : ∀ a, s a * s a = 1) (W : ι → ι → ℝ) (k : ι) :
    read (flip s W) (alt k) = read W (alt k) := by
  rw [read_alt_p2mProof, read_alt_p2mProof]
  unfold flip
  rw [hs k, one_mul]

omit [Fintype ι] [DecidableEq ι] in
/-- It turns over the connection between two alternatives of opposite sign. -/
theorem flip_connection_p2mProof (s : ι → ℝ) (W : ι → ι → ℝ) {i j : ι} (hi : s i = 1) (hj : s j = -1) :
    flip s W i j = -W i j := by
  unfold flip
  rw [hi, hj]
  ring

end Tables

section Mark



/-- On the circle the bill is `eps` plus twice the price of the connection times the connection. -/
theorem bill_on_the_circle_p2mProof (eps k : ℝ) {u v : ℝ} (h : u * u + v * v = 1) :
    bill eps k u v = eps + 2 * k * (u * v) := by
  unfold bill
  have : eps * (u * u) + eps * (v * v) = eps * (u * u + v * v) := by ring
  rw [this, h]
  ring

/-- The bill is the same at every place of the circle exactly when the connection carries no price. -/
theorem bill_flat_iff_p2mProof (eps k : ℝ) :
    (∀ u v : ℝ, u * u + v * v = 1 → bill eps k u v = eps) ↔ k = 0 := by
  constructor
  · intro h
    have h1 : ((3 : ℝ) / 5) * (3 / 5) + (4 / 5) * (4 / 5) = 1 := by norm_num
    have := h (3 / 5) (4 / 5) h1
    rw [bill_on_the_circle_p2mProof eps k h1] at this
    linarith
  · intro hk u v h
    rw [bill_on_the_circle_p2mProof eps k h, hk]
    ring

/-- The connection of a place on the circle lies from `-1/2` to `1/2`. -/
theorem connection_bounds_p2mProof {u v : ℝ} (h : u * u + v * v = 1) : -(1 / 2) ≤ u * v ∧ u * v ≤ 1 / 2 := by
  constructor
  · nlinarith [mul_self_nonneg (u + v)]
  · nlinarith [mul_self_nonneg (u - v)]

/-- With a positive price on the connection, the bill is at least `eps - k`. -/
theorem priced_bill_ge_p2mProof {eps k : ℝ} (hk : 0 < k) {u v : ℝ} (h : u * u + v * v = 1) :
    eps - k ≤ bill eps k u v := by
  rw [bill_on_the_circle_p2mProof eps k h]
  have := (connection_bounds_p2mProof h).1
  nlinarith

/-- With equality exactly at the places where `u + v = 0`. -/
theorem priced_bill_eq_iff_p2mProof {eps k : ℝ} (hk : 0 < k) {u v : ℝ} (h : u * u + v * v = 1) :
    bill eps k u v = eps - k ↔ u + v = 0 := by
  rw [bill_on_the_circle_p2mProof eps k h]
  constructor
  · intro hb
    have h1 : k * (2 * (u * v) + 1) = 0 := by linarith
    have h2 : 2 * (u * v) + 1 = 0 := by
      rcases mul_eq_zero.mp h1 with h0 | h0
      · exact absurd h0 (ne_of_gt hk)
      · exact h0
    have h3 : (u + v) * (u + v) = 0 := by nlinarith
    exact mul_self_eq_zero.mp h3
  · intro hs
    have hv : v = -u := by linarith
    subst hv
    have : u * u = 1 / 2 := by nlinarith
    nlinarith

/-- With a negative price on the connection, the bill is at least `eps + k`. -/
theorem priced_bill_ge_of_neg_p2mProof {eps k : ℝ} (hk : k < 0) {u v : ℝ} (h : u * u + v * v = 1) :
    eps + k ≤ bill eps k u v := by
  rw [bill_on_the_circle_p2mProof eps k h]
  have := (connection_bounds_p2mProof h).2
  nlinarith

/-- With equality exactly at the places where `u = v`. -/
theorem priced_bill_eq_iff_of_neg_p2mProof {eps k : ℝ} (hk : k < 0) {u v : ℝ} (h : u * u + v * v = 1) :
    bill eps k u v = eps + k ↔ u = v := by
  rw [bill_on_the_circle_p2mProof eps k h]
  constructor
  · intro hb
    have h1 : k * (2 * (u * v) - 1) = 0 := by linarith
    have h2 : 2 * (u * v) - 1 = 0 := by
      rcases mul_eq_zero.mp h1 with h0 | h0
      · exact absurd h0 (ne_of_lt hk)
      · exact h0
    have h3 : (u - v) * (u - v) = 0 := by nlinarith
    have := mul_self_eq_zero.mp h3
    linarith
  · intro hs
    subst hs
    have : u * u = 1 / 2 := by nlinarith
    nlinarith

/-- With a positive price on the connection, two places of least bill have the same table. -/
theorem least_cost_table_unique_p2mProof {eps k : ℝ} (hk : 0 < k) {u v u' v' : ℝ}
    (h : u * u + v * v = 1) (h' : u' * u' + v' * v' = 1)
    (hmin : bill eps k u v = eps - k) (hmin' : bill eps k u' v' = eps - k) :
    u * u = u' * u' ∧ v * v = v' * v' ∧ u * v = u' * v' := by
  have hs : u + v = 0 := (priced_bill_eq_iff_p2mProof hk h).mp hmin
  have hs' : u' + v' = 0 := (priced_bill_eq_iff_p2mProof hk h').mp hmin'
  have hv : v = -u := by linarith
  have hv' : v' = -u' := by linarith
  subst hv
  subst hv'
  have e : u * u = 1 / 2 := by nlinarith
  have e' : u' * u' = 1 / 2 := by nlinarith
  refine ⟨by rw [e, e'], ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- Two places with the same counted numbers have the same connection or opposite ones. -/
theorem counted_numbers_leave_a_sign_p2mProof {u v u' v' : ℝ} (hu : u * u = u' * u') (hv : v * v = v' * v') :
    u * v = u' * v' ∨ u * v = -(u' * v') := by
  have h : (u * v) * (u * v) = (u' * v') * (u' * v') := by
    have : (u * v) * (u * v) = (u * u) * (v * v) := by ring
    rw [this, hu, hv]
    ring
  have h2 : (u * v - u' * v') * (u * v + u' * v') = 0 := by nlinarith
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Both happen: two places on the circle with the same counted numbers and opposite connections. -/
theorem same_counts_two_connections_p2mProof :
    ((3 : ℝ) / 5) * (3 / 5) + (4 / 5) * (4 / 5) = 1 ∧
      ((3 : ℝ) / 5) * (3 / 5) + (-(4 / 5)) * (-(4 / 5)) = 1 ∧
      ((4 : ℝ) / 5) * (4 / 5) = (-(4 / 5)) * (-(4 / 5)) ∧
      ((3 : ℝ) / 5) * (4 / 5) ≠ (3 / 5) * (-(4 / 5)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The connection of a place is half the difference of its two counted numbers read an eighth of a
turn away, which are `(u + v)^2 / 2` and `(u - v)^2 / 2`. -/
theorem connection_is_counted_a_turn_away_p2mProof (u v : ℝ) :
    u * v = ((u + v) * (u + v) / 2 - (u - v) * (u - v) / 2) / 2 := by
  ring

/-- And those two numbers are the counted numbers of a place on the circle. -/
theorem turned_place_on_the_circle_p2mProof {u v : ℝ} (h : u * u + v * v = 1) :
    (u + v) * (u + v) / 2 + (u - v) * (u - v) / 2 = 1 := by
  nlinarith

/-- A place on the circle whose connection is small: for `0 < t < 1`, the place
`((1 - t*t)/(1 + t*t), 2*t/(1 + t*t))`. -/
theorem rational_place_on_the_circle_p2mProof (t : ℝ) :
    ((1 - t * t) / (1 + t * t)) * ((1 - t * t) / (1 + t * t)) +
      (2 * t / (1 + t * t)) * (2 * t / (1 + t * t)) = 1 := by
  have hd : (1 + t * t) ≠ 0 := ne_of_gt (by nlinarith [mul_self_nonneg t])
  field_simp
  ring

/-- Its connection is positive. -/
theorem rational_place_connection_pos_p2mProof {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < ((1 - t * t) / (1 + t * t)) * (2 * t / (1 + t * t)) := by
  have hd : 0 < 1 + t * t := by positivity
  have hn : 0 < 1 - t * t := by nlinarith
  positivity

/-- And at most `2 * t`. -/
theorem rational_place_connection_le_p2mProof {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    ((1 - t * t) / (1 + t * t)) * (2 * t / (1 + t * t)) ≤ 2 * t := by
  have hd : 0 < 1 + t * t := by positivity
  have hd1 : 1 ≤ 1 + t * t := by nlinarith [mul_self_nonneg t]
  have hn : 0 < 1 - t * t := by nlinarith
  have e : ((1 - t * t) / (1 + t * t)) * (2 * t / (1 + t * t)) =
      2 * t * ((1 - t * t) / ((1 + t * t) * (1 + t * t))) := by
    field_simp
  rw [e]
  have hfrac : (1 - t * t) / ((1 + t * t) * (1 + t * t)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [mul_self_nonneg t]
  nlinarith

/-- If the bill of every place on the circle is a whole number of `eps`, the connection carries no
price. -/
theorem count_valued_bill_is_flat_p2mProof {eps k : ℝ} (heps : 0 < eps)
    (h : ∀ u v : ℝ, u * u + v * v = 1 → ∃ m : ℤ, bill eps k u v = (m : ℝ) * eps) : k = 0 := by
  by_contra hk
  have ha : 0 < |k| := abs_pos.mpr hk
  have hden : 0 < 8 * (|k| + eps) := by positivity
  obtain ⟨t, ht0, ht1, hkt⟩ : ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 8 * |k| * t < eps := by
    refine ⟨eps / (8 * (|k| + eps)), div_pos heps hden, ?_, ?_⟩
    · rw [div_lt_one hden]; nlinarith
    · have : 8 * |k| * (eps / (8 * (|k| + eps))) = eps * (|k| / (|k| + eps)) := by
        field_simp
      rw [this]
      have hlt : |k| / (|k| + eps) < 1 := by
        rw [div_lt_one (by positivity)]; linarith
      nlinarith
  set u : ℝ := (1 - t * t) / (1 + t * t) with hu
  set v : ℝ := 2 * t / (1 + t * t) with hv
  have hcirc : u * u + v * v = 1 := rational_place_on_the_circle_p2mProof t
  have hpos : 0 < u * v := rational_place_connection_pos_p2mProof ht0 ht1
  have hle : u * v ≤ 2 * t := rational_place_connection_le_p2mProof ht0 ht1
  obtain ⟨m, hm⟩ := h u v hcirc
  rw [bill_on_the_circle_p2mProof eps k hcirc] at hm
  -- 2*k*(u*v) = (m - 1) * eps
  have hn : ((m - 1 : ℤ) : ℝ) * eps = 2 * k * (u * v) := by
    push_cast; linarith
  have habs : |((m - 1 : ℤ) : ℝ)| * eps = 2 * |k| * (u * v) := by
    have := congrArg abs hn
    rw [abs_mul, abs_of_pos heps, abs_mul, abs_mul, abs_of_pos hpos] at this
    rw [this]; norm_num
  have hsmall : |((m - 1 : ℤ) : ℝ)| * eps < eps := by
    rw [habs]; nlinarith
  have hlt1 : |((m - 1 : ℤ) : ℝ)| < 1 := by
    by_contra hge
    have hge' : 1 ≤ |((m - 1 : ℤ) : ℝ)| := not_lt.mp hge
    nlinarith
  have hz : m - 1 = 0 := by
    have : |(m - 1 : ℤ)| < 1 := by exact_mod_cast hlt1
    exact Int.abs_lt_one_iff.mp this
  have : 2 * |k| * (u * v) = 0 := by
    rw [← habs, hz]; simp
  have hprod : 0 < 2 * |k| * (u * v) := by positivity
  linarith

end Mark

end APFPaper5.K3.Connections


universe apfNative_u_1
theorem solution :
∀ {ι : Type apfNative_u_1} (s : ι → Real) (W : ι → ι → Real) {i j : ι}
  (hi : @Eq.{1} Real (s i) (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hj :
    @Eq.{1} Real (s j)
      (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))),
  @Eq.{1} Real (@APFPaper5.K3.Connections.flip.{apfNative_u_1} ι s W i j) (@Neg.neg.{0} Real Real.instNeg (W i j)) := by
  exact @APFPaper5.K3.Connections.flip_connection_p2mProof
