-- Prove2me | solution 1 for APFPaper5.K3.ThreeFourFive.returns_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-17T06:52:57.449336+00:00
-- url     : https://prove2.me/submissions/e6b5c6c6-e717-43fc-aea8-759eebc485d0

import Definitions.Def_APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over_Vocabulary
/-
APF Foundation Ledger — theorem node DRAFT (Claude seat, session EthanBrooke-01WrrBvv, 2026-11-16; not
 gated, not reviewed, not released, not built on the build machine)
name: APFPaper5_K3_the_345_turn_never_returns_and_never_turns_a_side_over
title: The 3-4-5 turn, repeated any number of times, never returns to where it began and never carries a side of a mark onto the other side; every number between two of its places is a ratio of whole numbers strictly between 0 and 1; its places are all different, so no finite set of states is a home for it; and every way of moving finitely many states that loses nothing returns
inputs_revision: 2026-11-14.1 (the occupant statement is NOT installed)
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: the author, 2026-11-16 08:55 HST: "Yes", to digging at option B (between two contexts). These
 are the two items TEE_UP_where_turns_between_could_come_from_2026-11-16 said this seat would type first
 (its observations 1 and 2).
 Consulted before writing. Paper 5 Supplement v7.33: 3505-3510 (from such a turn R the quarter turn is
 arithmetic, J = (25R + 7I)/24), 3551-3563 ("One exact infinite-order gate, a bounded normalized orbit,
 and effectivity close the effective holonomy image to the full circle"; "finite calibration certifies
 only a declared finite-resolution orbit cover"), 1954. Paper 1 Supplement v9.28: 4707-4719 (continuous
 outcomes "enter only through a directed family of finite resolutions"). Codebank:
 apf/two_exchange_holonomy.py and apf/two_exchange_roots.py (two exchanges with fixed lines at the 3-4-5
 angle; trace -14/25; nine named roots, not banked), apf/irrational_gate_holonomy.py
 (check_T_rational_trace_forces_infinite_order), apf/ijc_boolean_defender_bridge.py (the 3-4-5 angle "is
 an INPUT, not a derived value"), apf/admitted_presentation_family.py.
standing: ORDINARY MATHEMATICS. Whole-number arithmetic on (3 + 4i)^n and a counting fact about finite
 sets. No context, no cost and no declared input appears. The 3-4-5 angle is chosen, as it is in the
 codebank.
consumes_inputs: none.
statement:
 pw n is the pair of whole numbers (a, b) with (3 + 4i)^n = a + b i. The n-th place of the turn is
 (a / 5^n, b / 5^n): where n turns carry the point (1, 0).
 - (pw_mod) for n at least 1, a leaves 3 and b leaves 4 on division by 5.
 - (first_ne_zero, second_ne_zero) so neither is zero.
 - (norm_pw) a^2 + b^2 = 25^n.
 - (pw_add) the numbers of m + k turns are those of m turns and k turns multiplied as 3 + 4i is.
 - (never_returns) no n at least 1 has a = 5^n and b = 0: the turn repeated never does nothing.
 - (never_turns_a_side_over) no n at least 1 has a = 0: the turn repeated never carries a line onto the
   line square to it.
 - (number_strictly_between) for n at least 1, 0 < a^2 < 25^n: the number between a place and the place
   n turns on, a^2 / 25^n, is a ratio of whole numbers strictly between 0 and 1.
 - (overlap_of_two_places) the same holds between any two places: a_m a_(m+k) + b_m b_(m+k) = 25^m a_k.
 - (place_injective, places_infinite) the places are all different, and there are infinitely many.
 - (returns_of_finite) an injective map of a finite set into itself returns: some repeat of it, at
   least one, is the identity.
 - (no_finite_home) no finite set of states, moved by any map, has a state whose successive positions
   read off the successive places of the 3-4-5 turn.
reading: a family of contexts a 3-4-5 turn apart, each with one mark of two sides, has no end, and no
 two of them share a side or have a side that is the other's opposite. Every number between two of
 them is counted. The infinity sits in the family of contexts; each context can stay finite. This is
 Niven's theorem for one angle, by hand. The general statement is not typed.
not_claimed: that any context is a 3-4-5 turn from another; that the angle is derived; that a dense
 family is a continuum (it is not; that the places are dense is standard and not typed here); that the
 places are states of the foundation's data. No lane. No claim that the transfer is forced, that the
 carrier gap is closed or narrowed, or that Born is derived.
axioms: within propext, Classical.choice, Quot.sound. No sorry.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace APFPaper5.K3.ThreeFourFive



theorem pw_zero_fst : (pw 0).1 = 1 := rfl
theorem pw_zero_snd : (pw 0).2 = 0 := rfl
theorem pw_succ_fst (n : ℕ) : (pw (n + 1)).1 = 3 * (pw n).1 - 4 * (pw n).2 := rfl
theorem pw_succ_snd (n : ℕ) : (pw (n + 1)).2 = 4 * (pw n).1 + 3 * (pw n).2 := rfl

/-- After at least one turn the first number leaves 3 and the second leaves 4 on division by 5. -/
theorem pw_mod_p2mProof (n : ℕ) :
    ∃ k l : ℤ, (pw (n + 1)).1 = 3 + 5 * k ∧ (pw (n + 1)).2 = 4 + 5 * l := by
  induction n with
  | zero =>
    refine ⟨0, 0, ?_, ?_⟩
    · rw [pw_succ_fst, pw_zero_fst, pw_zero_snd]; norm_num
    · rw [pw_succ_snd, pw_zero_fst, pw_zero_snd]; norm_num
  | succ n ih =>
    obtain ⟨k, l, hk, hl⟩ := ih
    refine ⟨3 * k - 4 * l - 2, 4 * k + 3 * l + 4, ?_, ?_⟩
    · rw [pw_succ_fst, hk, hl]; ring
    · rw [pw_succ_snd, hk, hl]; ring

/-- The first number is never zero after at least one turn. -/
theorem first_ne_zero_p2mProof (n : ℕ) (hn : 1 ≤ n) : (pw n).1 ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨k, _, hk, _⟩ := pw_mod_p2mProof m
  omega

/-- The second number is never zero after at least one turn. -/
theorem second_ne_zero_p2mProof (n : ℕ) (hn : 1 ≤ n) : (pw n).2 ≠ 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨_, l, _, hl⟩ := pw_mod_p2mProof m
  omega

/-- The two numbers of `n` turns have squares adding to `25^n`. -/
theorem norm_pw_p2mProof (n : ℕ) : (pw n).1 ^ 2 + (pw n).2 ^ 2 = 25 ^ n := by
  induction n with
  | zero => rw [pw_zero_fst, pw_zero_snd]; norm_num
  | succ n ih =>
    have h : (25 : ℤ) ^ (n + 1) = 25 ^ n * 25 := pow_succ 25 n
    rw [pw_succ_fst, pw_succ_snd, h, ← ih]
    ring

/-- The numbers of `m + k` turns are those of `m` turns and of `k` turns, multiplied as `3 + 4i` is. -/
theorem pw_add_p2mProof (m k : ℕ) :
    (pw (m + k)).1 = (pw m).1 * (pw k).1 - (pw m).2 * (pw k).2 ∧
      (pw (m + k)).2 = (pw m).1 * (pw k).2 + (pw m).2 * (pw k).1 := by
  induction k with
  | zero =>
    constructor
    · rw [Nat.add_zero, pw_zero_fst, pw_zero_snd]; ring
    · rw [Nat.add_zero, pw_zero_fst, pw_zero_snd]; ring
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    constructor
    · rw [← Nat.add_assoc, pw_succ_fst, pw_succ_fst, pw_succ_snd, ih1, ih2]; ring
    · rw [← Nat.add_assoc, pw_succ_snd, pw_succ_fst, pw_succ_snd, ih1, ih2]; ring

/-- The turn repeated never does nothing. -/
theorem never_returns_p2mProof (n : ℕ) (hn : 1 ≤ n) : ¬ ((pw n).1 = 5 ^ n ∧ (pw n).2 = 0) :=
  fun h => second_ne_zero_p2mProof n hn h.2

/-- The turn repeated never carries a line onto the line square to it: it never turns a side over. -/
theorem never_turns_a_side_over_p2mProof (n : ℕ) (hn : 1 ≤ n) : (pw n).1 ≠ 0 := first_ne_zero_p2mProof n hn

/-- The number between a place and the place `n` turns on is `a^2 / 25^n`, a ratio of whole numbers
strictly between 0 and 1. -/
theorem number_strictly_between_p2mProof (n : ℕ) (hn : 1 ≤ n) :
    0 < (pw n).1 ^ 2 ∧ (pw n).1 ^ 2 < 25 ^ n := by
  have h3 := norm_pw_p2mProof n
  have h4 : 0 < (pw n).1 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (first_ne_zero_p2mProof n hn)))
  have h5 : 0 < (pw n).2 ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (second_ne_zero_p2mProof n hn)))
  exact ⟨h4, by linarith⟩

/-- The same between any two places: the overlap of the place `m` turns on and the place `m + k` turns on
is that of the start and the place `k` turns on. -/
theorem overlap_of_two_places_p2mProof (m k : ℕ) :
    (pw m).1 * (pw (m + k)).1 + (pw m).2 * (pw (m + k)).2 = 25 ^ m * (pw k).1 := by
  obtain ⟨h1, h2⟩ := pw_add_p2mProof m k
  rw [h1, h2, ← norm_pw_p2mProof m]
  ring

/-- If the place `m` turns on and the place `m + k` turns on coincide, then `k = 0`. -/
theorem same_place_only_at_the_same_count (m k : ℕ)
    (ha : (pw (m + k)).1 = (pw m).1 * 5 ^ k) (hb : (pw (m + k)).2 = (pw m).2 * 5 ^ k) : k = 0 := by
  by_contra hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
  obtain ⟨h1, h2⟩ := pw_add_p2mProof m k
  have e1 : (pw m).1 * (pw k).1 - (pw m).2 * (pw k).2 = (pw m).1 * 5 ^ k := by rw [← h1]; exact ha
  have e2 : (pw m).1 * (pw k).2 + (pw m).2 * (pw k).1 = (pw m).2 * 5 ^ k := by rw [← h2]; exact hb
  have e3 : ((pw m).1 ^ 2 + (pw m).2 ^ 2) * (pw k).2 = 0 := by
    linear_combination (pw m).1 * e2 - (pw m).2 * e1
  rw [norm_pw_p2mProof] at e3
  rcases mul_eq_zero.mp e3 with h | h
  · exact pow_ne_zero m (by norm_num) h
  · exact second_ne_zero_p2mProof k hk1 h



/-- A place and the place `k` turns further on coincide only when `k = 0`. -/
theorem place_eq_only_at_the_same_count (m k : ℕ) (h : place m = place (m + k)) : k = 0 := by
  have h5m : (5 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5k : (5 : ℚ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hA : ((pw m).1 : ℚ) / 5 ^ m = ((pw (m + k)).1 : ℚ) / 5 ^ (m + k) := congrArg Prod.fst h
  have hB : ((pw m).2 : ℚ) / 5 ^ m = ((pw (m + k)).2 : ℚ) / 5 ^ (m + k) := congrArg Prod.snd h
  rw [pow_add, div_eq_div_iff h5m (mul_ne_zero h5m h5k)] at hA hB
  have hA' : ((pw (m + k)).1 : ℚ) = (pw m).1 * 5 ^ k :=
    mul_right_cancel₀ h5m (by linear_combination -hA)
  have hB' : ((pw (m + k)).2 : ℚ) = (pw m).2 * 5 ^ k :=
    mul_right_cancel₀ h5m (by linear_combination -hB)
  exact same_place_only_at_the_same_count m k (by exact_mod_cast hA') (by exact_mod_cast hB')

/-- The places are all different. -/
theorem place_injective_p2mProof : Function.Injective place := by
  intro m n h
  rcases Nat.le_total m n with hmn | hnm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := place_eq_only_at_the_same_count m k h
    omega
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    have := place_eq_only_at_the_same_count n k h.symm
    omega

/-- There are infinitely many places. -/
theorem places_infinite_p2mProof : (Set.range place).Infinite :=
  Set.infinite_range_of_injective place_injective_p2mProof

/-- An injective map of a finite set into itself returns: some repeat of it, at least one, is the
identity. Every way of moving finitely many states that loses nothing comes back. -/
theorem returns_of_finite_p2mProof {S : Type*} [Finite S] (f : S → S) (hf : Function.Injective f) :
    ∃ n : ℕ, 1 ≤ n ∧ f^[n] = id := by
  have hnot : ¬ Function.Injective (fun n : ℕ => f^[n]) := not_injective_infinite_finite _
  have hex : ∃ m k : ℕ, 1 ≤ k ∧ f^[m] = f^[m + k] := by
    by_contra hcon
    apply hnot
    intro m n h
    have h' : f^[m] = f^[n] := h
    by_contra hmn
    rcases Nat.lt_or_gt_of_ne hmn with hlt | hgt
    · exact hcon ⟨m, n - m, by omega, by rw [show m + (n - m) = n by omega]; exact h'⟩
    · exact hcon ⟨n, m - n, by omega, by rw [show n + (m - n) = m by omega]; exact h'.symm⟩
  obtain ⟨m, k, hk, h⟩ := hex
  refine ⟨k, hk, ?_⟩
  funext s
  apply hf.iterate m
  have h2 := congrFun h s
  rw [Function.iterate_add_apply] at h2
  exact h2.symm

/-- No finite set of states, moved by any map, has a state whose successive positions read off the
successive places of the 3-4-5 turn. -/
theorem no_finite_home_p2mProof {S : Type*} [Finite S] (f : S → S) (s : S) (r : S → ℚ × ℚ)
    (hr : ∀ n : ℕ, r (f^[n] s) = place n) : False := by
  have hinj : Function.Injective (fun n : ℕ => f^[n] s) := by
    intro m n h
    apply place_injective_p2mProof
    rw [← hr m, ← hr n]
    exact congrArg r h
  exact not_injective_infinite_finite _ hinj

end APFPaper5.K3.ThreeFourFive


universe apfNative_u_1
theorem solution :
∀ {S : Type apfNative_u_1} [Finite.{apfNative_u_1 + 1} S] (f : S → S)
  (hf : @Function.Injective.{apfNative_u_1 + 1, apfNative_u_1 + 1} S S f),
  @Exists.{1} Nat fun (n : Nat) =>
    And (@LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n)
      (@Eq.{apfNative_u_1 + 1} (S → S) (@Nat.iterate.{apfNative_u_1 + 1} S f n) (@id.{apfNative_u_1 + 1} S)) := by
  exact @APFPaper5.K3.ThreeFourFive.returns_of_finite_p2mProof
