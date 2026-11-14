-- Prove2me | solution 1 for APFPaper5.K1.one_number_cannot_carry_value_and_rate
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:40:29.506099+00:00
-- url     : https://prove2.me/submissions/96ec0d3e-d5cb-4aa1-a259-4752700426b0

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_three_directions
title: One number cannot carry a relation's value and its rate, two can, and under the first-order clause every repeated turn of the difference stays in one plane
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:1621-1647, Theorem "Minimum complete bipolar first-jet carrier"
 (thm:q4-first-jet-rank-two): the minimum complete first-order lift is two-dimensional, with coordinates the
 present comparison and its continuation direction; and 1956, negative control "rank two is first-order
 minimality, not an assumed complex or Bloch plane". Codebank: check_T_bipolar_first_jet_rank_two,
 held_holonomy.py. Found on the author's instruction of 2026-11-12, "We derive three dimensions - find it".
consumes_inputs: none. The second theorem is CONDITIONAL on the first-order clause hfirst.
statement: (one_number_cannot_carry_value_and_rate) every linear reading a * x + b * y of a pair (value, rate)
 vanishes on some nonzero pair. So a one-number carrier is not faithful to first-order data, while the pair
 itself is. (iterated_turn_in_plane) let T be additive and homogeneous. If the second turn of z is a
 combination of z and its first turn, then every repeated turn of z is a combination of z and its first turn.
reading: with the total of the two exclusive marks, which a turn fixes, this gives exactly three directions for
 the space the turned marks span: the total, the difference, and the first turn of the difference.
not_claimed: the first-order clause itself. It is the Supplement's declared first-order regime. Three here
 counts the total and a plane; it is the real case.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1

theorem one_number_cannot_carry_value_and_rate (a b : ℝ) :
    ∃ x y : ℝ, (x ≠ 0 ∨ y ≠ 0) ∧ a * x + b * y = 0 := by
  by_cases h : a = 0 ∧ b = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    rw [h.1, h.2]
    ring
  · refine ⟨b, -a, ?_, by ring⟩
    by_contra hc
    have hc' := not_or.mp hc
    have hb : b = 0 := not_not.mp hc'.1
    have ha : -a = 0 := not_not.mp hc'.2
    exact h ⟨by linarith, hb⟩

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem iterated_turn_in_plane (T : V → V)
    (hTadd : ∀ a b : V, T (a + b) = T a + T b)
    (hTsmul : ∀ (r : ℝ) (a : V), T (r • a) = r • T a)
    (z : V) (alpha beta : ℝ) (hfirst : T (T z) = alpha • z + beta • T z) :
    ∀ n : ℕ, ∃ a b : ℝ, T^[n] z = a • z + b • T z := by
  intro n
  induction n with
  | zero =>
    refine ⟨1, 0, ?_⟩
    rw [Function.iterate_zero, id_eq, one_smul, zero_smul, add_zero]
  | succ k ih =>
    obtain ⟨a, b, hk⟩ := ih
    refine ⟨b * alpha, a + b * beta, ?_⟩
    rw [Function.iterate_succ_apply', hk, hTadd, hTsmul, hTsmul, hfirst, smul_add, smul_smul,
      smul_smul, add_smul]
    exact add_left_comm _ _ _

end APFPaper5.K1


theorem solution :
∀ (a b : Real),
  @Exists.{1} Real fun (x : Real) =>
    @Exists.{1} Real fun (y : Real) =>
      And
        (Or (@Ne.{1} Real x (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@Ne.{1} Real y (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
        (@Eq.{1} Real
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a x)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b y))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))) := by
  exact @APFPaper5.K1.one_number_cannot_carry_value_and_rate
