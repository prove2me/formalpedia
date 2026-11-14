-- Prove2me | solution 1 for APFPaper5.K3.no_turn_exchanges
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:43:05.075987+00:00
-- url     : https://prove2.me/submissions/87790a2e-76ba-4d5b-928c-a1f3ac12c1db

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_two_mark_exchange
title: In the two-mark model the marks are exchanged by a mirror, by a turn only when they commute, and words alone do not bound the number
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Thm_APFPaper1_pair_number_symm and Def_APFPaper5_K3_TwoMarkExchange.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model.
statement: (qpq) read from the turned mark's side the number is again u * u. (mirror_carries_P,
 mirror_carries_Q, mirror_self_inverse) for a unit pair the mirror carries each mark to the other and undoes
 itself. (no_turn_exchanges) if a turn carries each mark to the other then u * v = 0, that is, the marks
 commute. (slantMark_idem, slant_pqp, slant_qpq) a slanted mark is repeatable and its number against the fixed
 mark is t from both sides, for every real t: the number is symmetric but need not lie from 0 to 1.
not_claimed: that the mirror is an admissible move; that exchange by a turn is required; anything about a
 third direction or a complex structure.
-/
import Definitions.Def_APFPaper5_K3_TwoMarkExchange
import Theorems.Thm_APFPaper5_K3_turn_carries_mark
import Theorems.Thm_APFPaper5_K3_twoMark_continuity
import Theorems.Thm_APFPaper5_K3_strictly_between_iff_not_commute
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem qpq (u v : ℝ) :
    mul (mul (markQ u v) markP) (markQ u v) = smul (u * u) (markQ u v) := by
  apply M2.ext <;> dsimp only [mul, smul, markP, markQ] <;> ring

theorem mirror_carries_P (u v : ℝ) :
    mul (mul (mirror u v) markP) (tr (mirror u v)) = markQ u v := by
  apply M2.ext <;> dsimp only [mul, tr, mirror, markP, markQ] <;> ring

theorem mirror_carries_Q (u v : ℝ) (h : u * u + v * v = 1) :
    mul (mul (mirror u v) (markQ u v)) (tr (mirror u v)) = markP := by
  have h2 : (u * u + v * v) * (u * u + v * v) = 1 := by rw [h, mul_one]
  apply M2.ext <;> dsimp only [mul, tr, mirror, markP, markQ] <;> linarith

theorem mirror_self_inverse (u v : ℝ) (h : u * u + v * v = 1) :
    mul (mirror u v) (mirror u v) = one := by
  apply M2.ext <;> dsimp only [mul, mirror, one] <;> linarith

theorem no_turn_exchanges (a b u v : ℝ)
    (h1 : mul (mul (turn a b) markP) (tr (turn a b)) = markQ u v)
    (h2 : mul (mul (turn a b) (markQ u v)) (tr (turn a b)) = markP) : u * v = 0 := by
  rw [turn_carries] at h1
  rw [turn_carries_mark] at h2
  have haa := congrArg M2.a h1
  have hab := congrArg M2.b h1
  have hd := congrArg M2.d h2
  dsimp only [markQ, markP] at haa hab hd
  have hz : b * u + a * v = 0 := mul_self_eq_zero.mp hd
  have h3 : a * b * u + a * a * v = 0 := by
    have e : a * b * u + a * a * v = a * (b * u + a * v) := by ring
    rw [e, hz, mul_zero]
  rw [hab, haa] at h3
  have h4 : u * (u * v) = 0 := by linarith
  rcases mul_eq_zero.mp h4 with hu | huv
  · rw [hu, zero_mul]
  · exact huv

theorem slantMark_idem (t : ℝ) : mul (slantMark t) (slantMark t) = slantMark t := by
  apply M2.ext <;> dsimp only [mul, slantMark] <;> ring

theorem slant_pqp (t : ℝ) : mul (mul markP (slantMark t)) markP = smul t markP := by
  apply M2.ext <;> dsimp only [mul, smul, markP, slantMark] <;> ring

theorem slant_qpq (t : ℝ) :
    mul (mul (slantMark t) markP) (slantMark t) = smul t (slantMark t) := by
  apply M2.ext <;> dsimp only [mul, smul, markP, slantMark] <;> ring

end APFPaper5.K3


theorem solution :
∀ (a b u v : Real)
  (h1 :
    @Eq.{1} APFPaper5.K3.M2
      (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) APFPaper5.K3.markP)
        (APFPaper5.K3.tr (APFPaper5.K3.turn a b)))
      (APFPaper5.K3.markQ u v))
  (h2 :
    @Eq.{1} APFPaper5.K3.M2
      (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) (APFPaper5.K3.markQ u v))
        (APFPaper5.K3.tr (APFPaper5.K3.turn a b)))
      APFPaper5.K3.markP),
  @Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u v)
    (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) := by
  exact @APFPaper5.K3.no_turn_exchanges
