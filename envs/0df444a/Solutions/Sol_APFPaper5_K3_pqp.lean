-- Prove2me | solution 1 for APFPaper5.K3.pqp
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:23:34.541211+00:00
-- url     : https://prove2.me/submissions/eb1a16a3-2374-4373-9dde-314251ac98a5

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_two_mark_turn
title: In the two-mark model, changing the relation is a reversible turn
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoMarkModel.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model; h says the pair (u, v) has unit length.
statement: (markQ_idem) for a unit pair the turned mark is repeatable. (pqp) the number between the fixed mark
 and the turned mark is u * u. (turn_carries) the turn carries the fixed mark to the turned mark.
 (turn_inverse) for a unit pair the transpose undoes the turn. (turn_compose) turns compose to a turn.
 (half_turn_unseen) reversing the sign of the pair gives the same mark.
not_claimed: that any interface contains a turned mark; that a turn is an admissible process or loses nothing;
 that the number u * u is a score; any complex structure (two marks give the real case only); smoothness as a
 statement about a physical family (the dependence on u and v is polynomial in this model).
-/
import Definitions.Def_APFPaper5_K3_TwoMarkModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem markQ_idem (u v : ℝ) (h : u * u + v * v = 1) :
    mul (markQ u v) (markQ u v) = markQ u v := by
  have ha : u * u * (u * u) + u * v * (u * v) = u * u := by
    have e : u * u * (u * u) + u * v * (u * v) = u * u * (u * u + v * v) := by ring
    rw [e, h, mul_one]
  have hb : u * u * (u * v) + u * v * (v * v) = u * v := by
    have e : u * u * (u * v) + u * v * (v * v) = u * v * (u * u + v * v) := by ring
    rw [e, h, mul_one]
  have hc : u * v * (u * u) + v * v * (u * v) = u * v := by
    have e : u * v * (u * u) + v * v * (u * v) = u * v * (u * u + v * v) := by ring
    rw [e, h, mul_one]
  have hd : u * v * (u * v) + v * v * (v * v) = v * v := by
    have e : u * v * (u * v) + v * v * (v * v) = v * v * (u * u + v * v) := by ring
    rw [e, h, mul_one]
  exact M2.ext ha hb hc hd

theorem pqp (u v : ℝ) : mul (mul markP (markQ u v)) markP = smul (u * u) markP := by
  apply M2.ext <;> dsimp only [mul, smul, markP, markQ] <;> ring

theorem turn_carries (u v : ℝ) : mul (mul (turn u v) markP) (tr (turn u v)) = markQ u v := by
  apply M2.ext <;> dsimp only [mul, tr, turn, markP, markQ] <;> ring

theorem turn_inverse (u v : ℝ) (h : u * u + v * v = 1) : mul (turn u v) (tr (turn u v)) = one := by
  apply M2.ext <;> dsimp only [mul, tr, turn, one] <;> linarith [h]

theorem turn_compose (u v u' v' : ℝ) :
    mul (turn u v) (turn u' v') = turn (u * u' - v * v') (u * v' + v * u') := by
  apply M2.ext <;> dsimp only [mul, turn] <;> ring

theorem half_turn_unseen (u v : ℝ) : markQ (-u) (-v) = markQ u v := by
  apply M2.ext <;> dsimp only [markQ] <;> ring

end APFPaper5.K3


theorem solution :
∀ (u v : Real),
  @Eq.{1} APFPaper5.K3.M2
    (APFPaper5.K3.mul (APFPaper5.K3.mul APFPaper5.K3.markP (APFPaper5.K3.markQ u v)) APFPaper5.K3.markP)
    (APFPaper5.K3.smul (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) u u) APFPaper5.K3.markP) := by
  exact @APFPaper5.K3.pqp
