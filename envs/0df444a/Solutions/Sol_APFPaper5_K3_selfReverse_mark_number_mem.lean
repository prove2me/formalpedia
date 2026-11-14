-- Prove2me | solution 1 for APFPaper5.K3.selfReverse_mark_number_mem
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:26:14.686809+00:00
-- url     : https://prove2.me/submissions/9f9a3833-0ee8-4f04-a285-ba92f048f437

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_two_mark_range
title: In the two-mark model a repeatable array that is its own transpose has a number from 0 to 1, and a slanted mark is never its own transpose
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Thm_APFPaper1_pair_number_range and Def_APFPaper5_K3_TwoMarkExchange.
consumes_inputs: none. CONDITIONAL INSTANCE in a supplied model, with the transpose as the reversal.
statement: (selfReverse_mark_number) for any array q, the word fixed mark, q, fixed mark is q.a times the fixed
 mark. (selfReverse_mark_number_mem) if q is its own transpose and repeatable, then 0 ≤ q.a ≤ 1.
 (slantMark_not_selfReverse) no slanted mark is its own transpose.
-/
import Definitions.Def_APFPaper5_K3_TwoMarkExchange
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem selfReverse_mark_number (q : M2) : mul (mul markP q) markP = smul q.a markP := by
  apply M2.ext <;> dsimp only [mul, smul, markP] <;> ring

theorem selfReverse_mark_number_mem (q : M2) (hsym : tr q = q) (hidem : mul q q = q) :
    0 ≤ q.a ∧ q.a ≤ 1 := by
  have hc := congrArg M2.b hsym
  have ha := congrArg M2.a hidem
  dsimp only [tr, mul] at hc ha
  rw [hc] at ha
  have hb2 : 0 ≤ q.b * q.b := mul_self_nonneg q.b
  have ha2 : 0 ≤ q.a * q.a := mul_self_nonneg q.a
  have h0 : 0 ≤ q.a := by linarith
  refine ⟨h0, ?_⟩
  by_contra hgt
  have h1 : 1 < q.a := not_le.mp hgt
  have h3 := mul_pos (sub_pos.mpr h1) (lt_trans zero_lt_one h1)
  linarith

theorem slantMark_not_selfReverse (t : ℝ) : tr (slantMark t) ≠ slantMark t := by
  intro h
  have hb := congrArg M2.b h
  dsimp only [tr, slantMark] at hb
  have hs := mul_self_nonneg (t - 1 / 2)
  linarith

end APFPaper5.K3


theorem solution :
∀ (q : APFPaper5.K3.M2) (hsym : @Eq.{1} APFPaper5.K3.M2 (APFPaper5.K3.tr q) q)
  (hidem : @Eq.{1} APFPaper5.K3.M2 (APFPaper5.K3.mul q q) q),
  And
    (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (APFPaper5.K3.M2.a q))
    (@LE.le.{0} Real Real.instLE (APFPaper5.K3.M2.a q)
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) := by
  exact @APFPaper5.K3.selfReverse_mark_number_mem
