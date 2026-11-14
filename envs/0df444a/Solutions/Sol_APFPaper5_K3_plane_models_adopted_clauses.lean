-- Prove2me | solution 1 for APFPaper5.K3.plane_models_adopted_clauses
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:49:52.792204+00:00
-- url     : https://prove2.me/submissions/3181b6a1-2223-4a04-9b30-0e900108c6f7

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_exchange_test
title: The exchange of two marks by a turn does not follow from the adopted clauses: the plane satisfies them and has no such turn; one further clause would give it
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_TwoPoint; Thm_APFPaper5_K3_two_mark_continuity, _two_mark_cross_term,
 _two_mark_exchange.
consumes_inputs: none. The first two theorems are conditional on candidate clauses. The rest are statements
 about the supplied plane model.
open_hypothesis: hroot in plane_models_adopted_clauses only.
statement: (exchange_is_turn_of_twoPoint, exchange_has_half_of_twoPoint) if the score is symmetric and turns
 carry any pair of marks to any pair with the same score, every two marks are exchanged by an admissible turn;
 if turns also have halves, by a turn done twice.
 (plane_models_adopted_clauses) the plane satisfies the continuity hypothesis, and its turns leave cost and
 cross term unchanged. (plane_no_turn_exchanges_between) yet for the mark halfway between the two exclusive
 marks, no turn exchanges it with the fixed mark. (plane_fails_twoPoint) and the plane fails the two-point
 clause: a turn that fixes the fixed mark cannot carry a turned mark to its mirror image unless they commute.
 (mirror_pairs_same_scores) the two mirror-image pairs have the same score and the same costs.
 (third_mark_sees_handedness) a third mark scores differently against a turned mark and its mirror image, by
 2 * (u * v). So which side a mark lies on is not hidden once a third mark is present.
reading: the exchange of two marks by a turn is independent of the adopted clauses. The two-point clause is
 what would force it, and the plane fails that clause because it has a handedness.
-/
import Definitions.Def_APFPaper5_K3_TwoPoint
import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Theorems.Thm_APFPaper5_K3_turn_carries_mark
import Theorems.Thm_APFPaper5_K3_twoMark_continuity
import Theorems.Thm_APFPaper5_K3_strictly_between_iff_not_commute
import Theorems.Thm_APFPaper5_K3_pair_number_is_cross_term
import Theorems.Thm_APFPaper5_K3_sqCost_turn_invariant
import Theorems.Thm_APFPaper5_K3_crossTerm_turn_invariant
import Theorems.Thm_APFPaper5_K3_no_turn_exchanges
import Theorems.Thm_APFPaper5_K3_slant_pqp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

universe u

theorem exchange_is_turn_of_twoPoint {V : Type u} (Marks : Set V) (B : V → V → ℝ)
    (Adm : Set (V → V)) (hsymm : ∀ p q : V, B p q = B q p) (h : TwoPoint Marks B Adm)
    (p q : V) (hp : p ∈ Marks) (hq : q ∈ Marks) : ∃ T ∈ Adm, T p = q ∧ T q = p :=
  h p q q p hp hq hq hp (hsymm p q)

theorem exchange_has_half_of_twoPoint {V : Type u} (Marks : Set V) (B : V → V → ℝ)
    (Adm : Set (V → V)) (hsymm : ∀ p q : V, B p q = B q p) (h : TwoPoint Marks B Adm)
    (hh : TurnsHaveHalves Adm) (p q : V) (hp : p ∈ Marks) (hq : q ∈ Marks) :
    ∃ H ∈ Adm, H (H p) = q ∧ H (H q) = p := by
  obtain ⟨T, hT, hpq, hqp⟩ := exchange_is_turn_of_twoPoint Marks B Adm hsymm h p q hp hq
  obtain ⟨H, hH, hHH⟩ := hh T hT
  exact ⟨H, hH, by rw [hHH, hpq], by rw [hHH, hqp]⟩

theorem plane_models_adopted_clauses (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t) :
    Continuity relNumber 0 1 admTurns ∧
      (∀ (a b : ℝ) (x : M2), a * a + b * b = 1 →
        sqCost (mul (mul (turn a b) x) (tr (turn a b))) = sqCost x) ∧
      (∀ (a b : ℝ) (x y : M2), a * a + b * b = 1 →
        crossTerm (mul (mul (turn a b) x) (tr (turn a b)))
          (mul (mul (turn a b) y) (tr (turn a b))) = crossTerm x y) :=
  ⟨twoMark_continuity hroot, fun a b x h => sqCost_turn_invariant a b h x,
    fun a b x y h => crossTerm_turn_invariant a b h x y⟩

theorem plane_no_turn_exchanges_between (r : ℝ) (hr : 2 * (r * r) = 1) :
    ¬ ∃ a b : ℝ, mul (mul (turn a b) markP) (tr (turn a b)) = markQ r r ∧
      mul (mul (turn a b) (markQ r r)) (tr (turn a b)) = markP := by
  rintro ⟨a, b, h1, h2⟩
  have h := no_turn_exchanges a b r r h1 h2
  linarith

theorem plane_fails_twoPoint (a b u v : ℝ)
    (h1 : mul (mul (turn a b) markP) (tr (turn a b)) = markP)
    (h2 : mul (mul (turn a b) (markQ u v)) (tr (turn a b)) = markQ u (-v)) : u * v = 0 := by
  rw [turn_carries] at h1
  rw [turn_carries_mark] at h2
  have haa := congrArg M2.a h1
  have hbb := congrArg M2.d h1
  dsimp only [markQ, markP] at haa hbb
  have hb : b = 0 := mul_self_eq_zero.mp hbb
  rw [hb] at h2
  have hq := congrArg M2.b h2
  dsimp only [markQ] at hq
  have h3 : a * a * (u * v) = -(u * v) := by linarith
  rw [haa, one_mul] at h3
  linarith

theorem mirror_pairs_same_scores (u v : ℝ) :
    crossTerm markP (markQ u (-v)) = crossTerm markP (markQ u v) ∧
      sqCost (markQ u (-v)) = sqCost (markQ u v) := by
  constructor <;> dsimp only [crossTerm, sqCost, markP, markQ] <;> ring

theorem third_mark_sees_handedness (r u v : ℝ) (hr : 2 * (r * r) = 1) :
    crossTerm (markQ r r) (markQ u v) - crossTerm (markQ r r) (markQ u (-v)) = 2 * (u * v) := by
  have e : crossTerm (markQ r r) (markQ u v) - crossTerm (markQ r r) (markQ u (-v)) =
      2 * (r * r) * (2 * (u * v)) := by
    dsimp only [crossTerm, markQ]
    ring
  rw [e, hr, one_mul]

end APFPaper5.K3


theorem solution :
∀
  (hroot :
    ∀ (t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Exists.{1} Real fun (r : Real) =>
          @Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t),
  And
    (@APFPaper5.K3.Continuity.{0} APFPaper5.K3.UnitPair APFPaper5.K3.relNumber
      (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) APFPaper5.K3.admTurns)
    (And
      (∀ (a b : Real) (x : APFPaper5.K3.M2),
        @Eq.{1} Real
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a a)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b b))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
          @Eq.{1} Real
            (APFPaper5.K3.sqCost
              (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) x) (APFPaper5.K3.tr (APFPaper5.K3.turn a b))))
            (APFPaper5.K3.sqCost x))
      (∀ (a b : Real) (x y : APFPaper5.K3.M2),
        @Eq.{1} Real
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a a)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b b))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
          @Eq.{1} Real
            (APFPaper5.K3.crossTerm
              (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) x) (APFPaper5.K3.tr (APFPaper5.K3.turn a b)))
              (APFPaper5.K3.mul (APFPaper5.K3.mul (APFPaper5.K3.turn a b) y) (APFPaper5.K3.tr (APFPaper5.K3.turn a b))))
            (APFPaper5.K3.crossTerm x y))) := by
  exact @APFPaper5.K3.plane_models_adopted_clauses
