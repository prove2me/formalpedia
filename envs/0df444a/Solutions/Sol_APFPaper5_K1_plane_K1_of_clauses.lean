-- Prove2me | solution 1 for APFPaper5.K1.plane_K1_of_clauses
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:52:54.968174+00:00
-- url     : https://prove2.me/submissions/23318f24-5458-47b6-9e9c-e56a69fdb78c

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_plane_K1
title: In the plane of two marks, K1's typed conditions hold for the cross form of a cost that turns leave unchanged, that adds across exclusive directions, and that is positive on the unit mark
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Thm_APFPaper5_K1_plane_cost_quadratic and Def_APFPaper5_K1_CrossForm; Paper 5 Supplement
 v7.33:3037-3040 (K1); Def_APFPaper5_K1_OrderedScore.
consumes_inputs: none as a hypothesis. CONDITIONAL on hturn, horth, hnn and hc (the unit mark has positive
 cost), with the open pure-mathematics hypothesis hroot. Only hnn comes from the ledger by definition.
statement: (crossForm_eq) for a squared-length cost the cross form is q 1 0 times the sum of products of
 coefficients. (plane_cost_satisfies_K1) so it is bilinear with a faithful nonnegative diagonal, for the
 identity role exchange. (plane_K1_of_clauses) the same conclusion directly from the three clauses.
not_claimed: K1. This is a plane with two exclusive marks and the identity role exchange. The construction of
 the plane from ledger words, the action of turns on it, and any interface with more marks are not here.
-/
import Definitions.Def_APFPaper5_K1_CrossForm
import Definitions.Def_APFPaper5_K1_OrderedScore
import Theorems.Thm_APFPaper5_K1_plane_cost_quadratic
import Theorems.Thm_APFPaper5_K1_square_of_cross_term
import Mathlib.Algebra.Module.Pi

set_option autoImplicit false
namespace APFPaper5.K1

theorem crossForm_eq (q : ℝ → ℝ → ℝ) (hq : ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y))
    (x y : Bool → ℝ) :
    crossForm q x y = q 1 0 * (x true * y true + x false * y false) := by
  unfold crossForm
  rw [hq (x true + y true) (x false + y false), hq (x true) (x false), hq (y true) (y false)]
  ring

theorem plane_cost_satisfies_K1 (q : ℝ → ℝ → ℝ)
    (hq : ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y)) (hc : 0 < q 1 0) :
    IsBilinear (VP := Bool → ℝ) (VE := Bool → ℝ) (crossForm q) ∧
      FaithfulNonnegDiagonal (crossForm q) (LinearEquiv.refl ℝ (Bool → ℝ)) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro e e' p
    simp only [crossForm_eq q hq, Pi.add_apply]
    ring
  · intro r e p
    simp only [crossForm_eq q hq, Pi.smul_apply, smul_eq_mul]
    ring
  · intro e p p'
    simp only [crossForm_eq q hq, Pi.add_apply]
    ring
  · intro r e p
    simp only [crossForm_eq q hq, Pi.smul_apply, smul_eq_mul]
    ring
  · intro x
    rw [LinearEquiv.refl_apply, crossForm_eq q hq]
    exact mul_nonneg hc.le (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  · intro x hx
    rw [LinearEquiv.refl_apply, crossForm_eq q hq] at hx
    have hsum : x true * x true + x false * x false = 0 := by
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd h (ne_of_gt hc)
      · exact h
    have h1 : x true * x true = 0 := by
      linarith [mul_self_nonneg (x true), mul_self_nonneg (x false)]
    have h2 : x false * x false = 0 := by
      linarith [mul_self_nonneg (x true), mul_self_nonneg (x false)]
    funext b
    cases b
    · exact mul_self_eq_zero.mp h2
    · exact mul_self_eq_zero.mp h1

theorem plane_K1_of_clauses (q : ℝ → ℝ → ℝ)
    (hturn : ∀ a b x y : ℝ, a * a + b * b = 1 → q (a * x - b * y) (b * x + a * y) = q x y)
    (horth : ∀ x1 y1 x2 y2 : ℝ, x1 * x2 + y1 * y2 = 0 →
      q (x1 + x2) (y1 + y2) = q x1 y1 + q x2 y2)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (hc : 0 < q 1 0) :
    IsBilinear (VP := Bool → ℝ) (VE := Bool → ℝ) (crossForm q) ∧
      FaithfulNonnegDiagonal (crossForm q) (LinearEquiv.refl ℝ (Bool → ℝ)) :=
  plane_cost_satisfies_K1 q (plane_cost_quadratic q hturn horth hnn hroot) hc

end APFPaper5.K1


theorem solution :
∀ (q : Real → Real → Real)
  (hturn :
    ∀ (a b x y : Real),
      @Eq.{1} Real
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a a)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b b))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) →
        @Eq.{1} Real
          (q
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a x)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b y))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) b x)
              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) a y)))
          (q x y))
  (horth :
    ∀ (x1 y1 x2 y2 : Real),
      @Eq.{1} Real
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x1 x2)
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y1 y2))
          (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) →
        @Eq.{1} Real
          (q (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x1 x2)
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) y1 y2))
          (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (q x1 y1) (q x2 y2)))
  (hnn :
    ∀ (x y : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) (q x y))
  (hroot :
    ∀ (t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Exists.{1} Real fun (r : Real) =>
          And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
            (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t))
  (hc :
    @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
      (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))),
  And
    (@APFPaper5.K1.IsBilinear.{0, 0} (Bool → Real) (Bool → Real)
      (@Pi.addCommGroup.{0, 0} Bool (fun (a : Bool) => Real) fun (i : Bool) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} Bool Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{0, 0} Bool (fun (a : Bool) => Real) fun (i : Bool) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} Bool Real Real Real.semiring
        (@Semiring.toAddCommMonoid.{0} Real (@Ring.toSemiring.{0} Real Real.instRing))
        (@Semiring.toModule.{0} Real Real.semiring))
      (APFPaper5.K1.crossForm q))
    (@APFPaper5.K1.FaithfulNonnegDiagonal.{0, 0} (Bool → Real) (Bool → Real)
      (@Pi.addCommGroup.{0, 0} Bool (fun (a : Bool) => Real) fun (i : Bool) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} Bool Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (@Pi.addCommGroup.{0, 0} Bool (fun (a : Bool) => Real) fun (i : Bool) => Real.instAddCommGroup)
      (@Pi.Function.module.{0, 0, 0} Bool Real Real Real.semiring Real.instAddCommMonoid
        (@Semiring.toModule.{0} Real Real.semiring))
      (APFPaper5.K1.crossForm q)
      (@LinearEquiv.refl.{0, 0} Real (Bool → Real) Real.semiring
        (@Pi.addCommMonoid.{0, 0} Bool (fun (a : Bool) => Real) fun (i : Bool) => Real.instAddCommMonoid)
        (@Pi.Function.module.{0, 0, 0} Bool Real Real Real.semiring Real.instAddCommMonoid
          (@Semiring.toModule.{0} Real Real.semiring)))) := by
  exact @APFPaper5.K1.plane_K1_of_clauses
