-- Prove2me | solution 1 for APFPaper5.K1.plane_cost_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:42:14.544196+00:00
-- url     : https://prove2.me/submissions/e76f26ff-a356-40c3-bc9f-2194ad2f2048

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
import Theorems.Thm_APFPaper5_K1_additive_nonneg_linear
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false
namespace APFPaper5.K1

theorem plane_cost_quadratic (q : ℝ → ℝ → ℝ)
    (hturn : ∀ a b x y : ℝ, a * a + b * b = 1 → q (a * x - b * y) (b * x + a * y) = q x y)
    (horth : ∀ x1 y1 x2 y2 : ℝ, x1 * x2 + y1 * y2 = 0 →
      q (x1 + x2) (y1 + y2) = q x1 y1 + q x2 y2)
    (hnn : ∀ x y : ℝ, 0 ≤ q x y)
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t) :
    ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y) := by
  have hkey : ∀ x y m : ℝ, 0 ≤ m → m * m = x * x + y * y → q x y = q m 0 := by
    intro x y m _ hmm
    by_cases hm0 : m = 0
    · have hsum : x * x + y * y = 0 := by rw [← hmm, hm0, mul_zero]
      have hx2 : x * x = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
      have hy2 : y * y = 0 := by linarith [mul_self_nonneg x, mul_self_nonneg y]
      rw [mul_self_eq_zero.mp hx2, mul_self_eq_zero.mp hy2, hm0]
    · have hm0' : m ≠ 0 := hm0
      have hunit : x / m * (x / m) + y / m * (y / m) = 1 := by
        rw [div_mul_div_comm, div_mul_div_comm, ← add_div, ← hmm, div_self (mul_ne_zero hm0' hm0')]
      have h := hturn (x / m) (y / m) m 0 hunit
      have e1 : x / m * m - y / m * 0 = x := by
        field_simp
        ring
      have e2 : y / m * m + x / m * 0 = y := by
        field_simp
        ring
      rw [e1, e2] at h
      exact h
  choose! root hroot_nn hroot_sq using hroot
  have hF_add : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      q (root (s + t)) 0 = q (root s) 0 + q (root t) 0 := by
    intro s t hs ht
    have hst : 0 ≤ s + t := add_nonneg hs ht
    have h1 : q (root s) (root t) = q (root (s + t)) 0 :=
      hkey _ _ _ (hroot_nn _ hst) (by rw [hroot_sq _ hst, hroot_sq _ hs, hroot_sq _ ht])
    have h2 := horth (root s) 0 0 (root t) (by ring)
    rw [add_zero, zero_add] at h2
    have h3 : q 0 (root t) = q (root t) 0 := hkey 0 (root t) (root t) (hroot_nn _ ht) (by ring)
    rw [← h1, h2, h3]
  have hlin := additive_nonneg_linear (fun s => q (root s) 0) hF_add (fun s _ => hnn _ _)
  have hr1 : root 1 = 1 := by
    have h1 := hroot_sq 1 zero_le_one
    have h2 := hroot_nn 1 zero_le_one
    have h3 : (root 1 - 1) * (root 1 + 1) = root 1 * root 1 - 1 := by ring
    rw [h1, sub_self] at h3
    rcases mul_eq_zero.mp h3 with h | h
    · linarith
    · linarith
  intro x y
  have hs : 0 ≤ x * x + y * y := by linarith [mul_self_nonneg x, mul_self_nonneg y]
  have h1 := hkey x y (root (x * x + y * y)) (hroot_nn _ hs) (hroot_sq _ hs)
  have h2 := hlin (x * x + y * y) hs
  simp only [hr1] at h2
  rw [h1, h2]
  ring

theorem cross_term_of_quadratic (q : ℝ → ℝ → ℝ)
    (hq : ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y)) (u v : ℝ) :
    q (1 + u) (0 + v) - q 1 0 - q u v = 2 * q 1 0 * u := by
  rw [hq (1 + u) (0 + v), hq u v]
  ring

theorem square_of_cross_term (q : ℝ → ℝ → ℝ)
    (hq : ∀ x y : ℝ, q x y = q 1 0 * (x * x + y * y)) (hc : q 1 0 ≠ 0) (u v : ℝ) :
    (q (1 + u) (0 + v) - q 1 0 - q u v) / (2 * q 1 0) *
      ((q (1 + u) (0 + v) - q 1 0 - q u v) / (2 * q 1 0)) = u * u := by
  have h2 : (2 : ℝ) * q 1 0 ≠ 0 := mul_ne_zero two_ne_zero hc
  have hu : (q (1 + u) (0 + v) - q 1 0 - q u v) / (2 * q 1 0) = u := by
    rw [cross_term_of_quadratic q hq u v, mul_comm (2 * q 1 0) u, mul_div_assoc, div_self h2,
      mul_one]
  rw [hu]

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
  (x y : Real),
  @Eq.{1} Real (q x y)
    (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
      (q (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
        (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x x)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y y))) := by
  exact @APFPaper5.K1.plane_cost_quadratic
