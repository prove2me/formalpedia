-- Prove2me | solution 1 for APFPaper5.K3.exists_amplitude_of_rotation
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:22:05.793207+00:00
-- url     : https://prove2.me/submissions/499bd59c-16e7-4a3a-921a-647b481554ee

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_amplitude_plane
title: Every rotation of the mark space is the double of a unit pair, pairs compose as turns do, and the number is the square of the pair's first entry
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_AmplitudePair; Thm_APFPaper5_K1_rank_three (a turn rotates the difference of two
 exclusive marks by a unit pair (x, y), and the number is (1 + x) / 2).
consumes_inputs: none. Pure arithmetic.
open_hypothesis: hroot, in exists_amplitude_of_rotation only (every nonnegative real is a square).
statement: (double_mul) doubling respects composition. (double_neg) a pair and its negative have the same
 double. (pairMul_unit, double_unit) unit pairs compose and double to unit pairs. (number_of_double) for a unit
 pair p with double (x, y), (1 + x) / 2 is p.1 * p.1 and (1 - x) / 2 is p.2 * p.2.
 (exists_amplitude_of_rotation) every unit pair (x, y) is the double of some unit pair.
reading: the plane of amplitude pairs is not an extra assumption once turns rotate the mark space. It is the
 square root of that rotation, fixed up to sign.
-/
import Definitions.Def_APFPaper5_K3_AmplitudePair
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3

theorem double_mul (p q : ℝ × ℝ) : double (pairMul p q) = pairMul (double p) (double q) := by
  apply Prod.ext <;> dsimp only [double, pairMul] <;> ring

theorem double_neg (p : ℝ × ℝ) : double (-p.1, -p.2) = double p := by
  apply Prod.ext <;> dsimp only [double, pairMul] <;> ring

theorem pairMul_unit (p q : ℝ × ℝ) (hp : p.1 * p.1 + p.2 * p.2 = 1)
    (hq : q.1 * q.1 + q.2 * q.2 = 1) :
    (pairMul p q).1 * (pairMul p q).1 + (pairMul p q).2 * (pairMul p q).2 = 1 := by
  have e : (pairMul p q).1 * (pairMul p q).1 + (pairMul p q).2 * (pairMul p q).2 =
      (p.1 * p.1 + p.2 * p.2) * (q.1 * q.1 + q.2 * q.2) := by
    dsimp only [pairMul]
    ring
  rw [e, hp, hq, mul_one]

theorem double_unit (p : ℝ × ℝ) (hp : p.1 * p.1 + p.2 * p.2 = 1) :
    (double p).1 * (double p).1 + (double p).2 * (double p).2 = 1 :=
  pairMul_unit p p hp hp

theorem number_of_double (p : ℝ × ℝ) (hp : p.1 * p.1 + p.2 * p.2 = 1) :
    (1 + (double p).1) / 2 = p.1 * p.1 ∧ (1 - (double p).1) / 2 = p.2 * p.2 := by
  dsimp only [double, pairMul]
  constructor <;> linarith

theorem exists_amplitude_of_rotation
    (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, 0 ≤ r ∧ r * r = t)
    (x y : ℝ) (hxy : x * x + y * y = 1) :
    ∃ p : ℝ × ℝ, p.1 * p.1 + p.2 * p.2 = 1 ∧ double p = (x, y) := by
  have hx1 : -1 ≤ x := by
    by_contra h
    have h1 : x < -1 := not_le.mp h
    have h2 := mul_pos (show (0 : ℝ) < -1 - x by linarith) (show (0 : ℝ) < 1 - x by linarith)
    linarith [mul_self_nonneg y]
  by_cases h0 : 1 + x = 0
  · have hx : x = -1 := by linarith
    have hy : y = 0 := by
      have hyy : y * y = 0 := by
        rw [hx] at hxy
        linarith
      exact mul_self_eq_zero.mp hyy
    refine ⟨(0, 1), by norm_num, ?_⟩
    rw [hx, hy]
    apply Prod.ext <;> dsimp only [double, pairMul] <;> norm_num
  · have hpos : 0 < 1 + x := lt_of_le_of_ne (by linarith) (Ne.symm h0)
    obtain ⟨u, _, hu2⟩ := hroot ((1 + x) / 2) (by linarith)
    have hune : u ≠ 0 := by
      intro hu
      rw [hu, mul_zero] at hu2
      linarith
    obtain ⟨v, huv⟩ : ∃ v : ℝ, 2 * u * v = y := ⟨y / (2 * u), by field_simp⟩
    have hyy : y * y = 4 * (u * u) * (v * v) := by
      rw [← huv]
      ring
    have hA : u * u * (1 - x) = (1 - x * x) / 2 := by
      rw [hu2]
      ring
    have h4 : u * u * (2 * (v * v) - (1 - x)) = 0 := by linarith
    have hv2 : 2 * (v * v) - (1 - x) = 0 :=
      (mul_eq_zero.mp h4).resolve_left (mul_ne_zero hune hune)
    refine ⟨(u, v), ?_, ?_⟩
    · show u * u + v * v = 1
      linarith
    · apply Prod.ext
      · show u * u - v * v = x
        linarith
      · show u * v + v * u = y
        linarith

end APFPaper5.K3


theorem solution :
∀
  (hroot :
    ∀ (t : Real),
      @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) t →
        @Exists.{1} Real fun (r : Real) =>
          And
            (@LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
            (@Eq.{1} Real (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) r r) t))
  (x y : Real)
  (hxy :
    @Eq.{1} Real
      (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x x)
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y y))
      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))),
  @Exists.{1} (Prod.{0, 0} Real Real) fun (p : Prod.{0, 0} Real Real) =>
    And
      (@Eq.{1} Real
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Prod.fst.{0, 0} Real Real p)
            (@Prod.fst.{0, 0} Real Real p))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) (@Prod.snd.{0, 0} Real Real p)
            (@Prod.snd.{0, 0} Real Real p)))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (@Eq.{1} (Prod.{0, 0} Real Real) (APFPaper5.K3.double p) (@Prod.mk.{0, 0} Real Real x y)) := by
  exact @APFPaper5.K3.exists_amplitude_of_rotation
