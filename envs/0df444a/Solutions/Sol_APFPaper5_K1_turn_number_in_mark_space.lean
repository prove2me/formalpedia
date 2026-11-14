-- Prove2me | solution 1 for APFPaper5.K1.turn_number_in_mark_space
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:02:47.721148+00:00
-- url     : https://prove2.me/submissions/a70b0bfd-4831-4640-9485-2d049f3ea29e

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K1_rank_three
title: A mark strictly between two exclusive marks is not a combination of them, and in the three-direction mark space a turn rotates their difference
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: Paper 5 Supplement v7.33:40-52 (finite score rank; the symmetric part of the score as a ledger form)
 and 3037-3040 (K1); Def_APFPaper5_K1_OrderedScore (IsBilinear). The adopted continuity hypothesis.
consumes_inputs: none as a hypothesis. CONDITIONAL on a bilinear score B on a real space of combinations.
statement: (no_mark_between_in_rank_two) if a + b = 1 and a * a + b * b = 1 then a is 0 or 1.
 (no_mark_between_in_span) let p and p' be exclusive marks of unit self-score. If q is a combination of p and
 p' with unit self-score whose scores against p and p' add to 1, then its score against p is 0 or 1. So a
 mark strictly between needs a third direction.
 (turn_number_in_mark_space) let e, z, w be mutually exclusive directions of self-score 2, with e the total of
 two exclusive marks and z their difference. Let T be additive, homogeneous, score-preserving, fix e, and
 send z to alpha • e + x • z + y • w. Then alpha = 0, x * x + y * y = 1, the score between the mark
 (e + z) / 2 and its turn is (1 + x) / 2, and the score between the opposite mark and that turn is
 (1 - x) / 2.
not_claimed: that the score on combinations is bilinear, or that its diagonal is nonnegative; that the mark
 space has exactly three directions; that a turn fixes the total; that a turn acts additively.
-/
import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K1

theorem no_mark_between_in_rank_two (a b : ℝ) (hsum : a + b = 1) (hunit : a * a + b * b = 1) :
    a = 0 ∨ a = 1 := by
  have hb : b = 1 - a := by linarith
  rw [hb] at hunit
  have h : a * (a - 1) = 0 := by linarith
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by linarith)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem no_mark_between_in_span (B : V → V → ℝ) (hB : IsBilinear B) (p p' q : V) (a b : ℝ)
    (hpp : B p p = 1) (hp'p' : B p' p' = 1) (hpp' : B p p' = 0) (hp'p : B p' p = 0)
    (hq : q = a • p + b • p') (hqq : B q q = 1) (hnorm : B p q + B p' q = 1) :
    B p q = 0 ∨ B p q = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  have hpq : B p q = a := by
    rw [hq]
    simp only [h3, h4, hpp, hpp']
    ring
  have hp'q : B p' q = b := by
    rw [hq]
    simp only [h3, h4, hp'p, hp'p']
    ring
  have hexp : B q q = a * a + b * b := by
    rw [hq]
    simp only [h1, h2, h3, h4, hpp, hp'p', hpp', hp'p]
    ring
  rw [hexp] at hqq
  rw [hpq, hp'q] at hnorm
  rw [hpq]
  exact no_mark_between_in_rank_two a b hnorm hqq

theorem turn_number_in_mark_space (B : V → V → ℝ) (hB : IsBilinear B) (e z w : V) (T : V → V)
    (alpha x y : ℝ)
    (hee : B e e = 2) (hzz : B z z = 2) (hww : B w w = 2)
    (hez : B e z = 0) (hze : B z e = 0) (hew : B e w = 0) (hwe : B w e = 0)
    (hzw : B z w = 0) (hwz : B w z = 0)
    (hTadd : ∀ a b : V, T (a + b) = T a + T b)
    (hTsmul : ∀ (r : ℝ) (a : V), T (r • a) = r • T a)
    (hiso : ∀ a b : V, B (T a) (T b) = B a b) (hTe : T e = e)
    (hTz : T z = alpha • e + x • z + y • w) :
    alpha = 0 ∧ x * x + y * y = 1 ∧
      B ((1 / 2 : ℝ) • (e + z)) (T ((1 / 2 : ℝ) • (e + z))) = (1 + x) / 2 ∧
      B ((1 / 2 : ℝ) • (e + (-1 : ℝ) • z)) (T ((1 / 2 : ℝ) • (e + z))) = (1 - x) / 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  have hα : alpha = 0 := by
    have h := hiso z e
    rw [hTe, hTz] at h
    simp only [h1, h2, hee, hze, hwe] at h
    linarith
  have hunit : x * x + y * y = 1 := by
    have h := hiso z z
    rw [hTz, hα, zero_smul, zero_add] at h
    simp only [h1, h2, h3, h4, hzz, hww, hzw, hwz] at h
    linarith
  have hTp : T ((1 / 2 : ℝ) • (e + z)) = (1 / 2 : ℝ) • (e + (x • z + y • w)) := by
    rw [hTsmul, hTadd, hTe, hTz, hα, zero_smul, zero_add]
  refine ⟨hα, hunit, ?_, ?_⟩
  · rw [hTp]
    simp only [h1, h2, h3, h4, hee, hzz, hez, hze, hew, hzw]
    ring
  · rw [hTp]
    simp only [h1, h2, h3, h4, hee, hzz, hez, hze, hew, hzw]
    ring

end APFPaper5.K1


universe apfNative_u_1
theorem solution :
∀ {V : Type apfNative_u_1} [inst : AddCommGroup.{apfNative_u_1} V]
  [inst_1 :
    @_root_.Module.{0, apfNative_u_1} Real V Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)]
  (B : V → V → Real) (hB : @APFPaper5.K1.IsBilinear.{apfNative_u_1, apfNative_u_1} V V inst inst_1 inst inst_1 B)
  (e z w : V) (T : V → V) (alpha x y : Real)
  (hee :
    @Eq.{1} Real (B e e)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  (hzz :
    @Eq.{1} Real (B z z)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  (hww :
    @Eq.{1} Real (B w w)
      (@OfNat.ofNat.{0} Real (nat_lit 2)
        (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
  (hez : @Eq.{1} Real (B e z) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hze : @Eq.{1} Real (B z e) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hew : @Eq.{1} Real (B e w) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hwe : @Eq.{1} Real (B w e) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hzw : @Eq.{1} Real (B z w) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hwz : @Eq.{1} Real (B w z) (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
  (hTadd :
    ∀ (a b : V),
      @Eq.{apfNative_u_1 + 1} V
        (T
          (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
            (@instHAdd.{apfNative_u_1} V
              (@AddCommMagma.toAdd.{apfNative_u_1} V
                (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                  (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
            a b))
        (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
          (@instHAdd.{apfNative_u_1} V
            (@AddCommMagma.toAdd.{apfNative_u_1} V
              (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                  (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
          (T a) (T b)))
  (hTsmul :
    ∀ (r : Real) (a : V),
      @Eq.{apfNative_u_1 + 1} V
        (T
          (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
            (@instHSMul.{0, apfNative_u_1} Real V
              (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                (@AddZero.toZero.{apfNative_u_1} V
                  (@AddZeroClass.toAddZero.{apfNative_u_1} V
                    (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                          (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                  (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                  (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                    (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                      (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
            r a))
        (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
          (@instHSMul.{0, apfNative_u_1} Real V
            (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
              (@AddZero.toZero.{apfNative_u_1} V
                (@AddZeroClass.toAddZero.{apfNative_u_1} V
                  (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
              (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                  (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                  (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                  (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
          r (T a)))
  (hiso : ∀ (a b : V), @Eq.{1} Real (B (T a) (T b)) (B a b)) (hTe : @Eq.{apfNative_u_1 + 1} V (T e) e)
  (hTz :
    @Eq.{apfNative_u_1 + 1} V (T z)
      (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
        (@instHAdd.{apfNative_u_1} V
          (@AddCommMagma.toAdd.{apfNative_u_1} V
            (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
              (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
        (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
          (@instHAdd.{apfNative_u_1} V
            (@AddCommMagma.toAdd.{apfNative_u_1} V
              (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                  (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
          (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
            (@instHSMul.{0, apfNative_u_1} Real V
              (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                (@AddZero.toZero.{apfNative_u_1} V
                  (@AddZeroClass.toAddZero.{apfNative_u_1} V
                    (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                          (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                  (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                  (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                    (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                      (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
            alpha e)
          (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
            (@instHSMul.{0, apfNative_u_1} Real V
              (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                (@AddZero.toZero.{apfNative_u_1} V
                  (@AddZeroClass.toAddZero.{apfNative_u_1} V
                    (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                          (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                  (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                  (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                    (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                      (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
            x z))
        (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
          (@instHSMul.{0, apfNative_u_1} Real V
            (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
              (@AddZero.toZero.{apfNative_u_1} V
                (@AddZeroClass.toAddZero.{apfNative_u_1} V
                  (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
              (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                  (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                  (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                  (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
          y w))),
  And (@Eq.{1} Real alpha (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
    (And
      (@Eq.{1} Real
        (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) x x)
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul) y y))
        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
      (And
        (@Eq.{1} Real
          (B
            (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
              (@instHSMul.{0, apfNative_u_1} Real V
                (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                  (@AddZero.toZero.{apfNative_u_1} V
                    (@AddZeroClass.toAddZero.{apfNative_u_1} V
                      (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                  (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                    (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                    (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                      (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                      (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                        (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
                (@instHAdd.{apfNative_u_1} V
                  (@AddCommMagma.toAdd.{apfNative_u_1} V
                    (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                      (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                        (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
                e z))
            (T
              (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
                (@instHSMul.{0, apfNative_u_1} Real V
                  (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                    (@AddZero.toZero.{apfNative_u_1} V
                      (@AddZeroClass.toAddZero.{apfNative_u_1} V
                        (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                          (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                            (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                              (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                    (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                      (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                      (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                        (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                          (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
                  (@instHAdd.{apfNative_u_1} V
                    (@AddCommMagma.toAdd.{apfNative_u_1} V
                      (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                        (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                          (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
                  e z))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))))
        (@Eq.{1} Real
          (B
            (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
              (@instHSMul.{0, apfNative_u_1} Real V
                (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                  (@AddZero.toZero.{apfNative_u_1} V
                    (@AddZeroClass.toAddZero.{apfNative_u_1} V
                      (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                  (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                    (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                    (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                      (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u_1} V (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                      (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                        (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
              (@HDiv.hDiv.{0, 0, 0} Real Real Real
                (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
                (@instHAdd.{apfNative_u_1} V
                  (@AddCommMagma.toAdd.{apfNative_u_1} V
                    (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                      (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                        (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
                e
                (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
                  (@instHSMul.{0, apfNative_u_1} Real V
                    (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                      (@AddZero.toZero.{apfNative_u_1} V
                        (@AddZeroClass.toAddZero.{apfNative_u_1} V
                          (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                            (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                              (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                                (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                      (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                        (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                          (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                            (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                              (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                        (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                          (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                            (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                              (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                          (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                            (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
                  (@Neg.neg.{0} Real Real.instNeg
                    (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
                  z)))
            (T
              (@HSMul.hSMul.{0, apfNative_u_1, apfNative_u_1} Real V V
                (@instHSMul.{0, apfNative_u_1} Real V
                  (@SMulZeroClass.toSMul.{0, apfNative_u_1} Real V
                    (@AddZero.toZero.{apfNative_u_1} V
                      (@AddZeroClass.toAddZero.{apfNative_u_1} V
                        (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                          (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                            (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                              (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))))
                    (@DistribSMul.toSMulZeroClass.{0, apfNative_u_1} Real V
                      (@AddMonoid.toAddZeroClass.{apfNative_u_1} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst))))
                      (@DistribMulAction.toDistribSMul.{0, apfNative_u_1} Real V Real.instMonoid
                        (@SubNegMonoid.toAddMonoid.{apfNative_u_1} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u_1} V
                            (@AddCommGroup.toAddGroup.{apfNative_u_1} V inst)))
                        (@Module.toDistribMulAction.{0, apfNative_u_1} Real V Real.semiring
                          (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst) inst_1)))))
                (@HDiv.hDiv.{0, 0, 0} Real Real Real
                  (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                  (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
                  (@instHAdd.{apfNative_u_1} V
                    (@AddCommMagma.toAdd.{apfNative_u_1} V
                      (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                        (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                          (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
                  e z))))
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)) x)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))))) := by
  exact @APFPaper5.K1.turn_number_in_mark_space
