-- Prove2me | solution 1 for APFPaper5.K4.firstOrder_coturn_kills_other_sheet
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:47:04.759342+00:00
-- url     : https://prove2.me/submissions/0f2df9f9-1f9d-4f33-aa20-8f9a0d3c8f4f

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K4_two_sheets
title: If a quarter turn of each part is unseen, a joint carrier splits into two sheets with no cross term; the first-order clause for the turn of both parts leaves one
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K4_TwoSheets. The test announced in NOTE_derivation_pass_11_2026-11-13.
consumes_inputs: none. General statements about any carrier with two commuting quarter turns.
statement: J1 and J2 are the quarter turns of the two parts. A state is on the first sheet when J1 and J2
 agree on it, on the second when they are opposite.
 (no_cross_sheet_terms) a cross term of cost that is unchanged by J1 and by J2 vanishes between a state on
 the first sheet and a state on the second.
 (sync_part_is_sync, anti_part_is_anti, twice_is_sync_plus_anti) twice any state is a state on the first
 sheet plus a state on the second.
 (part_flip_sync_to_anti, part_flip_anti_to_sync) a map that anticommutes with J1 and commutes with J2, as
 the rate flip of the first part does, carries each sheet to the other.
 (firstOrder_coturn_kills_other_sheet) let T be additive, a turn on x and the identity on y, with no
 combination of x and T x on the line of y. If the first-order clause holds for T at x + y, then y = 0.
not_claimed: that the turn of both parts together is a turn to which the first-order clause applies at an
 interface; that all products lie on the same sheet; the composition clause; any K.
-/
import Definitions.Def_APFPaper5_K3_FirstOrder
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K4

universe u
variable {V : Type u} [AddCommGroup V]

theorem no_cross_sheet_terms (J1 J2 : V → V) (B : V → V → ℝ)
    (hB1 : ∀ x y : V, B (J1 x) (J1 y) = B x y) (hB2 : ∀ x y : V, B (J2 x) (J2 y) = B x y)
    (hneg : ∀ x y : V, B x (-y) = -(B x y)) (x y : V) (hx : J1 x = J2 x) (hy : J1 y = -(J2 y)) :
    B x y = 0 := by
  have e : B x y = -(B x y) := by
    calc B x y = B (J1 x) (J1 y) := (hB1 x y).symm
      _ = B (J2 x) (-(J2 y)) := by rw [hx, hy]
      _ = -(B (J2 x) (J2 y)) := hneg _ _
      _ = -(B x y) := by rw [hB2]
  linarith

theorem sync_part_is_sync (J1 J2 : V →+ V) (hsq1 : ∀ x : V, J1 (J1 x) = -x)
    (hsq2 : ∀ x : V, J2 (J2 x) = -x) (hcomm : ∀ x : V, J1 (J2 x) = J2 (J1 x)) (x : V) :
    J1 (x - J1 (J2 x)) = J2 (x - J1 (J2 x)) := by
  rw [map_sub, map_sub, hsq1, ← hcomm (J2 x), hsq2, map_neg]
  abel

theorem anti_part_is_anti (J1 J2 : V →+ V) (hsq1 : ∀ x : V, J1 (J1 x) = -x)
    (hsq2 : ∀ x : V, J2 (J2 x) = -x) (hcomm : ∀ x : V, J1 (J2 x) = J2 (J1 x)) (x : V) :
    J1 (x + J1 (J2 x)) = -(J2 (x + J1 (J2 x))) := by
  rw [map_add, map_add, hsq1, ← hcomm (J2 x), hsq2, map_neg]
  abel

theorem twice_is_sync_plus_anti (J1 J2 : V → V) (x : V) :
    (x - J1 (J2 x)) + (x + J1 (J2 x)) = x + x := by
  abel

theorem part_flip_sync_to_anti (J1 J2 F : V → V) (h1 : ∀ x : V, F (J1 x) = -(J1 (F x)))
    (h2 : ∀ x : V, F (J2 x) = J2 (F x)) (x : V) (hx : J1 x = J2 x) : J1 (F x) = -(J2 (F x)) := by
  have e := h1 x
  rw [hx, h2] at e
  rw [e, neg_neg]

theorem part_flip_anti_to_sync (J1 J2 F : V → V) (h1 : ∀ x : V, F (J1 x) = -(J1 (F x)))
    (h2 : ∀ x : V, F (J2 x) = J2 (F x)) (hFneg : ∀ x : V, F (-x) = -(F x)) (x : V)
    (hx : J1 x = -(J2 x)) : J1 (F x) = J2 (F x) := by
  have e := h1 x
  rw [hx, hFneg, h2] at e
  exact (neg_injective e).symm

theorem firstOrder_coturn_kills_other_sheet [Module ℝ V] (T : V → V)
    (hadd : ∀ a b : V, T (a + b) = T a + T b) (x y : V) (C : ℝ) (hC : C ≠ 1)
    (hx : T (T x) = (-1 : ℝ) • x + (2 * C) • T x) (hy : T y = y)
    (hind : ∀ a b c : ℝ, a • x + b • T x = c • y → a = 0 ∧ b = 0)
    (hfo : APFPaper5.K3.FirstOrder T (x + y)) : y = 0 := by
  obtain ⟨α, β, h⟩ := hfo
  rw [hadd x y, hy, hadd (T x) y, hy, hx] at h
  have key : (-1 - α) • x + (2 * C - β) • T x = (α + β - 1) • y := by
    rw [smul_add, smul_add] at h
    rw [sub_smul, sub_smul, sub_smul, add_smul, one_smul]
    have e2 : (-1 : ℝ) • x + (2 * C) • T x = α • x + α • y + (β • T x + β • y) - y :=
      eq_sub_of_add_eq h
    have e3 : (-1 : ℝ) • x - α • x + ((2 * C) • T x - β • T x) =
        ((-1 : ℝ) • x + (2 * C) • T x) - α • x - β • T x := by abel
    rw [e3, e2]
    abel
  obtain ⟨ha, hb⟩ := hind _ _ _ key
  have hα : α = -1 := by linarith
  have hβ : β = 2 * C := by linarith
  rw [ha, hb, zero_smul, zero_smul, add_zero, hα, hβ] at key
  have hr : (-1 + 2 * C - 1 : ℝ) ≠ 0 := by
    intro h0
    apply hC
    linarith
  calc y = (-1 + 2 * C - 1 : ℝ)⁻¹ • ((-1 + 2 * C - 1 : ℝ) • y) := by
        rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
    _ = (-1 + 2 * C - 1 : ℝ)⁻¹ • (0 : V) := by rw [← key]
    _ = 0 := smul_zero _

end APFPaper5.K4


universe apfNative_u
theorem solution :
∀ {V : Type apfNative_u} [inst : AddCommGroup.{apfNative_u} V]
  [inst_1 : @_root_.Module.{0, apfNative_u} Real V Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst)]
  (T : V → V)
  (hadd :
    ∀ (a b : V),
      @Eq.{apfNative_u + 1} V
        (T
          (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} V V V
            (@instHAdd.{apfNative_u} V
              (@AddCommMagma.toAdd.{apfNative_u} V
                (@AddCommSemigroup.toAddCommMagma.{apfNative_u} V
                  (@AddCommMonoid.toAddCommSemigroup.{apfNative_u} V
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst)))))
            a b))
        (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} V V V
          (@instHAdd.{apfNative_u} V
            (@AddCommMagma.toAdd.{apfNative_u} V
              (@AddCommSemigroup.toAddCommMagma.{apfNative_u} V
                (@AddCommMonoid.toAddCommSemigroup.{apfNative_u} V
                  (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst)))))
          (T a) (T b)))
  (x y : V) (C : Real) (hC : @Ne.{1} Real C (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne)))
  (hx :
    @Eq.{apfNative_u + 1} V (T (T x))
      (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} V V V
        (@instHAdd.{apfNative_u} V
          (@AddCommMagma.toAdd.{apfNative_u} V
            (@AddCommSemigroup.toAddCommMagma.{apfNative_u} V
              (@AddCommMonoid.toAddCommSemigroup.{apfNative_u} V
                (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst)))))
        (@HSMul.hSMul.{0, apfNative_u, apfNative_u} Real V V
          (@instHSMul.{0, apfNative_u} Real V
            (@SMulZeroClass.toSMul.{0, apfNative_u} Real V
              (@AddZero.toZero.{apfNative_u} V
                (@AddZeroClass.toAddZero.{apfNative_u} V
                  (@AddMonoid.toAddZeroClass.{apfNative_u} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))))
              (@DistribSMul.toSMulZeroClass.{0, apfNative_u} Real V
                (@AddMonoid.toAddZeroClass.{apfNative_u} V
                  (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))
                (@DistribMulAction.toDistribSMul.{0, apfNative_u} Real V Real.instMonoid
                  (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst)))
                  (@Module.toDistribMulAction.{0, apfNative_u} Real V Real.semiring
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst) inst_1)))))
          (@Neg.neg.{0} Real Real.instNeg (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))) x)
        (@HSMul.hSMul.{0, apfNative_u, apfNative_u} Real V V
          (@instHSMul.{0, apfNative_u} Real V
            (@SMulZeroClass.toSMul.{0, apfNative_u} Real V
              (@AddZero.toZero.{apfNative_u} V
                (@AddZeroClass.toAddZero.{apfNative_u} V
                  (@AddMonoid.toAddZeroClass.{apfNative_u} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))))
              (@DistribSMul.toSMulZeroClass.{0, apfNative_u} Real V
                (@AddMonoid.toAddZeroClass.{apfNative_u} V
                  (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))
                (@DistribMulAction.toDistribSMul.{0, apfNative_u} Real V Real.instMonoid
                  (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                    (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst)))
                  (@Module.toDistribMulAction.{0, apfNative_u} Real V Real.semiring
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst) inst_1)))))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
            C)
          (T x))))
  (hy : @Eq.{apfNative_u + 1} V (T y) y)
  (hind :
    ∀ (a b c : Real),
      @Eq.{apfNative_u + 1} V
          (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} V V V
            (@instHAdd.{apfNative_u} V
              (@AddCommMagma.toAdd.{apfNative_u} V
                (@AddCommSemigroup.toAddCommMagma.{apfNative_u} V
                  (@AddCommMonoid.toAddCommSemigroup.{apfNative_u} V
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst)))))
            (@HSMul.hSMul.{0, apfNative_u, apfNative_u} Real V V
              (@instHSMul.{0, apfNative_u} Real V
                (@SMulZeroClass.toSMul.{0, apfNative_u} Real V
                  (@AddZero.toZero.{apfNative_u} V
                    (@AddZeroClass.toAddZero.{apfNative_u} V
                      (@AddMonoid.toAddZeroClass.{apfNative_u} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))))
                  (@DistribSMul.toSMulZeroClass.{0, apfNative_u} Real V
                    (@AddMonoid.toAddZeroClass.{apfNative_u} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))
                    (@DistribMulAction.toDistribSMul.{0, apfNative_u} Real V Real.instMonoid
                      (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst)))
                      (@Module.toDistribMulAction.{0, apfNative_u} Real V Real.semiring
                        (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst) inst_1)))))
              a x)
            (@HSMul.hSMul.{0, apfNative_u, apfNative_u} Real V V
              (@instHSMul.{0, apfNative_u} Real V
                (@SMulZeroClass.toSMul.{0, apfNative_u} Real V
                  (@AddZero.toZero.{apfNative_u} V
                    (@AddZeroClass.toAddZero.{apfNative_u} V
                      (@AddMonoid.toAddZeroClass.{apfNative_u} V
                        (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                          (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))))
                  (@DistribSMul.toSMulZeroClass.{0, apfNative_u} Real V
                    (@AddMonoid.toAddZeroClass.{apfNative_u} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))
                    (@DistribMulAction.toDistribSMul.{0, apfNative_u} Real V Real.instMonoid
                      (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst)))
                      (@Module.toDistribMulAction.{0, apfNative_u} Real V Real.semiring
                        (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst) inst_1)))))
              b (T x)))
          (@HSMul.hSMul.{0, apfNative_u, apfNative_u} Real V V
            (@instHSMul.{0, apfNative_u} Real V
              (@SMulZeroClass.toSMul.{0, apfNative_u} Real V
                (@AddZero.toZero.{apfNative_u} V
                  (@AddZeroClass.toAddZero.{apfNative_u} V
                    (@AddMonoid.toAddZeroClass.{apfNative_u} V
                      (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                        (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))))
                (@DistribSMul.toSMulZeroClass.{0, apfNative_u} Real V
                  (@AddMonoid.toAddZeroClass.{apfNative_u} V
                    (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst))))
                  (@DistribMulAction.toDistribSMul.{0, apfNative_u} Real V Real.instMonoid
                    (@SubNegMonoid.toAddMonoid.{apfNative_u} V
                      (@AddGroup.toSubNegMonoid.{apfNative_u} V (@AddCommGroup.toAddGroup.{apfNative_u} V inst)))
                    (@Module.toDistribMulAction.{0, apfNative_u} Real V Real.semiring
                      (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst) inst_1)))))
            c y) →
        And (@Eq.{1} Real a (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)))
          (@Eq.{1} Real b (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))))
  (hfo :
    @APFPaper5.K3.FirstOrder.{apfNative_u} V inst inst_1 T
      (@HAdd.hAdd.{apfNative_u, apfNative_u, apfNative_u} V V V
        (@instHAdd.{apfNative_u} V
          (@AddCommMagma.toAdd.{apfNative_u} V
            (@AddCommSemigroup.toAddCommMagma.{apfNative_u} V
              (@AddCommMonoid.toAddCommSemigroup.{apfNative_u} V
                (@AddCommGroup.toAddCommMonoid.{apfNative_u} V inst)))))
        x y)),
  @Eq.{apfNative_u + 1} V y
    (@OfNat.ofNat.{apfNative_u} V (nat_lit 0)
      (@Zero.toOfNat0.{apfNative_u} V
        (@NegZeroClass.toZero.{apfNative_u} V
          (@SubNegZeroMonoid.toNegZeroClass.{apfNative_u} V
            (@SubtractionMonoid.toSubNegZeroMonoid.{apfNative_u} V
              (@SubtractionCommMonoid.toSubtractionMonoid.{apfNative_u} V
                (@AddCommGroup.toDivisionAddCommMonoid.{apfNative_u} V inst))))))) := by
  exact @APFPaper5.K4.firstOrder_coturn_kills_other_sheet
