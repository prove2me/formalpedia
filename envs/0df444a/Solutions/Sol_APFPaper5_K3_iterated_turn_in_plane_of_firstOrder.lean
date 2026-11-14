-- Prove2me | solution 1 for APFPaper5.K3.iterated_turn_in_plane_of_firstOrder
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:48:05.271779+00:00
-- url     : https://prove2.me/submissions/b7020818-3e42-4164-91a3-55d2640172c5

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-12; not gated, not reviewed)
name: APFPaper5_K3_exchange_needs_room
title: In the plane the exchange of two marks is a mirror with no half; in three dimensions it is a flip about an axis, which is the square of a quarter turn
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_ThreeDirections and Def_APFPaper5_K3_FirstOrder; Thm_APFPaper5_K3_two_mark_exchange
 (no_turn_exchanges); archive APFNativeG2.G2_06 (the exchange of a classical bit has no real square root).
consumes_inputs: none. CONDITIONAL INSTANCES in supplied models. A test of the bridge "the directions a mark
 can be turned in are the directions of space".
statement: plane: (det2_mul, det2_mirror, mirror_has_no_half) the mirror that exchanges two marks has
 determinant minus one, and no real array squares to it. (quarter_turn_has_half, quarter_turn_exchanges) the
 quarter turn does exchange the two exclusive marks and is the square of a turn.
 three dimensions: (quarter_quarter, quarter_quarter_unit) the quarter turn about a unit axis, done twice, is
 the flip about that axis. (quarter_dot, quarter_isometry) the quarter turn about a unit axis preserves dot
 products. (flip_exchanges) any two unit directions that are not opposite are exchanged by the flip about
 their sum.
 first order: (iterated_turn_in_plane_of_firstOrder) the plane theorem restated on the named clause.
reading: with turns having halves, exchanging two marks that are not exclusive is impossible by a turn in the
 plane and possible in three dimensions.
not_claimed: that space has three dimensions on the Foundation Ledger; that the directions a mark can be
 turned in are directions of space; that role exchange must be a turn; any complex structure.
-/
import Definitions.Def_APFPaper5_K3_ThreeDirections
import Definitions.Def_APFPaper5_K3_FirstOrder
import Theorems.Thm_APFPaper5_K3_no_turn_exchanges
import Theorems.Thm_APFPaper5_K3_slant_pqp
import Theorems.Thm_APFPaper5_K1_one_number_cannot_carry_value_and_rate
import Theorems.Thm_APFPaper5_K1_iterated_turn_in_plane
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3

theorem det2_mul (m n : M2) : det2 (mul m n) = det2 m * det2 n := by
  dsimp only [det2, mul]
  ring

theorem det2_mirror (u v : ℝ) : det2 (mirror u v) = -(u * u + v * v) := by
  dsimp only [det2, mirror]
  ring

theorem mirror_has_no_half (u v : ℝ) (h : u * u + v * v = 1) (m : M2) :
    mul m m ≠ mirror u v := by
  intro hm
  have hd := congrArg det2 hm
  rw [det2_mul, det2_mirror, h] at hd
  have hsq := mul_self_nonneg (det2 m)
  linarith

theorem quarter_turn_has_half (r : ℝ) (hr : 2 * (r * r) = 1) :
    mul (turn r r) (turn r r) = turn 0 1 := by
  have h1 : r * r - r * r = 0 := sub_self _
  have h2 : r * r + r * r = 1 := by linarith
  rw [turn_compose, h1, h2]

theorem quarter_turn_exchanges :
    mul (mul (turn 0 1) markP) (tr (turn 0 1)) = markQ 0 1 ∧
      mul (mul (turn 0 1) (markQ 0 1)) (tr (turn 0 1)) = markP := by
  constructor
  · exact turn_carries 0 1
  · apply M2.ext <;> dsimp only [mul, tr, turn, markP, markQ] <;> ring

theorem quarter_quarter (b v : V3) :
    quarterTurn b (quarterTurn b v) =
      add3 (sub3 (smul3 (2 * dot3 b v) b) v)
        (smul3 (dot3 b b - 1) (sub3 (smul3 (dot3 b v) b) v)) := by
  apply V3.ext <;> dsimp only [quarterTurn, add3, sub3, smul3, cross3, dot3] <;> ring

theorem quarter_quarter_unit (b v : V3) (hb : dot3 b b = 1) :
    quarterTurn b (quarterTurn b v) = flipAbout b v := by
  rw [quarter_quarter, hb, sub_self]
  apply V3.ext <;> dsimp only [flipAbout, add3, sub3, smul3] <;> rw [hb] <;> ring

theorem quarter_dot (b v w : V3) :
    dot3 (quarterTurn b v) (quarterTurn b w) =
      dot3 v w + (dot3 b b - 1) * (dot3 b v * dot3 b w + dot3 v w) := by
  dsimp only [quarterTurn, add3, smul3, cross3, dot3]
  ring

theorem quarter_isometry (b v w : V3) (hb : dot3 b b = 1) :
    dot3 (quarterTurn b v) (quarterTurn b w) = dot3 v w := by
  rw [quarter_dot, hb, sub_self, zero_mul, add_zero]

theorem flip_exchanges (m n : V3) (hm : dot3 m m = 1) (hn : dot3 n n = 1)
    (hne : dot3 (add3 m n) (add3 m n) ≠ 0) : flipAbout (add3 m n) m = n := by
  have h1 : 2 * dot3 (add3 m n) m = dot3 (add3 m n) (add3 m n) := by
    dsimp only [dot3, add3] at hm hn ⊢
    linarith
  have hcoef : 2 * dot3 (add3 m n) m / dot3 (add3 m n) (add3 m n) = 1 := by
    rw [h1]
    exact div_self hne
  unfold flipAbout
  rw [hcoef]
  apply V3.ext <;> dsimp only [sub3, smul3, add3] <;> ring

theorem iterated_turn_in_plane_of_firstOrder {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : V → V) (hTadd : ∀ a b : V, T (a + b) = T a + T b)
    (hTsmul : ∀ (r : ℝ) (a : V), T (r • a) = r • T a) (z : V) (h : FirstOrder T z) :
    ∀ n : ℕ, ∃ a b : ℝ, T^[n] z = a • z + b • T z := by
  obtain ⟨alpha, beta, hf⟩ := h
  exact APFPaper5.K1.iterated_turn_in_plane T hTadd hTsmul z alpha beta hf

end APFPaper5.K3


universe apfNative_u_1
theorem solution :
∀ {V : Type apfNative_u_1} [inst : AddCommGroup.{apfNative_u_1} V]
  [inst_1 :
    @_root_.Module.{0, apfNative_u_1} Real V Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)]
  (T : V → V)
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
  (z : V) (h : @APFPaper5.K3.FirstOrder.{apfNative_u_1} V inst inst_1 T z) (n : Nat),
  @Exists.{1} Real fun (a : Real) =>
    @Exists.{1} Real fun (b : Real) =>
      @Eq.{apfNative_u_1 + 1} V (@Nat.iterate.{apfNative_u_1 + 1} V T n z)
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
            a z)
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
            b (T z))) := by
  exact @APFPaper5.K3.iterated_turn_in_plane_of_firstOrder
