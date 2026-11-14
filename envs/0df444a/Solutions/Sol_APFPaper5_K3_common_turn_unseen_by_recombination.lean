-- Prove2me | solution 1 for APFPaper5.K3.common_turn_unseen_by_recombination
-- status  : ACCEPTED   (prove)
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:20:17.7161+00:00
-- url     : https://prove2.me/submissions/11048240-0ac6-4166-8e4e-fb15f4759af4

/-
APF Foundation Ledger — theorem node DRAFT (session EthanBrooke-01WrrBvu, 2026-11-13; not gated, not reviewed)
name: APFPaper5_K3_common_turn_unseen
title: A turn applied to both held components at once is unseen by every recombination record
inputs_revision: 2026-10-04.1
mathlib_rev: 0df444a360eaa60ab8c11dca51a86af692955474
source: as Def_APFPaper5_K3_Recombination. Paper 5 Supplement v7.33:1660-1680 (Reversible ledger isometry) and
 1808-1832 (Global-phase kernel theorem). Thm_APFPaper5_K1_turn_structure (turns are additive and
 homogeneous); Thm_APFPaper5_K3_preservation_cost (turns leave cost unchanged).
consumes_inputs: none. CONDITIONAL on T being additive, homogeneous and cost-preserving. Each of the three was
 obtained earlier from the adopted hypotheses: additivity and homogeneity from score preservation and losing
 nothing, cost preservation from the two preservation clauses.
statement: (common_turn_unseen_by_recombination) if T is additive and homogeneous and leaves cost unchanged,
 then for all weights the recombination record of T x and T y equals that of x and y.
reading: the Supplement's "only the diagonal common action is record-null", for records that are costs of
 recombinations. It is a consequence here, not an assumption.
not_claimed: that every record is the cost of a recombination; that a turn applied to one component alone is
 seen (that is shown in a model in Thm_APFPaper5_K3_two_components).
-/
import Definitions.Def_APFPaper5_K3_Recombination

set_option autoImplicit false
namespace APFPaper5.K3

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem common_turn_unseen_by_recombination (cost : V → ℝ) (T : V → V)
    (hTadd : ∀ x y : V, T (x + y) = T x + T y)
    (hTsmul : ∀ (r : ℝ) (x : V), T (r • x) = r • T x)
    (hcost : ∀ x : V, cost (T x) = cost x) (a b : ℝ) (x y : V) :
    recombinationRecord cost a b (T x) (T y) = recombinationRecord cost a b x y := by
  unfold recombinationRecord
  rw [← hTsmul a x, ← hTsmul b y, ← hTadd, hcost]

end APFPaper5.K3


universe apfNative_u_1
theorem solution :
∀ {V : Type apfNative_u_1} [inst : AddCommGroup.{apfNative_u_1} V]
  [inst_1 :
    @_root_.Module.{0, apfNative_u_1} Real V Real.semiring (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)]
  (cost : V → Real) (T : V → V)
  (hTadd :
    ∀ (x y : V),
      @Eq.{apfNative_u_1 + 1} V
        (T
          (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
            (@instHAdd.{apfNative_u_1} V
              (@AddCommMagma.toAdd.{apfNative_u_1} V
                (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                  (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                    (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
            x y))
        (@HAdd.hAdd.{apfNative_u_1, apfNative_u_1, apfNative_u_1} V V V
          (@instHAdd.{apfNative_u_1} V
            (@AddCommMagma.toAdd.{apfNative_u_1} V
              (@AddCommSemigroup.toAddCommMagma.{apfNative_u_1} V
                (@AddCommMonoid.toAddCommSemigroup.{apfNative_u_1} V
                  (@AddCommGroup.toAddCommMonoid.{apfNative_u_1} V inst)))))
          (T x) (T y)))
  (hTsmul :
    ∀ (r : Real) (x : V),
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
            r x))
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
          r (T x)))
  (hcost : ∀ (x : V), @Eq.{1} Real (cost (T x)) (cost x)) (a b : Real) (x y : V),
  @Eq.{1} Real (@APFPaper5.K3.recombinationRecord.{apfNative_u_1} V inst inst_1 cost a b (T x) (T y))
    (@APFPaper5.K3.recombinationRecord.{apfNative_u_1} V inst inst_1 cost a b x y) := by
  exact @APFPaper5.K3.common_turn_unseen_by_recombination
