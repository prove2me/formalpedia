-- Prove2me | Definitions.Def_PandoraKnapsack_Skipping_SamplingRAM
-- name    : PandoraKnapsack_Skipping_SamplingRAM
-- status  : Definition
-- author  : @Jie Luo
-- created : 2026-11-25T17:43:30.956733+00:00
-- url     : https://prove2.me/theorems/81d14938-c1f3-5d35-84bb-b0903774546d
-- title:
--   Uniform categorical sampling and sorted policy emission on the costed machine
-- statement:
--   A row scan uses one uniform draw per item to select its choice and dyadic time. A second scan emits triples in increasing time and then increasing item order, with threshold equal to capacity minus the assigned time.
-- source:
--   Barak, Berlin, Cohen, Eden, Porat and Talgam-Cohen, Pandora’s Knapsack via Simple Policies, arXiv:2509.05956v5, https://arxiv.org/html/2509.05956v5#S5.SS1, explicit implementation of Algorithm 1 and the polynomial-time clause of Theorem 5.1 under the machine model in Prove2Me theorem 7898d376-37b2-42fd-8375-13696ef594ef. Derived implementation for the dyadic approximate solver.

import Definitions.Def_PandoraKnapsack_Skipping_ArrayRAM
import Definitions.Def_PandoraKnapsack_Skipping_DyadicPlan
import Definitions.Def_PandoraKnapsack_Skipping_UniformAssignment

namespace PandoraKnapsack.Skipping.ArrayRAM

theorem samplingLabel_le {T : ℕ} (k : Fin (labelCount T)) : timeLabel k ≤ T := by
  unfold timeLabel
  split_ifs with hk
  · omega
  · have h := k.isLt
    unfold labelCount at h
    split_ifs at h with hz
    · omega
    · exact (Nat.pow_le_pow_right (by decide : 0 < 2) (show k.val-1 ≤ Nat.log 2 T by omega)).trans
        (Nat.pow_log_le_self 2 hz)


/-- Categorical labels in the same order as the nested choice/time scan. -/
def samplingLab (m T : ℕ) (c : Fin (m * labelCount T)) : Fin m × Fin (T+1) :=
  let jh := finProdFinEquiv.symm c
  (jh.1, ⟨timeLabel jh.2, Nat.lt_succ_of_le (samplingLabel_le jh.2)⟩)

/-- Column address in the time-fastest order of `columns`. -/
def sampleColumn : N := (.var 45 * .var 1 + .var 46) * .var 2 + .var 47

/-- Visit one choice-time column. The left edge is inclusive and the right edge exclusive. -/
noncomputable def sampleCellCode : C :=
  .seq (.itePos (0 - .get 1 sampleColumn) (.letR 47 0) (.letR 47 (.get 4 sampleColumn / 4)))
    (.seq (.itePos (.var 46 - .var 45) .skip
        (.itePos ((.var 46 + .var 47) - .var 45)
          (.seq (.put 9 (.var 45) (.nat (.var 47 + 1)))
            (.put 10 (.var 45) (.nat (.var 46))))
          .skip))
      (.letR 46 (.var 46 + .var 47)))

/-- Draw once per item, visit the choice-time columns, and record the selected label and choice.
Zero in table 9 means that the item was unassigned, and `h+1` denotes label `h`. -/
noncomputable def sampleRowsCode : C :=
  .forN 45 (.var 0)
    (.seq (.uniform 45)
      (.seq (.letR 46 0)
        (.seq (.put 9 (.var 45) 0)
          (.forN 46 (.var 1) (.forN 47 (.var 2) sampleCellCode)))))

/-- Write one emitted policy entry in the platform's output format. -/
noncomputable def emitEntryCode : C :=
  .seq (.out (1 + 3 * .var 48) (.nat (.var 45)))
    (.seq (.out (2 + 3 * .var 48) (.get 10 (.var 45)))
      (.seq (.out (3 + 3 * .var 48) (.var 0 - .get 0 (.var 47)))
        (.letN 48 (.var 48 + 1))))

noncomputable def emitIfCode : C :=
  let marker : R := .get 9 (.var 45)
  let expected : R := .nat (.var 47 + 1)
  .itePos (marker - expected) .skip (.itePos (expected - marker) .skip emitEntryCode)

/-- Emit in label order with increasing item index breaking ties, then write the list length. -/
noncomputable def emitRowsCode : C :=
  .seq (.letN 48 0)
    (.seq (.forN 47 (.var 2) (.forN 45 (.var 0) emitIfCode))
      (.out 0 (.nat (.var 48))))

/-- Sample the skipping policy from the solved dyadic LP, then serialize it in scan order. -/
noncomputable def samplingCode : C := .seq sampleRowsCode emitRowsCode

end PandoraKnapsack.Skipping.ArrayRAM


