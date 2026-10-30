-- Prove2me | Definitions.Def_OAIQ081S146
-- name    : OAIQ081S146
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:52:07.547514+00:00
-- url     : https://prove2.me/theorems/dc2e732b-db4f-4c9c-8f20-ad5c64ca9e9f
-- title:
--   Definitions bundle OAIQ081S146 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 59 declarations of OpenAI's Lean: 28 definitions, 3 inductive types or structures and 28 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Query.Sources`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Measured`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.OutputEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.Query.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety.baseSafe`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety.safe`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.highCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.NodesInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.environment`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.working`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.advanceU`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.buildQuery`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.finishRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.inner`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.row`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.slot`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.startRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wclear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wcopy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wideAccumulate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wpush`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsReadoutProgram.wtransfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.NativePackingBounds.sourceSize`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.ArithmeticInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTable.preparedStore`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LeafProgramQueryInput`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendCore`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendMeasure`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendRegisterSafety`, `SubexponentialSAT_SqrtLog_LeafQueryFrontendRun`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolationReplay`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative`, `SubexponentialSAT_SqrtLog_MomentsReadoutProgramState`, `SubexponentialSAT_SqrtLog_NativePackingBounds`, `SubexponentialSAT_SqrtLog_NativePackingBoundsGenerated`, `SubexponentialSAT_SqrtLog_PerturbationAssemblyInputReady`, `SubexponentialSAT_SqrtLog_RingNodeProgram`, `SubexponentialSAT_SqrtLog_RingNodeProgramModel`, `SubexponentialSAT_SqrtLog_RingNodeProgramPrepare`, `SubexponentialSAT_SqrtLog_RingProgramTableInitial`, `SubexponentialSAT_SqrtLog_RingProgramTableModel`, `SubexponentialSAT_SqrtLog_RingProgramTablePowers`, `SubexponentialSAT_SqrtLog_RingProgramTableSemantics`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S121`, `OAIQ081S122`, `OAIQ081S123`, `OAIQ081S125`, `OAIQ081S127`, `OAIQ081S128`, `OAIQ081S129` and `OAIQ081S130` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S158`, `OAIQ081S159` and `OAIQ081S165`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.callback_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.WeightedCore.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Multiplier.arithmetic_runs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.accumulator_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps.mul_hash_clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentApplyProgram.add_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.accumulate_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.arityCall_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.measureCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Normalize.program_run` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.step_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S121
import Definitions.Def_OAIQ081S122
import Definitions.Def_OAIQ081S123
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S127
import Definitions.Def_OAIQ081S128
import Definitions.Def_OAIQ081S129
import Definitions.Def_OAIQ081S130

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCalls
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The frontend calls only concrete finite machines. All state embeddings
below are specifications of actual calls, never free data transformations. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

def highCall : Code := .call (ProgramLinking.liftProgram HighIncidenceProgram.Prepare.program r10 high)
def arityCall : Code := .call (ProgramLinking.liftProgram LeafStatisticsProgram.Arity.program r10 arity)

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendMeasure
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual scope/mask scans are joined before any statistic is converted. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod


def measureCommand : Code := sequence [copies statsCopies,statsCall,
  copies arityCopies,arityRegisters,arityCall,finishCall]

def Measured (rows : List (List ℕ)) (forward : List Bool) (a : Data) : Prop :=
  a.stacks 626=List.replicate (totals rows forward).free true ∧
  a.stacks 627=List.replicate (totals rows forward).occurrence true ∧
  a.stacks 628=List.replicate (totals rows forward).incidences true ∧
  a.stacks 613=List.replicate (rows.length+(totals rows forward).uncovered) true ∧
  a.stacks 642=List.replicate (completedArity rows forward) true

noncomputable def measureBudget (a : Data) (rows : List (List ℕ)) (forward : List Bool) :=
  copiesCost statsCopies a+LeafStatisticsProgram.bootBudget rows forward+
  LeafStatisticsProgram.variableBudget rows 0 forward+2+
  7*forward.length+5+7*(LeafStatisticsProgram.scopeBits rows).length+5+3+
  4+RecordPrograms.budget (LeafStatisticsProgram.Arity.cost forward)
    (rows.map (Encoding.encodeList Encoding.encodeNat))+3*(totals rows forward).uncovered+10

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Joined per-query core. Mathematical values below describe physical input
words and computed outputs; they are not extra machine inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

def Query.Ready (q : Query) (a : Data) : Prop :=
  a.stacks 700=Encoding.encodeList id q.clauses ∧
  a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows ∧
  a.stacks 705=q.index ∧ a.stacks 706=[q.mark.isSome] ∧
  a.stacks 707=q.modulus ∧ a.stacks 708=q.width ∧ a.stacks 709=q.ambient ∧
  emptyRange a 340 680 ∧ a.stacks 338=[] ∧ a.stacks 718=[] ∧ a.stacks 719=[]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete source masters and reusable empty workspace at each marked
query boundary. The frontend's hypotheses follow after the paid reference
staging program; no serialized scope or arithmetic cache is an input. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod

structure Sources (q : LeafQueryFrontend.Query) (a : Data) : Prop where
  formula : a.stacks 700=Encoding.encodeList id q.clauses
  rows : a.stacks 701=HashScopeProgram.RawTable.inputBits q.width.length q.rows
  modulus : a.stacks 707=q.modulus
  width : a.stacks 708=q.width
  ambient : a.stacks 709=q.ambient

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls
attribute [local simp] Fin.coe_ofNat_eq_mod
open LeafParametersProgram

def Query.OutputEmpty (_q : Query) (a : Data) : Prop :=
  Exports.OutputEmpty a ∧ a.stacks 704=[] ∧ a.stacks 134=[] ∧ a.stacks 141=[]

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafQueryFrontendRegisterSafety
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Structural register frames for the actual frontend syntax. -/
namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety
open SubexponentialSAT BitProgram StructuredCalls

abbrev baseSafe {r s : ℕ} (j : Fin r) : StructuredProgram.Cmd r s → Prop
  | .skip => True
  | .atom a => ∀ d, (a.eval d).regs j=d.regs j
  | .seq a b => baseSafe j a ∧ baseSafe j b
  | .ite _ a b => baseSafe j a ∧ baseSafe j b
  | .while _ a => baseSafe j a

abbrev safe {r s : ℕ} (j : Fin r) : Cmd r s → Prop
  | .base c => baseSafe j c
  | .call p => ∀ q d, (execInstr (p.code q) d).regs j=d.regs j
  | .seq a b => safe j a ∧ safe j b
  | .ite _ a b => safe j a ∧ safe j b
  | .while _ a => safe j a

end SubexponentialSAT.SqrtLog.LeafQueryFrontend.RegisterSafety

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed physical program generating all nonzero radix nodes up to a runtime
bound. The bound counts down, so prepending each row gives ascending order. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation SubexpBasePUnranking SubexpEnumerationProgram
open BinaryArithmetic SubexpLiftRing

theorem step_eval (r : Fin 8 → Bool) (m rank arity out : List Bool)
    (hp : 0 < value rank) (hm : 0 < BinaryArithmetic.toNat m) :
    ∃ n ≤ stepBudget m.length rank.length arity.length, ∃ rf,
      Eval step n (data r m rank arity [] [] out)
        (data rf m (ripple false rank) arity [] []
          (digits m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out)) ∧
      rf (ports.register 2) = !(isZero (ripple false rank)) := by
  obtain ⟨nb, hb, rb, eb⟩ := SubexpFieldRowPreparation.command_eval r m rank arity out
  rw [unrank_eq_digits m rank hm] at eb
  let out' := digits m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out
  let db := data rb m rank arity [] [] out'
  have ed := ripple_eval ports false false db rfl
  rw [ripple_data] at ed
  let rd := (rippleResult ports false false db).regs
  have et := test_eval ports (data rd m (ripple false rank) arity [] [] out') rfl
  have hf := testResult_flag ports (data rd m (ripple false rank) arity [] [] out')
  rw [test_data] at et
  have h := eb.seq (ed.seq et)
  refine ⟨_, ?_, _, h, hf⟩
  dsimp [db, out'] at *
  have hc := rippleCost_le false rank
  have hl := decrement_length hp
  simp only [ports, target, Bool.false_eq_true, ↓reduceIte, data, tapes_13] at *
  dsimp [stepBudget, SubexpFieldRowPreparation.budget, SubexpBasePUnranking.budget] at *
  omega

theorem loop_eval (Q : ℕ) (r : Fin 8 → Bool) (m rank arity out : List Bool)
    (hm : 0 < BinaryArithmetic.toNat m) (hq : value rank = Q)
    (hf : r (ports.register 2) = !(isZero rank)) :
    ∃ n ≤ Q * stepBudget m.length rank.length arity.length + Q + 1, ∃ rf finalRank,
      Eval loop n (data r m rank arity [] [] out)
        (data rf m finalRank arity [] []
          (stream m.length (BinaryArithmetic.toNat m) arity.length Q ++ out)) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  induction Q generalizing r rank out with
  | zero =>
    have hz := (isZero_eq_true_iff rank).2 hq
    refine ⟨1, by omega, r, rank, ?_, hq, rfl⟩
    simpa [stream, loop, hz] using (Eval.while_false (body := step)
      (by simpa [SubexpFieldRowPreparation.data, hz] using hf) :
      Eval (.while (ports.register 2) step) 1
        (data r m rank arity [] [] out) (data r m rank arity [] [] out))
  | succ Q ih =>
    have hp : 0 < value rank := by omega
    have hz := (isZero_eq_false_iff rank).2 hp
    obtain ⟨ns, hs, rs, es, fs⟩ := step_eval r m rank arity out hp hm
    have hv := value_decrement hp
    have hl := decrement_length hp
    have hnext : value (ripple false rank) = Q := by omega
    obtain ⟨nl, hlb, rl, last, el, hvlast, hllast⟩ :=
      ih rs (ripple false rank)
        (digits m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out) hnext fs
    refine ⟨ns + nl + 1, ?_, rl, last, ?_, hvlast, hllast.trans hl⟩
    · rw [hl] at hlb
      nlinarith
    · have h := Eval.while_true
        (by simpa [SubexpFieldRowPreparation.data, hz] using hf) es el
      have hr : BinaryArithmetic.toNat rank = Q + 1 := by rw [← value_eq_toNat, hq]
      simpa only [loop, stream, List.append_assoc, hr] using h

/-- No node table is an input: runtime Q, arity, and a padded positive radix
suffice to physically produce every node record. -/
theorem command_eval (r : Fin 8 → Bool) (m rank arity out : List Bool)
    (hm : 0 < BinaryArithmetic.toNat m) :
    ∃ n ≤ budget m.length rank.length arity.length (BinaryArithmetic.toNat rank), ∃ rf finalRank,
      Eval command n (data r m rank arity [] [] out)
        (data rf m finalRank arity [] []
          (stream m.length (BinaryArithmetic.toNat m) arity.length (BinaryArithmetic.toNat rank) ++ out)) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  have et := test_eval ports (data r m rank arity [] [] out) rfl
  have hf := testResult_flag ports (data r m rank arity [] [] out)
  rw [test_data] at et
  obtain ⟨nl, hl, rf, last, el, hv, hlen⟩ :=
    loop_eval (BinaryArithmetic.toNat rank) _ m rank arity out hm (value_eq_toNat rank) hf
  refine ⟨_, ?_, rf, last, et.seq el, hv, hlen⟩
  simp only [ports, data, tapes_13]
  dsimp [budget]
  nlinarith

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical radix generator emits precisely the coefficient encoding of
nodes in the actual supplied-polynomial unramified ring. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BinaryArithmetic SubexpLiftRing SubexpQuarticRing
open RingProgram

theorem nodeCode_flat (t d n : ℕ) :
    flat (nodeCode t d n) = digits (baseWidth 3 t) 3 d n :=
  (digits_eq_ofFn _ _ _ _).symm

theorem stream_eq_flat_nodes (t d Q : ℕ) :
    stream (baseWidth 3 t) 3 d Q =
      (List.finRange Q).flatMap (fun i => flat (nodeCode t d (i.val+1))) := by
  induction Q with
  | zero => simp [stream]
  | succ Q ih =>
    rw [stream, List.finRange_succ_last, List.flatMap_append, List.flatMap_map,
      List.flatMap_singleton, ih]
    simp only [ Fin.val_castSucc, Fin.val_last, nodeCode_flat]

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableInitial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpQuarticRing

theorem literalLast_word {B : ℕ} (n : ℕ) (seed zeroWord old : Word B) :
    literalLast n seed zeroWord old.val = (literalLastWord n seed zeroWord old).val := by
  induction n generalizing seed old with
  | zero => rfl
  | succ n ih => exact ih zeroWord seed

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingNodeProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Constant-control preparation of the padded radix and the final node stream.
The only supplied words are zero padding, binary Q, and unary d. -/
namespace SubexponentialSAT.SqrtLog.RingNodeProgram

open SubexponentialSAT BitProgram StructuredCalls CounterPrograms
open SubexpFieldRowPreparation BinaryArithmetic SubexpLiftRing

theorem preparedCommand_eval (r : Fin 8 → Bool) (B : ℕ) (hB : 2 ≤ B)
    (rank arity out : List Bool) :
    ∃ n ≤ budget B rank.length arity.length (BinaryArithmetic.toNat rank) + 4, ∃ rf finalRank,
      Eval preparedCommand n (data r (List.replicate B false) rank arity [] [] out)
        (data rf (true :: true :: List.replicate (B-2) false) finalRank arity [] []
          (stream B 3 arity.length (BinaryArithmetic.toNat rank) ++ out)) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  have hz : List.replicate B false = false :: false :: List.replicate (B-2) false := by
    conv_lhs => rw [show B = (B-2)+2 by omega]
    simp [List.replicate_succ]
  obtain ⟨r1,h1⟩ := prepareRadix_eval r (List.replicate (B-2) false) rank arity out
  rw [← hz] at h1
  have hzv (k : ℕ) : BinaryArithmetic.toNat (List.replicate k false) = 0 := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, ih]
  have hm : BinaryArithmetic.toNat (true :: true :: List.replicate (B-2) false) = 3 := by
    simp [BinaryArithmetic.toNat, bitVal, hzv]
  obtain ⟨n,hn,rf,last,he,hv,hl⟩ := command_eval r1
    (true :: true :: List.replicate (B-2) false) rank arity out (by omega)
  have hw : (true :: true :: List.replicate (B-2) false).length = B := by simp; omega
  rw [hm,hw] at he
  rw [hw] at hn
  exact ⟨4+n,by omega,rf,last,h1.seq he,hv,hl⟩

/-- Physical generation of the exact reconstruction input ABI from runtime
sizes, including radix construction and every loop/control instruction. -/
theorem preparedProgram_nodes (r : Fin 8 → Bool) (t : ℕ) (ht : 0 < t)
    (rank arity : List Bool) :
    ∃ rf finalRank,
      RunsIn preparedProgram
        (budget (baseWidth 3 t) rank.length arity.length (BinaryArithmetic.toNat rank) + 5)
        ((data r (List.replicate (baseWidth 3 t) false) rank arity [] [] []).withPC
          (some preparedProgram.entry))
        ((data rf (true :: true :: List.replicate (baseWidth 3 t-2) false)
          finalRank arity [] []
          ((List.finRange (BinaryArithmetic.toNat rank)).flatMap
            (fun i => RingProgram.flat (nodeCode t arity.length (i.val+1))))).withPC none) ∧
      value finalRank = 0 ∧ finalRank.length = rank.length := by
  obtain ⟨n,hn,rf,last,he,hv,hl⟩ := preparedCommand_eval r (baseWidth 3 t)
    (by rw [RingProgram.ternary_baseWidth]; omega) rank arity []
  rw [stream_eq_flat_nodes, List.append_nil] at he
  exact ⟨rf,last,⟨n+1,by omega,compiled_halt_trace he 13 12⟩,hv,hl⟩

end SubexponentialSAT.SqrtLog.RingNodeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTablePowers
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem powerLoop_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ)
    (v : VectorData (baseWidth p t) d) (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ m ≤ n*(roundBudget (baseWidth p t) d+2)+1, ∃ rf, Eval powerLoop m
      (state (readRegs regs 1 3 count.head?) (ready {s with rounds := count.tail} c v zeroWord minusOne))
      (state rf (ready {s with rounds := [], powers := (generatedBits p t M zeroWord minusOne c n v).reverse ++ s.powers}
        c (iterData p t M zeroWord minusOne c n v) zeroWord minusOne)) := by
  induction n generalizing v s regs count with
  | zero =>
    have hc : count = [] := List.length_eq_zero_iff.mp hcount
    subst count
    refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
    apply Eval.while_false
    simp [ readRegs_present]
  | succ n ih =>
    cases count with
    | nil => simp at hcount
    | cons bit count =>
      have hc : count.length = n := by simpa using hcount
      let next := advance p t M zeroWord minusOne c v
      let s' := {s with powers := (wordBits next.coefficients.val).reverse ++ s.powers}
      obtain ⟨m, hm, rf, hr⟩ := round_eval p t M hd zeroWord minusOne c v {s with rounds := count}
        (readRegs regs 1 3 (some bit)) hmod hw hdegree
      have hp := popRound_eval (ready {s' with rounds := count} c next zeroWord minusOne) rf
      obtain ⟨k, hk, rg, hl⟩ := ih next s' rf count hc hmod hw hdegree
      have he := Eval.while_true
        (show (state (readRegs regs 1 3 (some bit)) (ready {s with rounds := count} c v zeroWord minusOne)).regs 3 = true by
          simp [ readRegs_present]) (hr.seq hp) hl
      refine ⟨m+1+k+1, ?_, rg, ?_⟩
      · nlinarith
      · simpa only [powerLoop, generatedBits, iterData, List.head?_cons, List.tail_cons,
          List.reverse_append, List.append_assoc, s', next] using he

theorem powerScan_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (n : ℕ)
    (v : VectorData (baseWidth p t) d) (s : Store) (regs : Fin 8 → Bool) (count : List Bool)
    (hcount : count.length = n) (hmod : s.modulus = M.bits)
    (hw : s.width.length = baseWidth p t) (hdegree : s.degree.length = d) :
    ∃ m ≤ n*(roundBudget (baseWidth p t) d+2)+2, ∃ rf, Eval powerScan m
      (state regs (ready {s with rounds := count} c v zeroWord minusOne))
      (state rf (ready {s with rounds := [], powers := (generatedBits p t M zeroWord minusOne c n v).reverse ++ s.powers}
        c (iterData p t M zeroWord minusOne c n v) zeroWord minusOne)) := by
  have hp := popRound_eval (ready {s with rounds := count} c v zeroWord minusOne) regs
  obtain ⟨m, hm, rf, hl⟩ := powerLoop_eval p t M hd zeroWord minusOne c n v s regs count hcount hmod hw hdegree
  exact ⟨1+m, by omega, rf, hp.seq hl⟩

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

theorem advance_tailCorrect (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t))
    (c : List.Vector (Word (baseWidth p t)) d) (v : VectorData (baseWidth p t) d) :
    TailCorrect (advance p t M zeroWord minusOne c v) := by
  apply outputWords_last
  intro he
  have h : (c.val.zip v.coefficients.val).length = d := by simp
  rw [he] at h
  simp at h
  omega


theorem literalWords_last {B : ℕ} (n : ℕ) (hn : 0 < n)
    (seed zeroWord old : Word B) :
    (literalWords n seed zeroWord).getLast? = some (literalLastWord n seed zeroWord old) := by
  induction n generalizing seed old with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simpa only [literalWords, literalLastWord, List.getLast?_cons_cons] using
        ih (by omega) zeroWord seed

theorem initialData_tailCorrect {B d : ℕ} (hd : 0 < d) (oneWord zeroWord : Word B) :
    TailCorrect (initialData d oneWord zeroWord) :=
  literalWords_last d hd oneWord zeroWord zeroWord

theorem iterData_tailCorrect (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) {d : ℕ} (hd : 0 < d)
    (zeroWord minusOne : Word (baseWidth p t)) (c : List.Vector (Word (baseWidth p t)) d)
    (n : ℕ) (v : VectorData (baseWidth p t) d) (hv : TailCorrect v) :
    TailCorrect (iterData p t M zeroWord minusOne c n v) := by
  induction n with
  | zero => exact hv
  | succ n ih =>
    rw [iterData_succ]
    exact advance_tailCorrect p t M hd zeroWord minusOne c _

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramTableModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def preparedStore (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {d : ℕ} (c : List.Vector (Word (baseWidth p t)) d) (s : Store) : Store :=
  ready {s with powers := allPowerBits p t M c cache.one cache.zero cache.minusOne, rounds := []}
    c (iterData p t M cache.zero cache.minusOne c (2*d-2)
      (initialData d cache.one cache.zero)) cache.zero cache.minusOne

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! The fixed executable preparation pipeline.  Its input is the actual
numerical bank emitted by `LeafParametersProgram`; no field polynomial,
modulus, multiplication table, nodes, or idempotent coefficients are inputs.
The stage-by-stage execution theorem is separate from this code definition.
-/


/-! Arithmetic consumers use the same bytes generated by the preceding
stages.  These are structural handoff lemmas; the complete production
trace must establish `NativeBytes` before invoking them. -/

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls

/-- A finite list of counter conversions is one measured program.  Its
conclusion identifies every stack, including preserved parameter words. -/
theorem unaryPlan_eval (ps : List (Fin 640 × Fin 640)) (a : Data)
    (hports : ∀ p ∈ ps, p.1.val < 625 ∧ p.2.val < 625 ∧ p.1≠p.2)
    (hnd : (ps.map Prod.snd).Nodup)
    (hempty : ∀ p ∈ ps, a.stacks p.2=[])
    (h11 : a.stacks 636=[]) (h12 : a.stacks 637=[]) (h13 : a.stacks 638=[]) :
    ∃ n ≤ counterCost ps a.stacks, ∃ e : Data,
      Eval (unaryPlan ps) n a e ∧ e.stacks=counterStacks ps a.stacks := by
  induction ps generalizing a with
  | nil => exact ⟨0,le_rfl,a,.base (.skip _),rfl⟩
  | cons p ps ih =>
    have hp := hports p (by simp)
    have hnd' : p.2 ∉ ps.map Prod.snd ∧ (ps.map Prod.snd).Nodup := by
      simpa using hnd
    obtain ⟨n,hn,e,he,hs⟩ := unary_eval_stacks p.1 p.2 a hp.1 hp.2.1 hp.2.2
      (hempty p (by simp)) h11 h12 h13
    have htail : ∀ q ∈ ps, e.stacks q.2=[] := by
      intro q hq
      have hne : q.2≠p.2 := by
        intro hh
        exact hnd'.1 (hh ▸ List.mem_map_of_mem hq)
      rw [hs,Function.update_of_ne hne]
      exact hempty q (by simp [hq])
    have h636 : (636 : Fin 640)≠p.2 := by intro h; have:=congrArg Fin.val h; omega
    have h637 : (637 : Fin 640)≠p.2 := by intro h; have:=congrArg Fin.val h; omega
    have h638 : (638 : Fin 640)≠p.2 := by intro h; have:=congrArg Fin.val h; omega
    obtain ⟨m,hm,f,hf,hfs⟩ := ih e (fun q hq => hports q (by simp [hq])) hnd'.2
      htail (by simpa [hs,h636] using h11) (by simpa [hs,h637] using h12)
      (by simpa [hs,h638] using h13)
    refine ⟨n+m,?_,f,he.seq hf,?_⟩
    · change n+m ≤ LeafParametersProgram.Serialization.unaryCopyBound (a.stacks p.1)+1+counterCost ps (counterStack a.stacks p)
      have hs' : e.stacks=counterStack a.stacks p := hs
      rw [←hs']
      exact Nat.add_le_add hn hm
    · change f.stacks=counterStacks ps (counterStack a.stacks p)
      have hs' : e.stacks=counterStack a.stacks p := hs
      rw [←hs']
      exact hfs

theorem numericPlan_eval (a : Data)
    (hempty : ∀ p ∈ numericPlan, a.stacks p.2=[])
    (h11 : a.stacks 636=[]) (h12 : a.stacks 637=[]) (h13 : a.stacks 638=[]) :
    ∃ n ≤ counterCost numericPlan a.stacks, ∃ e : Data,
      Eval (unaryPlan numericPlan) n a e ∧ e.stacks=counterStacks numericPlan a.stacks :=
  unaryPlan_eval numericPlan a (by
    intro p hp
    simp only [numericPlan,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl <;> decide) (by decide) hempty h11 h12 h13

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram
open BitProgram StructuredCalls SubexpLiftRing

structure NodesInput (t : ℕ) (a : Data) : Prop where
  zero : a.stacks 617=List.replicate (baseWidth 3 t) false
  clean : ∀ i : Fin 15, i∉([5,13,14] : List (Fin 15)) → a.stacks (nodes i)=[]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramInterpolationReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact-time replay footprint of the existing interpolation producer. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem clear (i : Fin 768) (h : ¬LeafProgram.OuterCarried.hidden i) : AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.clear i) :=
  avoids_clearProgram LeafProgram.OuterCarried.hidden i 38 39 h

theorem copy (src dst : Fin 768) (hs : ¬LeafProgram.OuterCarried.hidden src) (hd : ¬LeafProgram.OuterCarried.hidden dst) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copy src dst) :=
  avoids_copyProgram LeafProgram.OuterCarried.hidden src dst 699 38 39 hs hd (by decide)

theorem overwrite (src dst : Fin 768) (hs : ¬LeafProgram.OuterCarried.hidden src) (hd : ¬LeafProgram.OuterCarried.hidden dst) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.overwrite src dst) := ⟨clear dst hd,copy src dst hs hd⟩

theorem clearPorts (ps : List (Fin 768)) (hp : ∀i∈ps,¬LeafProgram.OuterCarried.hidden i) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.clearPorts ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨clear p (hp p (by simp)),ih (fun i hi => hp i (by simp [hi]))⟩

theorem copyPlan (ps : List (Fin 768 × Fin 768))
    (hp : ∀p∈ps,¬LeafProgram.OuterCarried.hidden p.1 ∧ ¬LeafProgram.OuterCarried.hidden p.2) :
    AvoidsCmd LeafProgram.OuterCarried.hidden (Interpolation.copyPlan ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨overwrite p.1 p.2 (hp p (by simp)).1 (hp p (by simp)).2,
      ih (fun q hq => hp q (by simp [hq]))⟩

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Interpolation.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramReplay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Syntactic no-read/no-write certificate for the existing native ring
producer.  Hidden collector tapes do not affect its exact execution time. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay
open BitProgram StructuredCalls ProgramTapeReplay

theorem unaryPlan (ps : List (Fin 640 × Fin 640))
    (hp : ∀p∈ps,¬hidden p.1 ∧ ¬hidden p.2) :
    AvoidsCmd hidden (LeafRingSetupProgram.unaryPlan ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih =>
    exact ⟨unary p.1 p.2 (hp p (by simp)).1 (hp p (by simp)).2,
      ih (fun q hq => hp q (by simp [hq]))⟩

theorem buildConstant (src out : Fin 640) (hs : ¬hidden src) (ho : ¬hidden out) :
    AvoidsCmd hidden (LeafRingSetupProgram.buildConstant src out) := by
  refine ⟨overwrite src 538 hs (by decide),?_⟩
  apply avoids_call_lift_of_range
  intro i
  unfold constant
  split_ifs
  · decide
  · exact ho
  · decide
  · decide
  · apply visible
    right
    dsimp
    omega

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram.Replay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

 def state (regs : Fin 8 → Bool) (modulus width count dict source : List Bool) : Data :=
  extend (Dictionary.machine regs (Dictionary.outputTape modulus width count dict [])) source

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

def ready {B d : ℕ} (regs : Fin 8 → Bool) (modulus width count : List Bool)
    (key : K → List Bool) (seed source : List (K × RingProgram.Code (Word B) d)) : Data :=
  state (readRegs regs 0 7 (bytes key source).head?) modulus width count (bytes key seed) (bytes key source)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Runtime persistent context. Every non-context low stack is initially empty. -/
def environment (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (degree width : List Bool) (u J : ℕ) : Store :=
  idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)

def working (e : Store) {n B d : ℕ} (left right acc : List (Entry n B d)) : Store :=
  {e with left := Normalize.bytes Squarefree.encodeIndex left, right := Normalize.bytes Squarefree.encodeIndex right, acc := Normalize.bytes Squarefree.encodeIndex acc}

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed forty-stack workspace for the two runtime readout counters. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def wideAccumulate : WideCode := .call
  (ProgramLinking.liftProgram accumulateProgram id widePorts)

def wcopy (src dst tmp : Fin 40) : WideCode :=
  .call (copyProgram src dst tmp (0 : Fin 8) 1)
def wtransfer (src dst : Fin 40) : WideCode :=
  .call (transferProgram src dst (0 : Fin 8) 1)
def wclear (src : Fin 40) : WideCode := .call (clearProgram src (0 : Fin 8) 1)

def wpush (dst : Fin 40) (bit : Bool) : WideCode :=
  .seq (.base (.atom (.set 0 bit))) (.base (.atom (.push dst 0)))

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Actual stack construction of the sparse key (u,z,empty support), followed
by the paid query cleanup and unary-index increment. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

def buildQuery : WideCode := .seq (wcopy 30 16 23)
  (.seq (wpush 16 false) (.seq (wcopy 31 16 23)
    (.seq (wpush 16 false) (wcopy 34 16 23))))

def advanceU : WideCode := .seq (wclear 16) (wpush 30 true)

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! One concrete (u,z) coefficient fetch, addition, and index advance. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def slot : WideCode := .seq buildQuery (.seq wideAccumulate advanceU)

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! The U loop is driven by a real unary stack. Every visit invokes the
concrete key builder and dictionary scan; no callback is left abstract. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def inner : WideCode := UnaryForPrograms.forCmd innerPorts slot

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Seed one Z accumulator from the cached zero vector and append the
completed coefficient to the output, paying for every copy and reversal. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def startRow : WideCode := .seq (wcopy 27 17 23) (wcopy 28 32 23)

def finishRow : WideCode := .seq (wtransfer 17 35) (.seq (wclear 30) (wpush 31 true))

def row : WideCode := .seq startRow (.seq inner finishRow)

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram


/-! Runtime Z enumeration. Completed fixed-width coefficients are prepended
in reverse and are restored once by the final output transfer. -/


/-! Build the all-false support mask from the actual ambient shape stack.
The loop length is the ambient number of variables, including unused ones. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsReadoutProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! End-to-end finite readout machine. Runtime words supply both loop counts,
the ambient shape, and the already constructed coefficient zero vector. -/
namespace SubexponentialSAT.SqrtLog.MomentsReadoutProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

def finish : WideCode := .seq (wtransfer 35 0) (.seq (wclear 31) (wclear 34))

end SubexponentialSAT.SqrtLog.MomentsReadoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBoundsGenerated
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native address-plan frontend bounds. The source size includes the actual
input plans and the number of represented types, not a scope-generated plan. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp LayoutProgram LayoutProgram.NativePacking
variable {U : Type*} [DecidableEq U]

def sourceSize (s : Spec U) : ℕ :=
  s.params.D+s.params.Δ+s.types.values.length+s.params.width.length+
    s.params.rows.flatten.length+(ProgramEncoding.encodeRecords s.params.alphabet).length+
    s.params.planStream.length+1

theorem depth_le (s : Spec U) : s.params.Δ+1 ≤ sourceSize s := by unfold sourceSize; omega
theorem count_le (s : Spec U) : s.types.values.length ≤ sourceSize s := by unfold sourceSize; omega
theorem alphabet_bytes_le (s : Spec U) : (ProgramEncoding.encodeRecords s.params.alphabet).length ≤ sourceSize s := by unfold sourceSize; omega

theorem type_word_le (s : Spec U) :
    ∀ row ∈ s.params.typeRows, row.length ≤ sourceSize s ^ 2 := by
  have hw : ∀ x ∈ s.params.alphabet,
      x.length ≤ (ProgramEncoding.encodeRecords s.params.alphabet).length :=
    PackingTupleBounds.member_length_le s.params.alphabet
  have hp := PackingTupleBounds.powerRows_width s.params.alphabet [[]] (s.params.Δ + 1) 0 _
    (by simp) hw
  intro row hr
  have h := hp row hr
  have hm : (s.params.Δ + 1) * (ProgramEncoding.encodeRecords s.params.alphabet).length ≤
      sourceSize s ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul (depth_le s) (alphabet_bytes_le s)
  calc
    row.length ≤ (s.params.Δ + 1) * (ProgramEncoding.encodeRecords s.params.alphabet).length := by
      simpa only [Nat.zero_add] using h
    _ ≤ sourceSize s ^ 2 := hm

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NativePackingBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial cost of the actual native address-plan suffix. -/
namespace SubexponentialSAT.SqrtLog.NativePackingBounds
open SubexponentialSAT.Subexp SubexponentialSAT.BitProgram LayoutProgram
variable {U : Type*} [DecidableEq U]

theorem keys_word_le (s : NativePacking.Spec U) :
    ∀ key ∈ PackLabels.keys s.suffix, key.length ≤ sourceSize s ^ 2 := by
  intro key hk
  apply type_word_le s key
  rw [s.type_records]
  exact hk

end SubexponentialSAT.SqrtLog.NativePackingBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PerturbationAssemblyInputReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Recover the native arithmetic invariants from the actual staged cache
words and an otherwise empty low workspace. No execution premise is used. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl DensePolynomialProgram
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod

structure ArithmeticInput (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (s : Store) : Prop where
  modulus : s 194=M.bits
  lowModulus : s 5=s 194
  width : (s 202).length=baseWidth 3 t
  lowWidth : s 10=s 202
  zero : s 203=cache.zero.val
  table : s 201=RingTriple.tableEncoding (HornerProgram.modelTable t a M cache)
  degree : (s 204).length=d
  fullZero : s 104=List.replicate (d*baseWidth 3 t) false
  clean : ∀ i:Fin 256,i.val < 205 → i∉arithmeticCachePorts → s i=[]

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
end


