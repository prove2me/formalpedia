-- Prove2me | Definitions.Def_OAIQ081S092
-- name    : OAIQ081S092
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:14:42.050558+00:00
-- url     : https://prove2.me/theorems/c6b124c0-3663-4720-a79f-627424462596
-- title:
--   Definitions bundle OAIQ081S092 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 87 declarations of OpenAI's Lean: 77 definitions and 10 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.LocalData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.constant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.duplicate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.localCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.prepare`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafNodeCacheProgram.prepared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNative.References.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNative.References.expand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNative.References.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNative.References.output`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routeCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routesCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.routesState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.saveWidth`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stageBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stageResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stageReturned`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stageSaved`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.workerCleared`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search.Invariant`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.SqrtData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.SqrtLocalReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParameterArithmetic.SqrtReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.check`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.checks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute.check`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.OutputEmpty`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.Scratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.budget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.clearCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.exportBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports.exportState` and 37 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_LayoutUniversal`, `SubexponentialSAT_SqrtLog_LeafHighContextProgramBase`, `SubexponentialSAT_SqrtLog_LeafNodeCacheProgram`, `SubexponentialSAT_SqrtLog_LeafOuterNativeReferences`, `SubexponentialSAT_SqrtLog_LeafOuterProgramPrepareCode`, `SubexponentialSAT_SqrtLog_LeafOuterProgramStage`, `SubexponentialSAT_SqrtLog_LeafOuterProgramStorage`, `SubexponentialSAT_SqrtLog_LeafParameterArithmetic`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticSearch`, `SubexponentialSAT_SqrtLog_LeafParameterArithmeticSqrt`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExports`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExportsOps`, `SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable`, `SubexponentialSAT_SqrtLog_LeafParametersProgramInterval`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_LeafParametersProgramSerializationUnary`, `SubexponentialSAT_SqrtLog_LeafProgramClauseCount`, `SubexponentialSAT_SqrtLog_LeafProgramCount`, `SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsArity`, `SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram`, `SubexponentialSAT_SqrtLog_SetupCleanup`, `SubexponentialSAT_SqrtLog_SetupGuard`, `SubexponentialSAT_SqrtLog_SetupSearch`, `SubexponentialSAT_SubexpCRTOuterControl`, `SubexponentialSAT_SubexpClauseMastersProgram`, `SubexponentialSAT_SubexpIntervalCoreProgram`, `SubexponentialSAT_SubexpIntervalFinishProgram`, `SubexponentialSAT_SubexpIntervalStartProgram`, `SubexponentialSAT_SubexpSetupStorage`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S066`, `OAIQ081S067`, `OAIQ081S069`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S075` and `OAIQ081S076` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S107`, `OAIQ081S108`, `OAIQ081S109`, `OAIQ081S110`, `OAIQ081S113`, `OAIQ081S114` and `OAIQ081S115`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval.at_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.stage_bounded_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgram.arity_pos_of_free_pos`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S066
import Definitions.Def_OAIQ081S067
import Definitions.Def_OAIQ081S069
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S072
import Definitions.Def_OAIQ081S075
import Definitions.Def_OAIQ081S076

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutUniversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual universal incidence-copy block over a commutative coefficient
ring in which the power-of-two denominator is a unit. -/

namespace SubexponentialSAT.SqrtLog.LayoutUniversal

open scoped BigOperators
open Matrix
open SubexponentialSAT.MulticolorTypes
open LayoutPullback LayoutExactBuckets LayoutScaledMatrices

variable {r Q : ℕ} {O : Type*} [CommRing O]

theorem locality {node : Fin Q → O} (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (a : U r Q) (t : Fin Q) (g : Fin r) (hg : g ≠ a.slot 0 t) :
    KillsIntegerKernel
      (fun y : Head t g =>
        (sourceRow (LayoutNumerator.family r Q 1 A R) denom a 0 R units y.val).eval
          (node t)) (constraints A R t g) := by
  classical
  intro z hz
  let zfull : U r Q → ℤ := row (headOwner t g) z
  have hzhead : ∀ y, y.head t ≠ g → zfull y = 0 := by
    intro y hy
    apply LayoutPullback.row_eq_zero
    rintro ⟨v, hv⟩
    exact hy (hv ▸ v.property)
  have hzjoint (y : Joint t g (0 : Fin 1)) : zfull y.val = z (jointOwner t g y) :=
    row_apply_injective (headOwner t g) (headOwner_injective t g) z
      (jointOwner t g y)
  have hc : clearedDefect (LayoutNumerator.denominator R)
      (LayoutNumerator.joint (0 : Fin 1) t g A R) *ᵥ
      (fun y : Joint t g (0 : Fin 1) => zfull y.val) = 0 := by
    funext j
    have hj := hz j
    change signature
      (pulledConstraints (jointOwner t g)
        (fun j i => clearedDefect (LayoutNumerator.denominator R)
          (LayoutNumerator.joint (0 : Fin 1) t g A R) j i)) z j = 0 at hj
    rw [signature_pullback] at hj
    simpa only [signature, duplicate, Function.comp_def, Matrix.mulVec,
      dotProduct, hzjoint, Pi.zero_apply] using hj
  have h := LayoutNumerator.family_sourceRow_annihilates A R denom hdenom a 0
    units t g hg zfull hzhead hc
  change (∑ y : Head t g,
    (sourceRow (LayoutNumerator.family r Q 1 A R) denom a 0 R units y.val).eval
      (node t) * (z y : O)) = 0
  have hcast (y : U r Q) : (zfull y : O) =
      row (headOwner t g) (fun v => (z v : O)) y :=
    row_map (Int.castRingHom O) (headOwner t g) z y
  simp_rw [hcast] at h
  rw [row_right_dot] at h
  exact h

end SubexponentialSAT.SqrtLog.LayoutUniversal

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHighContextProgramBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid parser pipeline stages the current physical high assignment. -/
namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

abbrev Data := State 4 10


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical storage operations for the closed parameter setup

All copies, clears, and register resets are fixed instruction sequences or
calls to proved bit programs. Their state transformations below are assertion
notation only. The setup program uses them to isolate dirty arithmetic
subroutines from the persistent parameter words.
-/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

def prepareCost {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) : ℕ :=
  clearManyCost [tmp] a + (clearManyCost ports (clearManyState [tmp] a) +
    (9 + copyManyCost inputs (beforeCopies tmp ports a)))

def finishCost {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) : ℕ :=
  clearManyCost (outputs.map Prod.snd) a +
    (copyManyCost outputs (clearManyState (outputs.map Prod.snd) a) +
      (clearManyCost ports (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)) + 9))

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafNodeCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical staging of node-local cached ring words. The ambient source tapes
and ring masters are copied, never consumed. The two raw-one caches are built
by the checked sparse-constant program, rather than supplied semantically. -/
namespace SubexponentialSAT.SqrtLog.LeafNodeCacheProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev LocalData := State 16 768

abbrev constant : Cmd 16 768 :=
  .call (ProgramLinking.liftProgram HashCircuitProgram.Constant.program constantRegisters constantStacks)
abbrev prepare : Cmd 16 768 := copyMany 346 copies
abbrev duplicate : Cmd 16 768 := copyMany 346 [(345,69),(345,167)]
abbrev finish : Cmd 16 768 := clearCmd 345
abbrev localCommand : Cmd 16 768 := .seq prepare (.seq constant (.seq duplicate finish))

def prepared (a : LocalData) : LocalData := copyManyState copies a


end SubexponentialSAT.SqrtLog.LeafNodeCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterNativeReferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked-reference stream is generated by a fixed program from the binary
clause count. Both binary-to-unary expansion and the quadratic framed stream
emission are part of the measured run. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterNative.References
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 10 10
abbrev expand : Cmd 10 10 := liftCommand CounterConversions.unaryCmd 0 1 registers stackMap

def input (regs : Fin 10 → Bool) (bits : List Bool) : Data :=
  ⟨regs,Function.update (fun _ => []) 0 bits⟩
def output (regs : Fin 10 → Bool) (m : ℕ) : Data :=
  ⟨regs,Function.update (fun _ => []) 7
    (ProgramEncoding.encodeRecords (RowSelectionProgram.Index.alphabet m))⟩

end SubexponentialSAT.SqrtLog.LeafOuterNative.References

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static routing for the outer leaf. Each route clears its destination and
then calls the measured physical copy routine. The route list belongs to the
fixed program, while every copied bit and every cleanup bit is charged. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls StackRoutines

abbrev Data := State 40 896

def routed (p : Route) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none,Function.update a.stacks p.2 (a.stacks p.1)⟩

def routeCost (p : Route) (a : Data) : ℕ :=
  2*(a.stacks p.2).length+7*(a.stacks p.1).length+8

def routesState : List Route → Data → Data
  | [],a => ⟨readRegs a.regs 0 1 none,a.stacks⟩
  | p::ps,a => routesState ps (routed p a)

def routesCost : List Route → Data → ℕ
  | [],_ => 3
  | p::ps,a => routeCost p a+routesCost ps (routed p a)

noncomputable def workerCleared (a : Data) : Data :=
  embedState id workerStack a LeafProgram.Cleanup.Wide.blank

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramPrepareCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafOuterProgram
open SubexponentialSAT BitProgram StructuredCalls

/-- Preserve the exact, possibly padded, count-word width for later row decoding. -/
abbrev saveWidth : Cmd 40 896 := route (768,783)

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramStage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact composition and memory charging for fixed outer-leaf stages. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls
open SubexpSetupStorage

noncomputable def stageReturned {r s : ℕ} (inputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) : Data :=
  embedState register stack (routesState inputs a) out

noncomputable def stageSaved {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) : Data :=
  routesState outputs (stageReturned inputs register stack a out)

noncomputable def stageResult {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) : Data :=
  workerCleared (stageSaved inputs outputs register stack a out)

noncomputable def stageBudget {r s : ℕ} (inputs outputs : List Route)
    (register : Fin r → Fin 40) (stack : Fin s → Fin 896)
    (a : Data) (out : State r s) (budget : ℕ) : ℕ :=
  routesCost inputs a + budget +
    routesCost outputs (stageReturned inputs register stack a out) +
    LeafProgram.Cleanup.Wide.budget
      (projectState id workerStack (stageSaved inputs outputs register stack a out)) + 1

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticQuotient
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A source-preserving floor quotient call using the audited finite binary
long-division program. Operands are runtime padded Boolean words. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

/-- The only final stack change is the quotient output. All work and both
source words are preserved, including arbitrary leading-zero padding. -/
theorem quotientAt_eval {S : ℕ} (p : QuotientPorts S) (d : Data S)
    (hd : QuotientReady p d) (hp : 0 < BinaryArithmetic.toNat (d.stacks p.right)) :
    ∃ t rf word,
      Eval (quotientAt p) t d ⟨rf, Function.update d.stacks p.out word⟩ ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat (d.stacks p.left) / BinaryArithmetic.toNat (d.stacks p.right) ∧
      word.length = (d.stacks p.left).length ∧
      t ≤ 150 * ((d.stacks p.left).length + (d.stacks p.right).length + 1)^2 := by
  let a := ArithmeticCalls.afterCopy p.left (p.work 5) d
  have hc : Eval (ArithmeticCalls.copyAt p.left (p.work 5) (p.work 1))
      (7*(d.stacks p.left).length+5) d a :=
    ArithmeticCalls.copyAt_eval _ _ _ d (p.work_ne_left 5).symm
      (p.work_ne_left 1).symm (by simp [p.work.injective.eq_iff]) (hd.2 5) (hd.2 1)
  obtain ⟨rf,word,rem,⟨t,ht,he⟩,hl,hrl,hv,_⟩ :=
    ModularQuotientPrograms.quotient_value a.regs (d.stacks p.right) (d.stacks p.left) hp
  have hcall := eval_call_lifted ModularQuotientPrograms.quotientProgram id
    (quotientStackMap p) d Function.injective_id (quotientStackMap_injective p)
    (a := ⟨a.regs, ModularQuotientPrograms.quotientStacks []
      (d.stacks p.right) (d.stacks p.left) []⟩)
    (b := ⟨rf, ModularQuotientPrograms.quotientStacks rem (d.stacks p.right) [] word⟩) he
  rw [quotient_embed_start p d hd, quotient_embed_finish p d hd] at hcall
  let b : Data S :=
    ⟨rf, Function.update (Function.update d.stacks p.out word) (p.work 0) rem⟩
  have hb : Eval (ArithmeticExpressionSupport.clearCmd (p.work 0))
      (2*rem.length+3) b
      ⟨readRegs rf 0 1 none, Function.update d.stacks p.out word⟩ := by
    have hh := ArithmeticExpressionSupport.clear_eval (p.work 0) b
    have hs : Function.update b.stacks (p.work 0) [] =
        Function.update d.stacks p.out word := by
      funext i
      by_cases hi : i = p.work 0
      · subst i; simp [b, p.work_ne_out, hd.2]
      · simp [b, hi]
    simpa only [b, Function.update_self, hs] using hh
  refine ⟨7*(d.stacks p.left).length+5+(t+(2*rem.length+3)),
    readRegs rf 0 1 none, word, hc.seq (hcall.seq hb), hv, hl, ?_⟩
  rw [hrl]
  nlinarith

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupGuard
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Guard

open BitProgram StructuredCalls
open ArithmeticExpressionSupport (clearCmd clear_eval)

/-- All arithmetic is performed by the existing finite multiplier and comparator.
The three source words are preserved and the nine scratch stacks are cleaned. -/
theorem command_eval (d : Data) (hempty : ∀ i : Fin 12, 3 ≤ i.val → d.stacks i = []) :
    ∃ t e, Eval command t d e ∧ e.stacks = d.stacks ∧
      (e.regs 0 = true ↔ BinaryArithmetic.toNat (d.stacks 0)^2 *
        BinaryArithmetic.toNat (d.stacks 1) ≤ BinaryArithmetic.toNat (d.stacks 2)) ∧
      t ≤ 10000 * ((d.stacks 0).length + (d.stacks 1).length +
        (d.stacks 2).length + 1)^2 := by
  have hwork (i : Fin 5) : 3 ≤ (work i).val := by
    change 3 ≤ i.val + 6
    omega
  have hv : ArithmeticCalls.Valid squarePorts d := by
    constructor
    · exact hempty 3 (by decide)
    · intro i; exact hempty (work i) (hwork i)
  obtain ⟨t1, r1, a, h1, ha, hla, ht1⟩ := ArithmeticCalls.multiplyAt_eval squarePorts d hv
  let d1 : Data := ⟨r1, Function.update d.stacks 3 a⟩
  change Eval _ t1 d d1 at h1
  have hv1 : ArithmeticCalls.Valid productPorts d1 := by
    constructor
    · simp [ productPorts, d1, hempty 4 (by decide)]
    · intro i
      have hi : work i ≠ (3 : Fin 12) := squarePorts.work_ne_out i
      change (Function.update d.stacks 3 a) (work i) = []
      rw [Function.update_noteq hi]
      exact hempty (work i) (hwork i)
  obtain ⟨t2, r2, b, h2, hb, hlb, ht2⟩ := ArithmeticCalls.multiplyAt_eval productPorts d1 hv1
  let d2 : Data := ⟨r2, Function.update d1.stacks 4 b⟩
  change Eval _ t2 d1 d2 at h2
  let d3 : Data := ⟨readRegs d2.regs 0 1 none, Function.update d2.stacks 3 []⟩
  have h3 : Eval (clearCmd 3) (2 * a.length + 3) d2 d3 := by
    simpa [d2, d1] using clear_eval 3 d2
  have hs3 : d3.stacks = Function.update d.stacks 4 b := by
    funext i
    by_cases hi : i = 3
    · subst i; simp [d3, d2, d1, hempty 3 (by decide)]
    · by_cases hi4 : i = 4
      · subst i; simp [d3,d2,d1]
      · simp [d3,d2,d1,hi,hi4]
  have h4 := ArithmeticCalls.copyAt_eval (2 : Fin 12) 5 11 d3
    (by decide) (by decide) (by decide)
    (by simp [hs3, hempty 5 (by decide)])
    (by simp [hs3, hempty 11 (by decide)])
  let d4 := ArithmeticCalls.afterCopy 2 5 d3
  change Eval _ _ d3 d4 at h4
  obtain ⟨d5, h5, hf, _, hs5, hz⟩ := SubexpGuardProgram.compare_call id comparePorts
    Function.injective_id comparePorts_injective d4
  let e := (StructuredProgram.Atom.bnot (0 : Fin 8) 0).eval d5
  have h6 : Eval (.base (.atom (.bnot 0 0))) 1 d5 e := .base (.atom _ _)
  refine ⟨t1 + (t2 + ((2 * a.length + 3) +
      ((7 * (d3.stacks 2).length + 5) +
      ((10 * max (d4.stacks (comparePorts 0)).length
        (d4.stacks (comparePorts 1)).length + 6) + 1)))), e,
    h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6)))), ?_, ?_, ?_⟩
  · funext i
    change d5.stacks i = d.stacks i
    by_cases hi5 : i = 5
    · subst i; simpa [comparePorts, hempty 5 (by decide)] using hz 0
    by_cases hi4 : i = 4
    · subst i; simpa [comparePorts, hempty 4 (by decide)] using hz 1
    have ho : ¬ ∃ j, comparePorts j = i := by
      rintro ⟨j,hj⟩; fin_cases j <;> simp_all [comparePorts]
    rw [hs5 i ho]
    simp [d4, ArithmeticCalls.afterCopy, hs3, hi4, hi5]
  · have ha' : BinaryArithmetic.toNat a = BinaryArithmetic.toNat (d.stacks 0)^2 := by
      simpa [squarePorts, pow_two] using ha
    have hb' : BinaryArithmetic.toNat b = BinaryArithmetic.toNat a *
        BinaryArithmetic.toNat (d.stacks 1) := by
      simpa [productPorts, d1] using hb
    have hf' : d5.regs 0 = true ↔ BinaryArithmetic.toNat (d.stacks 2) <
        BinaryArithmetic.toNat b := by
      simpa [comparePorts, d4, ArithmeticCalls.afterCopy, hs3] using hf
    change (!(d5.regs 0)) = true ↔ _
    rw [hb',ha'] at hf'
    cases hr : d5.regs 0 <;> simp [hr] at hf' ⊢ <;> omega
  · simp only [squarePorts] at hla ht1
    simp only [productPorts, d1, Function.update_same] at hlb ht2
    simp at hlb ht2
    simp [d4, ArithmeticCalls.afterCopy, hs3, comparePorts]
    have hm : max (d.stacks 2).length b.length ≤
        (d.stacks 2).length + b.length := by omega
    nlinarith

end SubexponentialSAT.SqrtLog.Setup.Guard

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Search

open BitProgram StructuredCalls
open CounterPrograms (value ripple)

abbrev Data := StructuredProgram.State 8 15

end SubexponentialSAT.SqrtLog.Setup.Search

namespace SubexponentialSAT.SqrtLog.Setup.Search

open BitProgram StructuredCalls
open CounterPrograms (value)

def iterationBound (initial : Data) (i : ℕ) : ℕ :=
  20000 * (i + (initial.stacks 1).length + (initial.stacks 2).length + i + 2)^2

end SubexponentialSAT.SqrtLog.Setup.Search

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticSearch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Generic correctness for the actual tested square-times-coefficient search.
The command is exactly `Setup.Search.command`; there is no arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

open BitProgram StructuredCalls
open CounterPrograms (value)
open Setup.Search (Data guardPorts iterationBound)

def Invariant (target : ℕ) (initial : _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.Search.Data) (i : ℕ) (d : _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Setup.Search.Data) : Prop :=
  value (d.stacks 0) = i ∧ value (d.stacks 12) = min i target ∧
  (d.stacks 0).length ≤ i ∧ (d.stacks 12).length ≤ i ∧
  ∀ j : Fin 15, j ≠ 0 → j ≠ 12 → j ≠ 13 → j ≠ 14 →
    d.stacks j = initial.stacks j

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic.Search

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SetupCleanup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Setup.Cleanup

open BitProgram StructuredCalls

abbrev Data (S : ℕ) := StructuredProgram.State 8 S

end SubexponentialSAT.SqrtLog.Setup.Cleanup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmeticSqrt
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual finite square-root calls. Search is bounded by the runtime input
value, which is charged explicitly; arbitrary padding is charged separately. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic

open BitProgram StructuredCalls
open CounterPrograms (value)

abbrev SqrtData := StructuredProgram.State 8 15

def SqrtLocalReady (d : SqrtData) : Prop :=
  ∀ i : Fin 15, i ≠ 2 → d.stacks i = []

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParameterArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Framed runtime square-root and quotient interfaces for parameter pipelines.
All program syntax is fixed by the port maps, never by the operand values. -/
namespace SubexponentialSAT.SqrtLog.LeafParameterArithmetic


open BitProgram StructuredCalls
open BinaryArithmetic (toNat)

def SqrtReady {S : ℕ} (p : SqrtPorts S) (d : Data S) : Prop :=
  d.stacks p.out = [] ∧ ∀ i, d.stacks (p.work i) = []

end SubexponentialSAT.SqrtLog.LeafParameterArithmetic

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseMastersProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical preparation of the shared clause-factor masters

Four preserved binary input words supply the declared variable count, chunk
width, field modulus, and chunk count. Copies of the three counts are converted
by the checked binary-to-unary program. The checked full-shape capture then
builds the padded-array shape. No desired shape is an input assumption.

The modulus-width shape is a physical copy of the modulus word: its consumers
use its length, not its bits. The other two copies supply the binary chunk
width and field modulus at the clause-family's own persistent ports.
-/

namespace SubexponentialSAT.SubexpClauseMastersProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 3 14

def write (d : Data) (dst : Fin 14) (word : List Bool) : Data :=
  ⟨zeroRegs, Function.update d.stacks dst word⟩

def copied (d : Data) (src dst : Fin 14) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks dst (d.stacks src)⟩

theorem embed_unary_input (src dst : Fin 14) (d : Data)
    (hd11 : dst ≠ 11) (hd12 : dst ≠ 12)
    (hd : d.stacks dst = []) (h12 : d.stacks 12 = []) :
    embedState id (unaryPorts dst) (copied d src 11)
      (CounterConversions.state (readRegs d.regs 0 1 none) (d.stacks src) []) =
      copied d src 11 := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id
    (unaryPorts_injective dst hd11 hd12)
  · intro i; rfl
  · intro i hi; rfl
  · intro i
    fin_cases i <;>
      simp [unaryPorts, copied, CounterConversions.state, hd11, hd, h12]
  · intro i hi; rfl

end SubexponentialSAT.SubexpClauseMastersProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramSerializationUnary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, preserving serialization of parameter words as unary loop counters.
This is the checked bit conversion already used for clause-factor masters. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

open BitProgram StructuredCalls BinaryArithmetic

abbrev Data := SubexpClauseMastersProgram.Data

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Serialization

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native runtime leaf parameter production, integer guards, and paid setup.
The former composition modules are import-only compatibility shims. -/


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramBankRoots -/

/-! A fixed ten-comparison bit guard. All operands are runtime binary words.
This module states their data relation separately from parameter production. -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard

open BitProgram StructuredCalls StructuredProgram BinaryArithmetic

abbrev check (j : Fin 10) : StructuredCalls.Cmd 9 20 :=
  .seq (.call (ProgramLinking.liftProgram SubexpGuardProgram.Compare.program regs (pair j)))
    (.base (.seq (.atom (.bnot 0 0)) (.atom (.band 8 8 0))))

/-- The list is fixed syntax; in the final guard it has exactly ten entries. -/
def checks : List (Fin 10) → StructuredCalls.Cmd 9 20
  | [] => .base .skip
  | j::js => .seq (check j) (checks js)

abbrev command : StructuredCalls.Cmd 9 20 :=
  .seq (.base (.atom (.set 8 true))) (checks allChecks)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit

open BitProgram StructuredCalls BinaryArithmetic Bank

/-- Values in ports untouched by the table are preserved exactly. -/
theorem result_value_frame (is : List Instr) (m : Model) (a : Fin 64)
    (ha : ∀ i ∈ is, output i≠a) : (result is m).val a=m.val a := by
  induction is generalizing m with
  | nil => rfl
  | cons i is ih =>
    rw [result,ih (next m i) (fun j hj => ha j (List.mem_cons_of_mem i hj))]
    simp [next,Ne.symm (ha i (List.mem_cons_self))]

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Circuit


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramLayout -/

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute

open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

abbrev check : Cmd 9 77 := liftCommand BitGuard.command 0 0 id guardStacks

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Execute


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuitBudget -/


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalCoreProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The multiplication and predecessor prefix of the actual interval-start
initializer. All widths refer to physical input words, including padding. -/

namespace SubexponentialSAT.SubexpIntervalCoreProgram

open BitProgram StructuredCalls BinaryArithmetic

attribute [local simp] Fin.coe_ofNat_eq_mod

def state (r : Regs) (w : Words) : Data :=
  ⟨r, fun i => if h : i.val < 10 then w ⟨i.val, h⟩ else []⟩

@[simp] theorem state_port (r : Regs) (w : Words) (i : Fin 10) :
    (state r w).stacks (port i) = w i := by simp [state, port]

@[simp] theorem state_regs (r : Regs) (w : Words) : (state r w).regs = r := rfl

abbrev copyCmd (a b : Fin 10) : Cmd 8 32 :=
  ArithmeticExpressionSupport.copyCmd (port a) (port b) 16

def predPorts (i : Fin 10) : CounterForPrograms.Ports 8 32 where
  register := ⟨fun j => ⟨j.val, by omega⟩, by
    intro a b h
    exact Fin.ext (congrArg (fun j : Fin 8 => j.val) h)⟩
  counter := port i
  scratch := 15
  counter_ne_scratch := by
    intro h
    have := congrArg Fin.val h
    simp only [] at this
    omega

abbrev predCmd (i : Fin 10) : Cmd 8 32 := CounterPredProgram.predCmd (predPorts i)

def arithmeticPorts (a b o : Fin 10) (hoa : o ≠ a) (hob : o ≠ b) :
    ArithmeticCalls.Ports 32 where
  left := port a
  right := port b
  out := port o
  work := ⟨fun j => ⟨10 + j.val, by omega⟩, by
    intro i j h
    apply Fin.ext
    have := congrArg Fin.val h
    dsimp at this
    omega⟩
  out_ne_left := by intro h; exact hoa (Fin.ext (congrArg (fun j : Fin 32 => j.val) h))
  out_ne_right := by intro h; exact hob (Fin.ext (congrArg (fun j : Fin 32 => j.val) h))
  work_ne_left := by
    intro i h
    have hv := congrArg Fin.val h
    change 10 + i.val = a.val at hv
    omega
  work_ne_right := by
    intro i h
    have hv := congrArg Fin.val h
    change 10 + i.val = b.val at hv
    omega
  work_ne_out := by
    intro i h
    have hv := congrArg Fin.val h
    change 10 + i.val = o.val at hv
    omega

abbrev multiplyCmd (a b o : Fin 10) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.multiplyAt (arithmeticPorts a b o hoa hob)

abbrev addCmd (a b o : Fin 10) (hoa : o ≠ a) (hob : o ≠ b) : Cmd 8 32 :=
  ArithmeticCalls.addAt (arithmeticPorts a b o hoa hob)

abbrev command : Cmd 8 32 :=
  .seq (copyCmd 0 4) (.seq (predCmd 4)
    (.seq (copyCmd 1 5) (.seq (predCmd 5)
      (.seq (multiplyCmd 5 4 6 (by decide) (by decide))
        (.seq (multiplyCmd 2 0 7 (by decide) (by decide))
          (addCmd 0 0 8 (by decide) (by decide)))))))

end SubexponentialSAT.SubexpIntervalCoreProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalFinishProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual long division and scratch cleanup for the interval initializer. -/

namespace SubexponentialSAT.SubexpIntervalFinishProgram

open BitProgram StructuredCalls BinaryArithmetic SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

def divisionState (r : Regs) (w : Words) (remainder numerator : List Bool) : Data :=
  ⟨r, Function.update (Function.update (state r w).stacks 15 numerator) 10 remainder⟩

@[simp] theorem divisionState_regs (r : Regs) (w : Words) (rem num : List Bool) :
    (divisionState r w rem num).regs = r := rfl

@[simp] theorem divisionState_ten (r : Regs) (w : Words) (rem num : List Bool) :
    (divisionState r w rem num).stacks 10 = rem := by simp [divisionState]

abbrev divisionCmd : Cmd 8 32 :=
  .seq (ArithmeticExpressionSupport.copyCmd (port 9) 15 16)
    (.seq (.call (ProgramLinking.liftProgram
      ModularQuotientPrograms.quotientProgram id quotientPorts))
      (ArithmeticExpressionSupport.clearCmd 10))

def clearWords : List (Fin 10) → Cmd 8 32
  | [] => .base .skip
  | i :: is => .seq (ArithmeticExpressionSupport.clearCmd (port i)) (clearWords is)

abbrev cleanup : Cmd 8 32 := clearWords [4, 5, 6, 7, 8, 9]

end SubexponentialSAT.SubexpIntervalFinishProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIntervalStartProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical binary initialization of the centered interval start

Three preserved input words encode r, Q, and R on ports 0, 1, and 2.
The fixed program computes ((Q-1)*(r-1)-R*r)/(2*r) using saturated
predecessors, products, saturated subtraction, and binary long division.
Only output port 3 differs on return; ports 4 through 31 are empty again.
-/

namespace SubexponentialSAT.SubexpIntervalStartProgram

open BitProgram StructuredCalls BinaryArithmetic
open SubexpIntervalCoreProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev subtractionCmd : Cmd 8 32 :=
  .call (ProgramLinking.liftProgram SaturatingSubtractionProgram.program id subtractionPorts)

abbrev command : Cmd 8 32 :=
  .seq SubexpIntervalCoreProgram.command
    (.seq subtractionCmd
      (.seq SubexpIntervalFinishProgram.divisionCmd SubexpIntervalFinishProgram.cleanup))

def program := compiled command (0 : Fin 32) 3

end SubexponentialSAT.SubexpIntervalStartProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramInterval
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval


open BitProgram StructuredCalls BinaryArithmetic Bank Circuit

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev intervalAt : Cmd 8 77 :=
  .call (ProgramLinking.liftProgram SubexpIntervalStartProgram.program id ports)

end SubexponentialSAT.SqrtLog.LeafParametersProgram.Interval

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid metadata exports. These commands touch only their destination and
three working registers; binary sources and all scratch words are restored. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := State 40 768
abbrev Code := Cmd 40 768

def payload (f : Field) (a : Data) : List Bool :=
  if f.unary then List.replicate (BinaryArithmetic.toNat (a.stacks f.src)) true else a.stacks f.src

def fieldState (f : Field) (a : Data) : Data :=
  if f.unary then embedState regs (ports f) a
    (SubexpClauseMastersProgram.write (projectState regs (ports f) a) 1 (payload f a))
  else SubexpScanPrimitives.afterCopy a f.src f.dst 0 1

def fieldCost (f : Field) (a : Data) : ℕ :=
  if f.unary then Serialization.unaryCopyBound (a.stacks f.src)+1
  else 7*(a.stacks f.src).length+5

def Scratch (a : Data) : Prop :=
  a.stacks 659=[] ∧ a.stacks 660=[] ∧ a.stacks 661=[] ∧ a.stacks 679=[]

def finalState : List Field → Data → Data
  | [],a => a
  | f::fs,a => finalState fs (fieldState f a)
def budget : List Field → Data → ℕ
  | [],_ => 0
  | f::fs,a => fieldCost f a+budget fs (fieldState f a)
def Ready : List Field → Data → Prop
  | [],_ => True
  | f::fs,a => f.Good ∧ a.stacks f.dst=[] ∧ Scratch a ∧ Ready fs (fieldState f a)

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExportsTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def OutputEmpty (a : Data) : Prop := ∀ i, a.stacks (destination i)=[]

def exportState (a : Data) : Data := finalState fields a
def exportBudget (a : Data) : ℕ := (fields.map (fun f => fieldCost f a)).sum

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramExports
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native cache preparation, persistent metadata export, and bank restoration.
The guard register is framed. Unary cache tapes are cleared after copying so
ring setup again receives the ordinary binary parameter model. -/
namespace SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports
open BitProgram StructuredCalls BinaryArithmetic Bank Circuit
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

def clearCommand : Code := BankRoutines.clearCmd 679 0 1 clearPorts

end
end SubexponentialSAT.SqrtLog.LeafParametersProgram.Exports

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClauseCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the clauses in the actual emitted leaf. Both the preserving record
scan and unary-to-binary conversion are fixed native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 8 16

def data (regs : Fin 8 → Bool) (formula unary binary : List Bool) : Data :=
  ⟨regs,![[],formula,unary,[],[],[],[],[],[],[],[],[],[],[],[],binary]⟩

abbrev convert : Cmd 8 16 := .call (ProgramLinking.liftProgram
  LeafStatisticsProgram.Binary.program binaryRegisters binaryStacks)

end SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Code := Cmd 16 320

def copy (src dst : Fin 320) : Code :=
  .call (StackRoutines.copyProgram src dst 318 (0 : Fin 16) 1)


abbrev Data := State 16 320

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One closed native count-recovery table: Hermite reconstruction over the
computed ring, integer readback, and reclamation of the two CRT entry caches.
Node-jet production and its semantic theorem are composed at the caller. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Count

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 40 768

end SubexponentialSAT.SqrtLog.LeafProgram.Count

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsSemanticsArity
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem residual_mem (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) (v : Free mask) :
    v ∈ residualScope scopes mask e ↔ v.val.val ∈ scopes.get e := by
  simp [residualScope, remainingScope]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingCoefficientLiftProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed scanner widens consecutive two-bit coefficients using a runtime
width tape. The original width is preserved, and all bit movement is paid. -/


/-! Exact byte bridge from canonical F3 coefficients to the supplied-polynomial
ring model. The program itself has no degree or width parameter. -/


/-! Search-to-table ABI. The search has 22 registers and 28 stacks. In particular,
stack24 may contain unread candidates and is outside this adapter's ports. -/
namespace SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev SearchData := State 22 28

end SubexponentialSAT.SqrtLog.RingCoefficientLiftProgram

end OAI.Algorithms
end


