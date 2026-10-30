-- Prove2me | Definitions.Def_OAIQ081S051
-- name    : OAIQ081S051
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:40:04.657993+00:00
-- url     : https://prove2.me/theorems/745cc49a-290e-4701-9aa6-6ec59dc2015a
-- title:
--   Definitions bundle OAIQ081S051 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 158 declarations of OpenAI's Lean: 148 definitions, 1 inductive type or structure and 9 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor.Counter.counterResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.EarlyThreshold.runtimeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant.pad`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold.Contract`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.literalBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.clauseLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.fetchLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.openWeighted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.productAdapter`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowCommand`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowLoop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.weightedClauseStep`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows.openWeighted`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.canonicalDecode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.canonicalLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.clear`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalDictionary`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.literalFetch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.lookupCall`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.parsePayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.unframeResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.encodedClauses`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Expansion.originalClause`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Frame.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Frame.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Frame.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loopBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.uniformBudget`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.clearScan`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.fetch`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.fetchProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.ports`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.readSelected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.skip` and 109 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructor`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramPair`, `SubexponentialSAT_SqrtLog_EarlyThreshold`, `SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative`, `SubexponentialSAT_SqrtLog_HashCircuitProgramCanonical`, `SubexponentialSAT_SqrtLog_HashCircuitProgramConstant`, `SubexponentialSAT_SqrtLog_HashCircuitProgramControl`, `SubexponentialSAT_SqrtLog_HashCircuitProgramDynamicFold`, `SubexponentialSAT_SqrtLog_HashCircuitProgramFrame`, `SubexponentialSAT_SqrtLog_HashCircuitProgramLookup`, `SubexponentialSAT_SqrtLog_HashCircuitProgramMeaning`, `SubexponentialSAT_SqrtLog_HashCircuitProgramPayload`, `SubexponentialSAT_SqrtLog_HashCircuitProgramRows`, `SubexponentialSAT_SqrtLog_HashFamilyPayloadValid`, `SubexponentialSAT_SqrtLog_HashInputProgramCandidate`, `SubexponentialSAT_SqrtLog_HashInputProgramExpansion`, `SubexponentialSAT_SqrtLog_HashInputProgramFrame`, `SubexponentialSAT_SqrtLog_HashInputProgramLookup`, `SubexponentialSAT_SqrtLog_HashInputProgramLoop`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal`, `SubexponentialSAT_SqrtLog_HashInputProgramOrigin`, `SubexponentialSAT_SqrtLog_HashInputProgramSource`, `SubexponentialSAT_SqrtLog_HashScopeProgramExtract`, `SubexponentialSAT_SqrtLog_HashScopeProgramFlatten`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedFrame`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawFrame`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawLoop`, `SubexponentialSAT_SqrtLog_HashScopeProgramScopeOnly`, `SubexponentialSAT_SqrtLog_HashSelectProgramCore`, `SubexponentialSAT_SqrtLog_HashSelectProgramGenerate`, `SubexponentialSAT_SqrtLog_HashSelectProgramLoop`, `SubexponentialSAT_SqrtLog_HeadScatterProgram`, `SubexponentialSAT_SqrtLog_HeadScatterProgramInit`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramMass`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost`, `SubexponentialSAT_SqrtLog_IrreducibleSearchEnumerationCost`, `SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram`, `SubexponentialSAT_SqrtLog_LeafProgramHash`, `SubexponentialSAT_SqrtLog_LeafProgramRecords`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeProgramClip`, `SubexponentialSAT_SqrtLog_SquarefreeProgramCompare`, `SubexponentialSAT_SqrtLog_SquarefreeProgramErase`, `SubexponentialSAT_SqrtLog_SquarefreeProgramJoin`, `SubexponentialSAT_SqrtLog_SquarefreeProgramLess`, `SubexponentialSAT_SqrtLog_SquarefreeProgramLookup`, `SubexponentialSAT_SqrtLog_SquarefreeProgramNat`, `SubexponentialSAT_SqrtLog_SquarefreeProgramRead`, `SubexponentialSAT_SqrtLog_SquarefreeProgramReplace`, `SubexponentialSAT_SqrtLog_SquarefreeProgramScan`, `SubexponentialSAT_SqrtLog_SquarefreeProgramStorage`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpConvolutionIteration`, `SubexponentialSAT_SubexpIncidenceSlotProgram`, `SubexponentialSAT_SubexpRecordScan`, `SubexponentialSAT_SubexpSetupStorage`, `SubexponentialSAT_Subexp_SelectorProgram`, `SubexponentialSAT_Subexp_SupportSelectionPrimitives`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S023`, `OAIQ081S024`, `OAIQ081S025`, `OAIQ081S026`, `OAIQ081S028`, `OAIQ081S029`, `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032` and `OAIQ081S034` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S069`, `OAIQ081S070`, `OAIQ081S071`, `OAIQ081S072`, `OAIQ081S073`, `OAIQ081S074`, `OAIQ081S075`, `OAIQ081S076`, `OAIQ081S077`, `OAIQ081S078`, `OAIQ081S079`, `OAIQ081S080` and `OAIQ081S081`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S023
import Definitions.Def_OAIQ081S024
import Definitions.Def_OAIQ081S025
import Definitions.Def_OAIQ081S026
import Definitions.Def_OAIQ081S028
import Definitions.Def_OAIQ081S029
import Definitions.Def_OAIQ081S030
import Definitions.Def_OAIQ081S031
import Definitions.Def_OAIQ081S032
import Definitions.Def_OAIQ081S034

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramConstructor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Width-generic padded constant and linear polynomial constructors. The
physical instruction table is unchanged; its zero-cell width and polynomial
length are runtime tapes. All output construction and cleanup is charged. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
namespace Counter
open SubexponentialSAT.SubexpLinearFactorProgram
def counterResult (d : Data) (D W : ℕ) (low high : List Bool)
    (regs : Fin 16 → Bool) : Data :=
  ⟨regs, Function.update (Function.update d.stacks 108 []) 102 (paddedBits W low high D)⟩

end Counter
open SubexponentialSAT.SubexpConvolutionControl

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Constructor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native arbitrary-width coefficient multiply-and-accumulate. The high
workspace computes the ring product; the low workspace updates one encoded
array cell. Its runtime index scans and all transfers are explicitly paid. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives
open SubexponentialSAT.SubexpConvolutionControl SubexponentialSAT.SubexpConvolutionPair
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Data := SubexponentialSAT.SubexpConvolutionControl.Data

end SubexponentialSAT.SqrtLog.DensePolynomialProgram.Pair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_EarlyThreshold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A paid, fixed native producer of the early high-incidence threshold.
The source is the original ambient count in bank slot 0.  It is never replaced
by the residual count or by the later block-size parameter. -/

namespace SubexponentialSAT.SqrtLog.EarlyThreshold

open BitProgram StructuredCalls BinaryArithmetic
open LeafParametersProgram.Bank LeafParametersProgram.Circuit


def runtimeBound (ambient : List Bool) : ℕ :=
  300001 * (ambient.length + Asymptotic.L (BinaryArithmetic.toNat ambient) + 20)^3

end SubexponentialSAT.SqrtLog.EarlyThreshold

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRecordScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control selection of serialized coefficient records

The inner record body is `frame key ++ frame coefficient`. All execution
claims below are traces of fixed Boolean-register/stack instruction tables.
-/

namespace SubexponentialSAT.SubexpRecordScan

open BitProgram StructuredProgram StructuredCalls

/-- The existing frame parser relocated to two named ports. -/
abbrev parseFrame (src dst : Fin 6) : Program 5 6 7 :=
  ProgramLinking.liftProgram ParserProgram.frameProgram lowRegs (twoPorts src dst)

/-- Enter the existing raw-frame routines, rather than their tagged-list entry. -/
abbrev rawSkip : Program 3 1 11 := {ExecCNFRecords.skipProgram with entry := 4}
abbrev rawCopy : Program 2 3 16 := {ExecCNFRecords.copyProgram with entry := 4}

abbrev skipPayload : Program 5 6 11 :=
  ProgramLinking.liftProgram rawSkip skipRegs onlyInput

abbrev copyPayload : Program 5 6 16 :=
  ProgramLinking.liftProgram rawCopy lowRegs payloadPorts

/-- Conditional payload selection keeps the entire frame and its boundary. -/
abbrev selectPayload : StructuredCalls.Cmd 5 6 :=
  .ite 4 (.call copyPayload) (.call skipPayload)

abbrev compareKeys : Program 5 6 10 :=
  ProgramLinking.liftProgram ExecClauseCost.bitEqualityProgram id (twoPorts 1 3)

/-- The entire inner-record selector is one fixed structured program.
Every call here is a fixed finite instruction table. -/
abbrev oneRecord : StructuredCalls.Cmd 5 6 :=
  .seq (.call (parseFrame 0 1))
    (.seq (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (.seq (.call compareKeys)
        (.seq (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
          (.seq (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1)) selectPayload))))

end SubexponentialSAT.SubexpRecordScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-code lookup with fallback for local read plans

The table is a raw sequence of framed key/payload pairs. The query and table
are runtime bit strings. The program reuses the verified key comparison and
record parsing routines, retaining the first matching payload.
-/

namespace SubexponentialSAT.Subexp.SelectorProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev body : Cmd 5 6 := .seq oneRecord continueOrStop
abbrev scan : Cmd 5 6 := .while 1 body

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive dictionary lookup. Dictionary normalization guarantees
unique keys. All key and coefficient bits are scanned by the existing finite
record program; key width, coefficient width and dictionary length are runtime
data and do not affect the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

abbrev dictionaryLookup : Cmd 5 6 :=
  .seq (.base (.atom (.set 4 false)))
    (.seq SubexponentialSAT.Subexp.SelectorProgram.peek SubexponentialSAT.Subexp.SelectorProgram.scan)

def dictionaryLookupProgram := compiled dictionaryLookup 0 5

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Native literal parsing and hash-specific incidence lookup

A literal payload is `key ++ [positive]`; the existing record parser supplies
its reversal. The key selects a variable in a physically selected hash slice.
The fixed command pops the polarity, copies and scans the saved incidence
slice, returns its framed dictionary payload, and reclaims both scan and query.
There is no circuit-evaluation instruction and no scope truth table.
-/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev lookupCall : Cmd 6 7 :=
  liftCommand Squarefree.Program.dictionaryLookup 0 5 Fin.castSucc Fin.castSucc

abbrev clear (src : Fin 7) : Cmd 6 7 :=
  .call (StackRoutines.clearProgram src (0 : Fin 6) 1)

/-- One fixed finite command, independent of variable indices, hash-row width,
coefficient widths, and the number of entries in the selected incidence slice. -/
abbrev literalFetch : Cmd 6 7 :=
  .seq popLiteral (.seq (copy 6 0 1) (.seq lookupCall (.seq (clear 0) (clear 2))))

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unframing of the selected incidence dictionary. A successful literal
lookup returns the actual forward dictionary bits on stack5. The success guard
handles a missing key without invoking a parser on an absent frame. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev parsePayload : Cmd 6 7 :=
  liftCommand (.call (parseFrame 5 0)) 5 0 Fin.castSucc Fin.castSucc

abbrev unframeResult : Cmd 6 7 :=
  .ite 4 (.seq parsePayload (transfer 0 5)) (.base .skip)

/-- The lookup itself and successful unframing are both fixed native code. -/
abbrev literalDictionary : Cmd 6 7 := .seq literalFetch unframeResult

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramCanonical
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct native incidence evaluation from original unary CNF literal records.
This module composes the paid literal decoder with the paid dictionary lookup;
no preprocessing assumption converts literal numbers into variable keys. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev canonicalDecode : Cmd 6 7 :=
  liftCommand Decode.programCommand 0 0 decodeRegisters decodeStacks

abbrev canonicalLiteral : Cmd 6 7 := .seq canonicalDecode literalDictionary

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical opening of an inline weighted clause record. The record payload is
`frame coefficient ++ encodeList encodeNat clause`. It is supplied reversed by
the outer record parser. Both the weight frame and the literal list are traversed
by fixed bit programs; source clause IDs are resolved by the upstream producer. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev openWeighted : Cmd 5 6 := .seq transfer (.call (parseFrame 2 5))

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev fetchLiteral : Cmd 8 96 :=
  liftCommand canonicalLiteral 2 5 literalRegisters literalStacks

abbrev openWeighted : Cmd 8 96 :=
  liftCommand Rows.openWeighted 0 2 rowRegisters rowStacks

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramRecords
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured physical folds over sparse-hash records

This module specializes the audited framed-record iterator to an accumulator
fold which visits every record. The callback is an actual finite `Cmd`; its
local execution contract remains explicit. `foldProgram_run` concerns primitive
Boolean-register/stack transitions, not an operation counter or semantic oracle.
The same program shape handles clause-literal products, sparse weighted sums,
coefficient-array maps, and support-key dictionary scans.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {A : Type*}

abbrev foldCommand (ports : Ports r s) (step : Cmd r s) : Cmd r s :=
  iterate ports step

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clear (src : Fin 96) : Cmd 8 96 :=
  .call (StackRoutines.clearProgram src (0 : Fin 8) 1)

def literalPorts : RecordPrograms.Ports 8 96 :=
  ⟨0,1,2,63,58,by decide,by decide,by decide,by decide⟩
def rowPorts : RecordPrograms.Ports 8 96 :=
  ⟨0,1,2,64,66,by decide,by decide,by decide,by decide⟩

/-- The polarity branch is taken before arithmetic may reuse the registers. -/
abbrev literalStep (arith : Arithmetic) : Cmd 8 96 :=
  .seq fetchLiteral
    (.seq (.ite 5 arith.oneMinus (.base .skip))
      (.seq arith.multiply recordReturn))

abbrev clauseLoop (arith : Arithmetic) : Cmd 8 96 :=
  RecordPrograms.iterate literalPorts (literalStep arith)

/-- Each clause starts from a physical preserving copy of the cached one. -/
abbrev weightedClauseStep (arith : Arithmetic) : Cmd 8 96 :=
  .seq openWeighted
    (.seq (copy 69 67 70)
      (.seq (clauseLoop arith) (.seq arith.scaleAdd recordReturn)))

/-- One fixed dynamic outer loop, independent of the number of clauses,
literals, hash entries, variable count and numeric precisions. -/
abbrev rowLoop (arith : Arithmetic) : Cmd 8 96 :=
  RecordPrograms.iterate rowPorts (weightedClauseStep arith)

abbrev rowCommand (arith : Arithmetic) : Cmd 8 96 :=
  .seq (clear 68) (rowLoop arith)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramCompare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Destructive key comparison with query preservation and complete scratch
cleanup, as a fixed primitive subroutine for dictionary replacement. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev compareDictionaryKey : Cmd 5 6 :=
  .seq (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
    (.seq (.call compareKeys)
      (.seq (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
        (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1))))

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Port relocation and paid bit-copy primitives for the dictionary builder. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

abbrev storageCall (c : Cmd 5 6) : Cmd 5 7 := liftCommand c 0 5 id Fin.castSucc

abbrev storageClear (src : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.clearProgram src (0 : Fin 5) 1)

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramErase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete one-record deletion for sparse coefficient dictionaries. The
selected key is saved before comparison; retained records are emitted intact. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev emitSaved : Cmd 5 7 := .call
  (ProgramLinking.liftProgram frameEmitProgram frameRegPorts frameStackPorts)

abbrev eraseKeep : Cmd 5 7 := .seq (storageCall (.call copyPayload)) emitSaved

abbrev eraseDrop : Cmd 5 7 := .seq (storageCall (.call skipPayload)) (storageClear 6)

abbrev eraseBranch : Cmd 5 7 := .ite 4 eraseDrop eraseKeep

abbrev eraseOne : Cmd 5 7 :=
  .seq (storageCall (.call (parseFrame 0 1)))
    (.seq (storageCopy 1 6 4) (.seq (storageCall compareDictionaryKey) eraseBranch))

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-sized dictionary deletion. One fixed loop visits every encoded
record and retains every nonmatching record, reversing record order. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev erasePeek : Cmd 5 7 := storageCall SubexponentialSAT.Subexp.SelectorProgram.peek

abbrev eraseLoop : Cmd 5 7 := .while 1 (.seq eraseOne erasePeek)

abbrev eraseScan : Cmd 5 7 := .seq erasePeek eraseLoop

def eraseScanProgram := compiled eraseScan 0 5

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramReplace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual dictionary replacement: delete all old matching keys, then prepend
one supplied coefficient. This is the storage phase of additive insertion;
the coefficient addition itself is a separately measured ring operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev replaceTail : Cmd 5 8 := .call
  (ProgramLinking.liftProgram prependRecordProgram replaceRegPorts replaceStackPorts)

abbrev dictionaryReplace : Cmd 5 8 := .seq
  (.call (ProgramLinking.liftProgram eraseScanProgram id Fin.castSucc)) replaceTail

def dictionaryReplaceProgram := compiled dictionaryReplace 0 5

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev clear (src : Fin 27) : Cmd 8 27 :=
  .call (clearProgram src (0 : Fin 8) 1)

abbrev lookup : Cmd 8 27 := .call
  (ProgramLinking.liftProgram Squarefree.Program.dictionaryLookupProgram smallRegs lookupStacks)
abbrev replace : Cmd 8 27 := .call
  (ProgramLinking.liftProgram Squarefree.Program.dictionaryReplaceProgram smallRegs replaceStacks)
abbrev parseOld : Cmd 8 27 := .call
  (ProgramLinking.liftProgram (SubexponentialSAT.SubexpRecordScan.parseFrame 0 1) parseRegisters parseStacks)

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramNat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive unary-field reader used by encoded sparse-key joins.
The unary magnitude affects execution time, never the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev readNat {s : ℕ} (src dst : Fin s) : Cmd 5 s :=
  .call (ProgramLinking.liftProgram ParserProgram.natProgram natRegs (natPorts src dst))

abbrev joinNat : Cmd 5 3 :=
  .seq (readNat 0 2) (.seq (readNat 1 2) (.base (.atom (.push 2 0))))

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev readFrame8 {s : ℕ} (src dst : Fin s) : Cmd 8 s :=
  .call (ProgramLinking.liftProgram ParserProgram.frameProgram frameReadRegs (frameReadPorts src dst))

abbrev takeDictionaryRecord : Cmd 8 28 :=
  .seq (readFrame8 27 16) (.seq (readFrame8 27 18) (transfer8 18 17))

end SubexponentialSAT.SqrtLog.Squarefree.Program

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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev clearCoefficient : Cmd 8 28 := .call (StackRoutines.clearProgram 17 0 1)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control Cartesian tuple generation

Alphabet words, tuple payloads, and iteration depths are stack data.  The
instruction tables below do not depend on any of their lengths.
-/

namespace SubexponentialSAT.Subexp.TupleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev escapedState {r s : ℕ} (p : RecordPrograms.Ports r s) (a : State r s) : State r s :=
  ⟨readRegs a.regs p.tag p.present none,
    Function.update (Function.update a.stacks p.source []) p.payload
      (escaped (a.stacks p.source).reverse ++ a.stacks p.payload)⟩

abbrev pushedState {r s : ℕ} (dst : Fin s) (value : Fin r) (b : Bool)
    (a : State r s) : State r s :=
  ⟨Function.update a.regs value b, Function.update a.stacks dst (b :: a.stacks dst)⟩

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

theorem powerRows_length (alphabet rows : Records) (n : ℕ) :
    (powerRows alphabet n rows).length = rows.length * alphabet.length ^ n := by
  revert rows
  refine Nat.rec (motive := fun n => ∀ rows : Records,
    (powerRows alphabet n rows).length = rows.length * alphabet.length ^ n) ?_ ?_ n
  · intro rows
    simp [powerRows]
  · intro n ih rows
    calc
      (powerRows alphabet (n + 1) rows).length =
          (powerRows alphabet n (cartesianOutput rows alphabet)).length := rfl
      _ = (cartesianOutput rows alphabet).length * alphabet.length ^ n := ih _
      _ = (rows.length * alphabet.length) * alphabet.length ^ n := by
        rw [cartesianOutput_length]
      _ = rows.length * alphabet.length ^ (n + 1) := by
        rw [pow_succ]
        ac_rfl

theorem generated_count (alphabet : Records) (n : ℕ) :
    (powerRows alphabet n [[]]).length = alphabet.length ^ n := by
  simpa using powerRows_length alphabet [[]] n

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLess
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary comparison with explicit residual-length bounds and paid
cleanup. Register 4 is a caller-owned Boolean saved across this operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.CodeSearchProgram

abbrev lessAt {s : ℕ} (src dst : Fin s) : Cmd 5 s :=
  .call (ProgramLinking.liftProgram unaryLessProgram lessRegs (natPorts src dst))

abbrev clearAt {s : ℕ} (src : Fin s) : Cmd 5 s :=
  .call (StackRoutines.clearProgram src (0 : Fin 5) 1)

abbrev lessClear {s : ℕ} (src dst : Fin s) : Cmd 5 s :=
  .seq (lessAt src dst) (.seq (clearAt src) (clearAt dst))

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramClip
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive clipping for sparse keys. The key and both unary limits
are disposable inputs; all four local stacks are empty on return. Callers may
keep master copies outside these ports. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev clipField (budget : Fin 4) : Cmd 5 4 :=
  .seq (readNat 0 3) (lessClear 3 budget)

abbrev clipIndex : Cmd 5 4 :=
  .seq (clipField 1) (.seq (.base (.atom (.copy 4 3)))
    (.seq (clipField 2) (.seq (.base (.atom (.band 4 4 3))) (clearAt 0))))

def clipIndexProgram := compiled clipIndex 0 0

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramJoin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single finite primitive program joins encoded sparse indices. Unary
exponents are added by scanning their fields; support bits are unioned by the
fixed OR scanner. The complete output is reversed for direct record emission. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev indexJoin : Cmd 5 3 :=
  .seq joinNat (.seq joinNat (.call maskUnionProgram))

def indexJoinProgram := compiled indexJoin 0 2

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev clear (src : Fin 15) : Cmd 8 15 :=
  .call (clearProgram src (0 : Fin 8) 1)

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev join : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram Program.indexJoinProgram regs5 joinPorts)

abbrev clip : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram Program.clipIndexProgram regs5 clipPorts)

abbrev emit : Cmd 8 15 :=
  .call (ProgramLinking.liftProgram Program.prependRecordProgram regs3 emitPorts)

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev prepare : Cmd 8 15 :=
  .seq (Program.readFrame8 0 5) (.seq (Program.readFrame8 0 6)
    (.seq (Program.transfer8 5 8) (copy 1 9)))

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finish : Cmd 8 15 := .ite 4 emit (.seq (clear 10) (clear 6))

abbrev step : Cmd 8 15 := .seq prepare (.seq join (.seq prepareClip (.seq clip finish)))

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev loop : Cmd 8 15 := .while 1 (.seq step peek)
abbrev scan : Cmd 8 15 := .seq peek loop

def scanProgram := compiled scan 0 4

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Base stage. -/
/-! Fixed physical ABI for scaling all coefficients in a sparse dictionary.
The low 32 stacks are the common coefficient-ring service. The eight high
stacks hold source, reversed output, scalar, key, coefficient staging, frame
staging, final output, and a preserved copy of the unary degree. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev emitFrame (src : Fin 40) : Cmd 8 40 :=
  .call (ProgramLinking.liftProgram Program.frameEmitProgram frameRegs (framePorts src))

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev prepare : Cmd 8 40 :=
  .seq (Program.readFrame8 32 35)
    (.seq (Program.readFrame8 32 36)
      (.seq (Program.transfer8 36 9) (.seq (copy 34 8) (copy 39 11))))

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Emit stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- Emit one result into a reversed stream. Reversing the complete stream once
at the end restores the original record order. -/
abbrev emit : Cmd 8 40 :=
  .seq (Program.transfer8 0 36) (.seq (emitFrame 35)
    (.seq (Program.transfer8 37 33) (.seq (emitFrame 36) (Program.transfer8 37 33))))

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

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

abbrev keyMap : Cmd 8 56 := .call (ProgramLinking.liftProgram Squarefree.KeyMapProgram.scanProgram id keyPorts)

abbrev read : Cmd 8 56 := .seq (Squarefree.Program.readFrame8 40 43)
  (.seq (Squarefree.Program.readFrame8 40 48) (transfer 48 44))

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Component: HashCircuitProgramArithmetic. All public namespaces and APIs are retained. -/


/-! Native arithmetic wiring for the hash interpreter. Scale and normalized
addition are fixed imported instruction tables. Product is wired separately
when the native product table is supplied by its implementation module. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Product's local ABI isA40, B41, result42, with B preserved. The copied
operands and native result are reclaimed after moving the result to67. -/
abbrev productAdapter (product : Cmd 8 96) : Cmd 8 96 :=
  .seq (copy 67 40 70)
    (.seq (copy 61 41 70)
      (.seq product
        (.seq (clear 67)
          (.seq (clear 61)
            (.seq (copy 42 67 70) (.seq (clear 42) (clear 41)))))))

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-! Component: HashCircuitProgram. All public namespaces and APIs are retained. -/


/-! The fixed native sparse-hash row instruction table. All arithmetic
components are now concrete native programs: there are no operation-valued
parameters in `command` or `program`. The complete serialized semantic and
primitive-time theorem must additionally discharge the local callback
contracts for this table; no such theorem is asserted merely by compilation. -/

/-! Component: HashCircuitProgramMemoryExtra. All public namespaces and APIs are retained. -/


/-! Component: HashCircuitProgramWeightedCallbacks. All public namespaces and APIs are retained. -/


/-! The two concrete weighted arithmetic adapters used by the hash evaluator.
The statements expose exact dictionary bytes and restoration of the common
arithmetic workspace. In particular they do not assume callback correctness. -/

/-! Component: HashCircuitProgramProduct. All public namespaces and APIs are retained. -/


/-! Concrete product callback refinement. Both sparse operands are copied from
persistent interpreter stacks into the real product program. The result is
copied back, and all temporary operands are physically reclaimed. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramConstant
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct a cached sparse constant from a shape word and a forward flat
coefficient. Zero support bits, key delimiters, reversal, record framing and
cleanup all execute on the native bit machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev pad : Cmd 8 6 := .call (ProgramLinking.liftProgram ModularPrograms.paddingProgram id padStacks)

abbrev command : Cmd 8 6 := .seq pad (.seq tag (.seq reverseCoefficient emit))
end SubexponentialSAT.SqrtLog.HashCircuitProgram.Constant

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramDynamicFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured physical record fold with accumulator-dependent cost. This
retains the actual fixed callback and parser; the cost recurrence can account
for changing sparse dictionary lengths without postulating a uniform bound. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {R A : Type*}

/-- A refinement relation may track the sparse accumulator and arbitrary
persistent machine context. The callback must consume its parsed payload. -/
abbrev Contract (p : Ports r s) (callback : Cmd r s) (encode : R → List Bool)
    (step : R → A → A) (cost : R → A → ℕ) (Rep : A → State r s → Prop) : Prop :=
  ∀ x a base, Rep a base → ∀ tail,
    ∃ n next, n ≤ cost x a ∧ Rep (step x a) next ∧
      Eval callback n (state p base false true false tail (encode x).reverse)
        (state p next false true false tail [])

end SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMeaning
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact pure result functions of the fixed native hash interpreter. The
execution proofs live in HashCircuitProgramInterpreter; no alternate evaluator
or operation oracle is introduced here. -/

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (u J : ℕ)

def literalBits {n : ℕ} (l : SAT.Literal (Fin n)) := Encoding.encodeNat (Encoding.literalCode l)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed-port binary argmin calls and a parser for unevaluated candidate
payloads. The scores are absent from the input encoding. All supplied commands
are actual finite programs; semantic scores are never atomic instructions. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def payloadPorts : RecordPrograms.Ports 8 9 where
  tag := 0
  present := 1
  found := 7
  source := 8
  payload := 0
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev parserCmd : Cmd 8 9 :=
  .seq (BinaryArgmin.atom (.pop 8 7 6))
    (.ite 7 (RecordPrograms.reader payloadPorts) (.base .skip))

def parserProgram := compiled parserCmd 8 0

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramGenerate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-depth tuple enumeration by the audited 83-label finite controller.
The selector reads the generator's existing framed queue directly: reversing
payload interpretation accounts for the parser's stack order without a free
array conversion. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp

@[simp] theorem generatedPayloads_length (alphabet : Records) (depth : ℕ) :
    (generatedPayloads alphabet depth).length = alphabet.length ^ depth := by
  simp [generatedPayloads, TupleProgram.generated_count]

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayloadValid
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily
open SubexponentialSAT.Subexp TupleProgram
open SubexponentialSAT.SubexpLiftRing (fixedBits)
open SubexponentialSAT.BinaryArithmetic (toNat)

@[simp] theorem generated_count (m width depth : ℕ) :
    (HashSelectProgram.generatedPayloads (alphabet m width) depth).length = (3 * m) ^ depth := by
  simp

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the agreed inline record payload: a framed flat ring
coefficient followed by the ORIGINAL canonical literal-list payload. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Frame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev emit : Cmd 3 3 := .call (ProgramLinking.liftProgram
  Squarefree.Program.frameEmitProgram id emitPorts)
abbrev command : Cmd 3 3 := .seq reverseWeight emit

def program := compiled command 0 1

end SubexponentialSAT.SqrtLog.HashInputProgram.Frame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramHash
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Sparse clause-circuit evaluation for one hash row

The input is a list of supplied nonzero coefficients and width-k clause lists.
The evaluator visits those lists directly; it never builds a truth table on the
union of the clause scopes. Counters include measured variable lookup and ring
callbacks. Their primitive realization is a separate obligation, not inferred
from these counters. `Algebra` also admits canonical truncated operations, whose
decoder need not be a homomorphism into the untruncated polynomial ring.
-/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open SubexponentialSAT.SubexpSymbolicCost

abbrev SparseRow (V C : Type*) := List (C × List (SAT.Literal V))

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical positional lookup in the ORIGINAL encoded clause list. The index
is a canonical natural field; all preceding records are scanned and discarded.
The master source is copied, preserved, and charged. No pre-expanded hash input
table is assumed. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev skip : Cmd 3 6 := .call
  (ProgramLinking.liftProgram ExecCNFRecords.skipProgram id (fun _ => (1 : Fin 6)))

abbrev skipLoop : Cmd 3 6 := .while 0 (.seq skip popIndex)

abbrev skipPrefix : Cmd 3 6 := .seq popIndex skipLoop

def ports : RecordPrograms.Ports 3 6 where
  tag := 0; present := 1; found := 2; source := 1; payload := 3
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

abbrev readSelected : Cmd 3 6 := .seq popTag (RecordPrograms.reader ports)

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete preserving, paid lookup of a source clause by its list position. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpScanPrimitives

abbrev clearScan : Cmd 3 6 := .call (StackRoutines.clearProgram 1 0 1)
abbrev fetch : Cmd 3 6 := .seq copySource (.seq skipPrefix
  (.seq readSelected (.seq clearScan forward)))

def fetchProgram := compiled fetch 2 5

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed raw-tuple assembler. The machine traverses raw digit bytes, not a
pre-expanded clause table. Each step looks up one ORIGINAL source clause and
emits its lifted coefficient plus unchanged canonical literal bytes. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def loopBudget (t d b ml : ℕ) (clauses : List (List Bool))
    (terms : List (Fin clauses.length × ZMod 3)) : ℕ :=
  3+(terms.map fun a => termBudget b ml clauses.length
    (Encoding.encodeList id clauses).length ((d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t)
    clauses[a.1.val].length+4).sum

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Public raw-input ABI and the uniform paid execution theorem. All control
tables are fixed independently of source size, raw tuple length and ring width.
Repeated source references and zero coefficients remain separate records. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def uniformBudget (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (count : ℕ) : ℕ :=
  3+count*(termBudget b modulus.length clauses.length (Encoding.encodeList id clauses).length
    ((d+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 t) (Encoding.encodeList id clauses).length+4)

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramOrigin
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact original-clause provenance for a raw tuple, including repetitions.
The integer lift is taken BEFORE the tuple terms are added; its reduction, not
its value in the thickened ring, equals the combined ternary selector row. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open scoped BigOperators
open LeafProgram

def rawRow {V : Type*} {m depth : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth) :
    SparseRow V (ZMod 3) :=
  List.ofFn fun j => (h.2 j, source (h.1 j))

@[simp] theorem rawRow_length {V : Type*} {m depth : ℕ}
    (source : Fin m → List (SAT.Literal V)) (h : HashFamily.Candidate m depth) :
    (rawRow source h).length=depth := by simp [rawRow]

def clausePayload {n : ℕ} (ls : List (SAT.Literal (Fin n))) : List Bool :=
  Encoding.encodeList (fun l => Encoding.encodeNat (Encoding.literalCode l)) ls

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramCandidate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The assembler receives exactly the selector's raw candidate bytes. Its
source is a serialized original formula, and its result is a produced inline
row, with every raw tuple occurrence retained. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def candidateTerms {m depth : ℕ} (h : HashFamily.Candidate m depth) :
    List (Fin m × ZMod 3) := List.ofFn fun j => (h.1 j,h.2 j)

end SubexponentialSAT.SqrtLog.HashInputProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramExpansion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact bytes and coefficient meaning at the raw-row/interpreter boundary.
The full extension dimension is D; the assembler parameter is D-1. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Expansion
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open HashCircuitProgram.Native
attribute [local simp] Fin.coe_ofNat_eq_mod

def encodedClauses {n : ℕ} (source : List (List (SAT.Literal (Fin n)))) : List (List Bool) :=
  source.map clausePayload

def originalClause {n : ℕ} (source : List (List (SAT.Literal (Fin n))))
    (i : Fin (encodedClauses source).length) : List (SAT.Literal (Fin n)) :=
  source[i.val]'(by simpa [encodedClauses] using i.isLt)

end SubexponentialSAT.SqrtLog.HashInputProgram.Expansion

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramExtract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical extraction of the literal-record bytes from one weighted raw
clause. Coefficient bytes are discarded even when the coefficient is zero. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Extract
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 3 6

def data (v p f : Bool) (source payload scan weight out tmp : List Bool) : Data :=
  ⟨ExecCNFRecords.regs v p f, ![source,payload,scan,weight,out,tmp]⟩

abbrev clear3 : Cmd 3 6 := .call (StackRoutines.clearProgram 3 0 1)

def weightPorts : RecordPrograms.Ports 3 6 :=
  ⟨0,1,2,2,3,by decide,by decide,by decide,by decide⟩

abbrev command : Cmd 3 6 := .seq move12 (.seq (RecordPrograms.reader weightPorts)
  (.seq clear3 (.seq move25 (.seq pop5 (.seq move54 finish)))))

end SubexponentialSAT.SqrtLog.HashScopeProgram.Extract

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed framed-record fold physically concatenates original literal-code
records after removing each term's coefficient frame. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open Extract (Data data)

def ports : RecordPrograms.Ports 3 6 :=
  ⟨0,1,2,0,1,by decide,by decide,by decide,by decide⟩

def Ready (a : Data) : Prop := a.stacks 2=[] ∧ a.stacks 3=[] ∧ a.stacks 5=[]

abbrev command : Cmd 3 6 := LeafProgram.foldCommand ports Extract.command
abbrev program := compiled command 0 4

end SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

abbrev Data := State 11 80

def ports : RecordPrograms.Ports 11 80 :=
  ⟨8,9,10,47,48,by decide,by decide,by decide,by decide⟩

def emitted (a : Data) : Data :=
  pushedState 48 8 true (escapedState ports (pushedState 48 8 false a))

def fixed (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 8 false) 9 true) 10 false,a.stacks⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

abbrev Data := State 11 49

def ports : RecordPrograms.Ports 11 49 :=
  ⟨8,9,10,47,48,by decide,by decide,by decide,by decide⟩

def emitted (a : Data) : Data :=
  pushedState 48 8 true (escapedState ports (pushedState 48 8 false a))

def fixed (a : Data) : Data :=
  ⟨Function.update (Function.update (Function.update a.regs 8 false) 9 true) 10 false,a.stacks⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpChunkRecordMap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual map from literal records to chunk records

The input is the canonical encoded list of literal codes and a preserved binary
chunk width. Each parsed record passes through the actual index decoder,
counter, division program, and record writer. The accumulator is reversed, as
required by the separately checked record-reversal and stable-deduplication
passes. No semantic map is installed as a machine instruction.
-/

namespace SubexponentialSAT.SubexpChunkRecordMap

open BitProgram StructuredCalls

def ports : RecordPrograms.Ports 11 22 where
  tag := 8
  present := 9
  found := 10
  source := 19
  payload := 9
  tag_ne_present := by decide
  found_ne_tag := by decide
  found_ne_present := by decide
  source_ne_payload := by decide

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed outer scanner for a table of raw tuple payloads. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls



def ports : RecordPrograms.Ports 11 49 :=
  ⟨8,9,10,46,47,by decide,by decide,by decide,by decide⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramScopeOnly
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Scope extraction can run before the eventual coefficient ring is selected.
A fixed two-bit temporary scalar shape gives exactly the same scope stream. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

namespace Complete

@[simp] theorem scopeOnly_shape :
    ([false,false] : List Bool).length=(0+1)*SubexponentialSAT.SubexpLiftRing.baseWidth 3 1 := by
  have hlog : Nat.log 2 3=1 := Nat.log_eq_of_pow_le_of_lt_pow (by decide) (by decide)
  simp [SubexponentialSAT.SubexpLiftRing.baseWidth,hlog]

end Complete
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- A bounded variant lets the callback cost depend on a certified maximum
number of rows. The bound is used only at iterations that actually run. -/
structure BoundedRoundSpec {r s : ℕ} {α : Type*} (p : LoopPorts r s)
    (body : Cmd r s) (next : α → α) (invariant : ℕ → α → State r s → Prop)
    (cost limit : ℕ) : Prop where
  read : ∀ q x a, invariant q x a → invariant q x (readCounterState p a)
  step : ∀ q x a, q < limit → invariant q x a → a.regs p.present = true →
    ∃ n ≤ cost, ∃ b, invariant (q + 1) (next x) b ∧
      b.stacks p.counter = a.stacks p.counter ∧ b.regs p.present = true ∧
      Eval body n a b

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT BitProgram StructuredCalls

def indices (js : List ℕ) : List Bool := ProgramEncoding.encodeRecords (js.map unary)

def replaceBit : Code := .call
  (ProgramLinking.liftProgram (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1)
    id arrayPorts)

def clearBit : Code := .call (StackRoutines.clearProgram 4 (0 : Fin 8) 1)

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

def savedInputs (js : List ℕ) (bits : List Bool) (n : ℕ) : Fin 3 → List Bool :=
  ![indices js,bits,unary n]

def initCost (js : List ℕ) (bits : List Bool) (n : ℕ) : ℕ :=
  7*(indices js).length+7*bits.length+11*n+20

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual two-level record scan counting explicit scope entries. The ghost
payload decoder occurs only in the loop specification; the executable callback
uses the existing physical record counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def ports : RecordPrograms.Ports 5 4 :=
  ⟨2, 3, 4, 0, 1, by decide, by decide, by decide, by decide⟩

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchEnumerationCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

open SubexpOrderedTupleData Subexp.PairScoreBounds SubexpEnumerationPayload

theorem cartesian_width (rows alphabet : List (List Bool)) (L W : ℕ)
    (hr : ∀ row ∈ rows, row.length ≤ L)
    (ha : ∀ row ∈ alphabet, row.length ≤ W) :
    ∀ row ∈ orderedCartesian rows alphabet, row.length ≤ L + W := by
  rw [orderedCartesian_eq_reverse]
  simpa only [List.mem_reverse] using
    Subexp.PairScoreBounds.cartesian_width rows alphabet L W hr ha

end SubexponentialSAT.SqrtLog.IrreducibleSearchEnumeration

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open SubexpEnumerationPayload

theorem scalarWidth_three : scalarWidth 3 = 2 := by
  have h : Nat.log 2 3 = 1 :=
    Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
  simp only [scalarWidth, h]

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/

/-! A fixed, paid iteration producing the three real scalar operands. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

abbrev Triple := WordPair × WordPair × WordPair

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionIteration
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Unary runtime-loop execution used by both convolution loops. The body
obligation contains actual executions; the loop invariant concerns physical
stacks and may include decoded coefficient arrays and their lengths. -/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

def testResult (counter : Fin 256) (flag : Fin 16) (d : Data) : Data :=
  (StructuredProgram.Atom.peek counter 0 flag).eval d

@[simp] theorem testResult_stacks (counter : Fin 256) (flag : Fin 16) (d : Data) :
    (testResult counter flag d).stacks = d.stacks := rfl

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

def selectPrefix : Code := .call (ProgramLinking.liftProgram CoreMaskProgram.program maskReg maskPort)

end SubexponentialSAT.SubexpIncidenceSlotProgram

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

def clearState {S : ℕ} (port : Fin S) (a : Data S) : Data S :=
  ⟨readRegs a.regs 0 1 none, Function.update a.stacks port []⟩

def clearManyState {S : ℕ} : List (Fin S) → Data S → Data S
  | [], a => a
  | p :: ps, a => clearManyState ps (clearState p a)

def resetMany {S : ℕ} : List (Fin 16) → Command S
  | [] => .base .skip
  | r :: rs => .seq (.base (.atom (.set r false))) (resetMany rs)

def resetManyState {S : ℕ} : List (Fin 16) → Data S → Data S
  | [], a => a
  | r :: rs, a => resetManyState rs ((StructuredProgram.Atom.set r false).eval a)

def resetWork {S : ℕ} : Command S := resetMany workRegisters

def beforeCopies {S : ℕ} (tmp : Fin S) (ports : List (Fin S)) (a : Data S) : Data S :=
  resetManyState workRegisters (clearManyState ports (clearManyState [tmp] a))

def prepareState {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) : Data S :=
  copyManyState inputs (beforeCopies tmp ports a)

def finishState {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) : Data S :=
  resetManyState workRegisters
    (clearManyState ports (copyManyState outputs (clearManyState (outputs.map Prod.snd) a)))

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SupportSelectionPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed copying, comparison and record emission for support selection. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open BitProgram StructuredCalls SubexpScanPrimitives

def emitPorts (dst : Fin 64) (h : dst ≠ 34) : RecordPrograms.Ports 16 64 :=
  ⟨0, 1, 2, 34, dst, by decide, by decide, by decide, h.symm⟩

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
end


