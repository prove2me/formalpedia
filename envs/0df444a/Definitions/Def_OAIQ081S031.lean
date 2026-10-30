-- Prove2me | Definitions.Def_OAIQ081S031
-- name    : OAIQ081S031
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:29:40.985204+00:00
-- url     : https://prove2.me/theorems/e962f8f6-4ed4-463d-8d9a-e0356c6851a7
-- title:
--   Definitions bundle OAIQ081S031 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 134 declarations of OpenAI's Lean: 118 definitions and 16 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.recordReturn`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.popLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.transfer`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload.alphabet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload.decode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload.decodeRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload.decodeVariableRow`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload.encode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload.encodeDigits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamilyPayload.readChunks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput.clauseValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput.falsifyingLiteral`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput.violationVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput.violationWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Frame.reverseWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.peekRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.rawInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.records`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.scanInput`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.word`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.copySource`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.forward`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.popIndex`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.popTag`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Source.recordPrefix`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.optionalCostBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.polynomialBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.rowCostBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Extract.finish`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Extract.move12`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Extract.move25`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Extract.move54`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Extract.pop5`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten.Valid`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten.termPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.appended`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Marked.markedScope` and 78 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HashCircuitProgramControl`, `SubexponentialSAT_SqrtLog_HashCircuitProgramLookup`, `SubexponentialSAT_SqrtLog_HashCircuitProgramPayload`, `SubexponentialSAT_SqrtLog_HashCircuitProgramRows`, `SubexponentialSAT_SqrtLog_HashFamilyPayload`, `SubexponentialSAT_SqrtLog_HashFamilyPayloadSelect`, `SubexponentialSAT_SqrtLog_HashFamilyPayloadValid`, `SubexponentialSAT_SqrtLog_HashInput`, `SubexponentialSAT_SqrtLog_HashInputProgramFrame`, `SubexponentialSAT_SqrtLog_HashInputProgramLookup`, `SubexponentialSAT_SqrtLog_HashInputProgramLoop`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopFinal`, `SubexponentialSAT_SqrtLog_HashInputProgramSource`, `SubexponentialSAT_SqrtLog_HashScopeProgramBounds`, `SubexponentialSAT_SqrtLog_HashScopeProgramBytes`, `SubexponentialSAT_SqrtLog_HashScopeProgramExtract`, `SubexponentialSAT_SqrtLog_HashScopeProgramFlatten`, `SubexponentialSAT_SqrtLog_HashScopeProgramLoop`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedFrame`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedStep`, `SubexponentialSAT_SqrtLog_HashScopeProgramNativeCost`, `SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawFrame`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawTable`, `SubexponentialSAT_SqrtLog_HashScopeProgramReset`, `SubexponentialSAT_SqrtLog_HashScopeProgramSemantics`, `SubexponentialSAT_SqrtLog_HashScopeProgramSingle`, `SubexponentialSAT_SqrtLog_HashSelectProgramCore`, `SubexponentialSAT_SqrtLog_HashSelectProgramGenerate`, `SubexponentialSAT_SqrtLog_HashSelectProgramLoop`, `SubexponentialSAT_SqrtLog_HashSelectSAT`, `SubexponentialSAT_SqrtLog_HashSelectTuple`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgram`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramLoop`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramLowMask`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics`, `SubexponentialSAT_SqrtLog_HeadScatterProgram`, `SubexponentialSAT_SqrtLog_HeadScatterProgramInit`, `SubexponentialSAT_SqrtLog_HeadScatterProgramScan`, `SubexponentialSAT_SqrtLog_HighIncidence`, `SubexponentialSAT_SqrtLog_HighIncidenceNeutral`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeProgramNat`, `SubexponentialSAT_SqrtLog_SquarefreeProgramRead`, `SubexponentialSAT_SqrtLog_SquarefreeProgramStorage`, `SubexponentialSAT_SqrtLog_SquarefreeProgramSupport`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpClauseRowProgram`, `SubexponentialSAT_SubexpLayoutFactorBounds`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpRecordScan`, `SubexponentialSAT_SubexpScopeProducer`, `SubexponentialSAT_Subexp_GlobalBasisMetadata`, `SubexponentialSAT_Subexp_SupportSelectionData`, `SubexponentialSAT_Subexp_TupleProgram`, `SubexponentialSAT_Subexp_TypeBitProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003`, `OAIQ081S005`, `OAIQ081S007`, `OAIQ081S008` and `OAIQ081S009` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S051`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060`, `OAIQ081S062` and `OAIQ081S064`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelect.initial_coverage_of_code`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S005
import Definitions.Def_OAIQ081S007
import Definitions.Def_OAIQ081S008
import Definitions.Def_OAIQ081S009

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRecordScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev Data := StructuredProgram.State 5 6

abbrev recordState (regs : Fin 5 → Bool) (input key query work tmp output : List Bool) : Data :=
  ⟨regs, storage input key query work tmp output⟩

end SubexponentialSAT.SubexpRecordScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev copy (src dst tmp : Fin 7) : Cmd 6 7 :=
  .call (StackRoutines.copyProgram src dst tmp (0 : Fin 6) 1)

abbrev popLiteral : Cmd 6 7 := .base (.atom (.pop 2 5 1))

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev transfer (src dst : Fin 7) : Cmd 6 7 :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 6) 1)
end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev transfer : Cmd 5 6 :=
  .call (StackRoutines.transferProgram (0 : Fin 6) 2 (0 : Fin 5) 1)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

/-- Both record loops use this physical three-instruction return convention. -/
abbrev recordReturn : Cmd 8 96 :=
  .seq (.base (.atom (.set 0 false)))
    (.seq (.base (.atom (.set 1 true))) (.base (.atom (.set 2 false))))

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev Entry := BinaryArgmin.Entry

/-- Only payloads are serialized. In particular no uncomputed score is supplied
as input data to this parser. A final false list marker is consumed. -/
def candidateEncoding : List (List Bool) → List Bool
  | [] => [false]
  | a :: rest => true :: (Encoding.frame a.reverse ++ candidateEncoding rest)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

@[simp] theorem escaped_append (a b : List Bool) :
    escaped (a ++ b) = escaped a ++ escaped b := by simp [escaped]

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

def prependRecord (bits out : List Bool) : List Bool :=
  true :: (Encoding.frame bits ++ out)

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramGenerate
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def generatedPayloads (alphabet : Records) (depth : ℕ) : Records :=
  (TupleProgram.powerRows alphabet depth [[]]).map List.reverse

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayload
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The actual tuple-generator bit alphabet and its reverse-aware semantic
decoder. The alphabet matches `SubexpAlphabetProgram.command_eval`. -/

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily
open SubexponentialSAT.Subexp TupleProgram
open SubexponentialSAT.SubexpLiftRing (fixedBits)
open SubexponentialSAT.BinaryArithmetic (toNat)

def alphabet (m width : ℕ) : List (List Bool) :=
  (List.range (3 * m)).map (fixedBits width)

def readChunks (width : ℕ) : ℕ → List Bool → List ℕ
  | 0, _ => []
  | depth + 1, bits =>
      BinaryArithmetic.toNat (bits.take width) :: readChunks width depth (bits.drop width)

def encodeDigits {m depth : ℕ} (width : ℕ) (a : Fin depth → Fin (3 * m)) : List Bool :=
  ((List.ofFn fun j => fixedBits width (a j).val).flatten).reverse

def encode {m depth : ℕ} (width : ℕ) (h : Candidate m depth) : List Bool :=
  encodeDigits width (candidateDigitsEquiv m depth h)

def decode (m depth width : ℕ) (hm : 0 < m) (payload : List Bool) : Candidate m depth :=
  decodeDigits fun j =>
    ⟨(readChunks width depth payload.reverse).getD j.val 0 % (3 * m),
      Nat.mod_lt _ (by omega)⟩

/-- A total row decoder; the zero-dimensional case has only the zero row. -/
def decodeRow (m depth width : ℕ) (payload : List Bool) : Fin m → ZMod 3 :=
  if hm : 0 < m then row (decode m depth width hm payload) else fun _ => 0

@[simp] theorem alphabet_length (m width : ℕ) : (alphabet m width).length = 3 * m := by
  simp [alphabet]

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayloadValid
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

@[simp] theorem readChunks_length (width depth : ℕ) (bits : List Bool) :
    (readChunks width depth bits).length = depth := by
  induction depth generalizing bits with
  | zero => rfl
  | succ depth ih => simp [readChunks, ih]

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInput
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual clause violations and sparse hash factors on the original variables. -/

namespace SubexponentialSAT.SqrtLog.HashInput


open scoped BigOperators
noncomputable section

variable {V E I R : Type*} [DecidableEq V] [CommRing R]

def clauseValue (C : SAT.Clause V) (x : SAT.Assignment V) : R :=
  if C.eval x then 0 else 1

def falsifyingLiteral (l : SAT.Literal V) : MvPolynomial V R :=
  if l.positive then 1 - MvPolynomial.X l.variable else MvPolynomial.X l.variable

omit [DecidableEq V] in
@[simp] theorem eval_falsifyingLiteral (l : SAT.Literal V) (x : SAT.Assignment V) :
    MvPolynomial.eval (fun v => boolValue (R := R) (x v)) (falsifyingLiteral l) =
      if l.eval x then 0 else 1 := by
  rcases l with ⟨v, p⟩
  cases p <;> cases h : x v <;>
    simp [falsifyingLiteral, boolValue, SAT.Literal.eval, h]

section Hash
variable [Fintype E] [DecidableEq E]

def violationVector (C : E → SAT.Clause V) (x : SAT.Assignment V) : E → R :=
  fun e => clauseValue (C e) x

def violationWeight (C : E → SAT.Clause V) (x : SAT.Assignment V) : ℕ :=
  ∑ e, if (C e).eval x then 0 else 1

end Hash
end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectSAT
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Instantiation of the finite selector with actual clause violations.
This is a conditional composition theorem: exact evaluation and initial
coverage are explicit hypotheses, not an assumed SAT oracle. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

def cnfRowAccept {n m : ℕ} (C : Fin m → SAT.Clause (Fin n))
    (r : Row m) (x : SAT.Assignment (Fin n)) : Bool :=
  decide ((∑ e, r e * HashInput.violationVector (R := ZMod 3) C x e) = 0)

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectTuple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete indexed tuple family discharges the selector's coverage
hypothesis from a supplied lower-support code. All tuples, including repeated
coordinates and repeated resulting rows, remain in the enumeration. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

open scoped BigOperators

def tupleRows (m d : ℕ) : Fin ((3 * m) ^ d) → Row m :=
  fun i => HashFamily.row (HashFamily.enumerate m d i)

def tupleFamily {m d c : ℕ} (hcount : (3 * m) ^ d = c + 1) :
    Fin (c + 1) → Row m :=
  fun i => tupleRows m d (Fin.cast hcount.symm i)

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyPayloadSelect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamilyPayload

open HashFamily

/-- Initial code rows may have more chunks than candidate hash rows. The
shared matrix decoder therefore obtains each row's depth from its payload. -/
def decodeVariableRow (m width : ℕ) (payload : List Bool) : Fin m → ZMod 3 :=
  decodeRow m (payload.length / width) width payload

end SubexponentialSAT.SqrtLog.HashFamilyPayload

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the agreed inline record payload: a framed flat ring
coefficient followed by the ORIGINAL canonical literal-list payload. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Frame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev reverseWeight : Cmd 3 3 := .call (StackRoutines.transferProgram 0 2 0 1)

end SubexponentialSAT.SqrtLog.HashInputProgram.Frame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev popIndex : Cmd 3 6 := .base (.atom (.pop 2 0 1))

def recordPrefix (xs : List (List Bool)) : List Bool :=
  xs.foldr (fun bits tail => true :: (Encoding.frame bits ++ tail)) []

abbrev popTag : Cmd 3 6 := .base (.atom (.pop 1 0 1))

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLookup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete preserving, paid lookup of a source clause by its list position. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Source
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev copySource : Cmd 3 6 := .call (StackRoutines.copyProgram 0 1 4 0 1)
abbrev forward : Cmd 3 6 := .call (StackRoutines.transferProgram 3 5 0 1)

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

def peekRegs (regs : Fin 8 → Bool) (raw : List Bool) : Fin 8 → Bool :=
  readRegs regs 0 1 raw.head?

def word (b m : ℕ) (a : Fin m × ZMod 3) : List Bool :=
  SubexponentialSAT.SubexpLiftRing.fixedBits b (a.1.val+m*a.2.val)

def scanInput {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) : List Bool :=
  (terms.map fun a => (word b m a).reverse).flatten

def records (ps : List (List Bool)) (acc : List Bool) : List Bool :=
  ps.foldr (fun p tail => true::(Encoding.frame p++tail)) acc

@[simp] theorem records_append (xs ys : List (List Bool)) (acc : List Bool) :
    records (xs++ys) acc=records xs (records ys acc) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [records]

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

def rawInput {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) : List Bool :=
  (terms.map (word b m)).flatten.reverse

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramBytes
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram

def recordPrefix : List (List Bool) → List Bool
  | [] => []
  | x :: xs => true :: (Encoding.frame x ++ recordPrefix xs)

def clauseBytes (bits : List Bool) : List Bool :=
  ((Encoding.readFrame bits).map Prod.snd).getD []

@[simp] theorem clauseBytes_payload (weight : List Bool) (records : List (List Bool)) :
    clauseBytes (Encoding.frame weight ++ Encoding.encodeList id records) =
      Encoding.encodeList id records := by simp [clauseBytes]

def accumulate (bits out : List Bool) : List Bool := (clauseBytes bits).dropLast ++ out

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramExtract
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical extraction of the literal-record bytes from one weighted raw
clause. Coefficient bytes are discarded even when the coefficient is zero. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Extract
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev move12 : Cmd 3 6 := .call (StackRoutines.transferProgram 1 2 0 1)
abbrev move25 : Cmd 3 6 := .call (StackRoutines.transferProgram 2 5 0 1)
abbrev move54 : Cmd 3 6 := .call (StackRoutines.transferProgram 5 4 0 1)
abbrev pop5 : Cmd 3 6 := .base (.atom (.pop 5 0 1))
abbrev finish : Cmd 3 6 := .base (.atom (.set 1 true))

end SubexponentialSAT.SqrtLog.HashScopeProgram.Extract

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFlatten
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed framed-record fold physically concatenates original literal-code
records after removing each term's coefficient frame. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
def Valid (bits : List Bool) : Prop :=
  ∃ w records, bits = Encoding.frame w ++ Encoding.encodeList id records

def cost (records : List (List Bool)) : ℕ :=
  4 + RecordPrograms.budget (fun bits => 30*(bits.length+1)) records

def termPayload (term : List Bool × List (List Bool)) : List Bool :=
  Encoding.frame term.1 ++ Encoding.encodeList id term.2

end SubexponentialSAT.SqrtLog.HashScopeProgram.Flatten

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpClauseRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An actual clause-row program

The input clause uses `Encoding.encodeList Encoding.encodeNat`. The stored
assignment is an explicit word of the declared length, one bit per variable.
The program parses each literal, decodes its unary index and polarity, performs
a preserving indexed read, and accumulates the disjunction. No semantic test is
an instruction. All auxiliary ports and all input requirements are explicit.
-/

namespace SubexponentialSAT.SubexpClauseRowProgram

open BitProgram StructuredCalls

namespace LiteralDecoder

/-- Each pair of unary payload bits adds one bit to the index counter. An odd
last bit is the positive-polarity flag. The leading reversed delimiter is consumed. -/
abbrev program : Program 4 10 8 where
  inputStack := 9
  outputStack := 2
  entry := 0
  code q := match q.val with
    | 0 => .pop 9 0 1 1
    | 1 => .set 2 false 2
    | 2 => .pop 9 0 1 3
    | 3 => .branch 1 4 7
    | 4 => .bnot 2 2 5
    | 5 => .branch 2 2 6
    | 6 => .push 2 0 2
    | _ => .halt

end LiteralDecoder


end SubexponentialSAT.SubexpClauseRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiteralChunkProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual literal-index to chunk-index conversion

The input is one reversed canonical unary literal field and a binary chunk
width. The fixed program decodes the variable index, counts it into binary,
divides by the chunk width, and constructs the reversed canonical chunk field.
-/

namespace SubexponentialSAT.SubexpLiteralChunkProgram

open BitProgram StructuredCalls StackRoutines

def straight : List (StructuredProgram.Atom 8 19) → StructuredProgram.Cmd 8 19
  | [] => .skip
  | a :: as => .seq (.atom a) (straight as)

def resetOps : List (StructuredProgram.Atom 8 19) :=
  [.set 0 false, .set 1 false, .set 2 false, .set 3 false,
    .set 4 false, .set 5 false, .set 6 false, .set 7 false]

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpChunkRecordMap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

def chunk (ell : List Bool) (code : ℕ) : ℕ := (code / 2) / BinaryArithmetic.toNat ell

def mappedBits (ell bits : List Bool) : List Bool :=
  Encoding.encodeNat (chunk ell (bits.length - 1))

@[simp] theorem mappedBits_encodeNat (ell : List Bool) (code : ℕ) :
    mappedBits ell (Encoding.encodeNat code) = Encoding.encodeNat (chunk ell code) := by
  simp [mappedBits]

def callbackCost (ell bits : List Bool) : ℕ :=
  SubexpLiteralChunkProgram.budget ell.length ((bits.length - 1) / 2) +
    5 * (mappedBits ell bits).length + 14

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Construct a clause's local chunk scope from its encoded literals

This fixed program maps actual literal records to chunk records, restores the
record order, and invokes the checked stable deduplicator. Its output order is
the last-occurrence order used by the materializer and incidence-plan producer.
-/

namespace SubexponentialSAT.SubexpScopeProducer

open BitProgram StructuredCalls SubexpChunkRecordMap

def scope (ell : List Bool) (codes : List ℕ) : List ℕ :=
  ExecCNF.dedupLiterals (codes.map (chunk ell))

@[simp] theorem mem_scope (ell : List Bool) (codes : List ℕ) (j : ℕ) :
    j ∈ scope ell codes ↔ ∃ code ∈ codes, (code / 2) / BinaryArithmetic.toNat ell = j := by
  simp only [scope, ExecCNF.mem_dedupLiterals, List.mem_map, chunk]

/-- Every term counts instructions in a concrete pass over an actual encoding. -/
def budget (ell : List Bool) (codes : List ℕ) : ℕ :=
  5 + RecordPrograms.budget (callbackCost ell) (codes.map Encoding.encodeNat) +
    10 * (Encoding.encodeList Encoding.encodeNat (codes.map (chunk ell))).length +
    120 * ((Encoding.encodeList Encoding.encodeNat (codes.map (chunk ell))).length + 1) ^ 2

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw hash scopes include every referenced literal, irrespective of its
coefficient. The physical materializer preserves these exact original codes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

def payload (term : Term) : Word :=
  Encoding.frame term.1 ++ Encoding.encodeList Encoding.encodeNat term.2

def mergedCodes (terms : List Term) : List ℕ := terms.reverse.flatMap Prod.snd

def scope (terms : List Term) : List ℕ :=
  SubexpScopeProducer.scope [true] (mergedCodes terms)

@[simp] theorem mem_mergedCodes (terms : List Term) (c : ℕ) :
    c ∈ mergedCodes terms ↔ ∃ term ∈ terms, c ∈ term.2 := by
  simp [mergedCodes]

@[simp] theorem mem_scope (terms : List Term) (v : ℕ) :
    v ∈ scope terms ↔ ∃ term ∈ terms, ∃ code ∈ term.2, code / 2 = v := by
  simp only [scope, SubexpScopeProducer.mem_scope, mem_mergedCodes]
  simp only [BinaryArithmetic.toNat, Nat.mul_zero, Nat.add_zero, BinaryArithmetic.bitVal_true, Nat.div_one]
  aesop

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSingle
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed program turns a physically materialized weighted raw row into
its deduplicated original-variable scope. All constant initialization is paid. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Single
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def wordTerms (terms : List Term) : List (List Bool × List (List Bool)) :=
  terms.map fun term => (term.1,term.2.map Encoding.encodeNat)

def cost (terms : List Term) : ℕ :=
  11 + Flatten.cost (terms.map payload) +
    6*(Encoding.encodeList Encoding.encodeNat (mergedCodes terms)).length +
    SubexpScopeProducer.budget [true] (mergedCodes terms)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Single

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLayoutFactorBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical bounds for the actual clause-factor calls.  All envelopes are
polynomials in a common bound on the represented sizes and word lengths. -/

namespace SubexponentialSAT.SubexpLayoutConstructionBounds

def scopeProgramBound (S : ℕ) :=
  5 + S * (12 * S + scopeCallbackBound S + 7) +
    10 * mappedScopeBytesBound S + 120 * (mappedScopeBytesBound S + 1) ^ 2

end SubexponentialSAT.SubexpLayoutConstructionBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Polynomial bit-size envelopes for the actual per-row scope computation. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
open SubexponentialSAT.SubexpLayoutConstructionBounds

abbrev natBits (xs : List ℕ) := Encoding.encodeList Encoding.encodeNat xs

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramReset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Reset
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Only instantiated at the fixed register inventory of the outer program. -/
def command {r s : ℕ} : List (Fin r) → Cmd r s
  | [] => .base .skip
  | i :: is => .seq (.base (.atom (.set i false))) (command is)

def result {r s : ℕ} (is : List (Fin r)) (a : State r s) : State r s :=
  ⟨fun i => if i ∈ is then false else a.regs i, a.stacks⟩

abbrev all {r s : ℕ} : Cmd r s := command (List.finRange r)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Reset

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed outer record loop: one concrete scope computation per raw hash row.
The induction is a trace proof; the instruction table contains only one loop. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Outer
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def scopeBytes (terms : List Term) : List Bool := Encoding.encodeList Encoding.encodeNat (scope terms)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Outer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

abbrev fix : Cmd 11 80 := .seq (.base (.atom (.set 8 false)))
  (.seq (.base (.atom (.set 9 true))) (.base (.atom (.set 10 false))))

end SubexponentialSAT.SqrtLog.HashScopeProgram.MarkedFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact scopes of the physically stored sparse raw rows and optional original
marked clause. These definitions are shared by the machine and resource proofs. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
namespace RawTable
def rowBits {m : ℕ} (b : ℕ) (terms : List (Fin m × ZMod 3)) : List Bool :=
  (terms.map (HashInputProgram.Loop.word b m)).flatten

end RawTable
namespace Marked
abbrev markedScope (codes : List ℕ) := SubexpScopeProducer.scope [true] codes
abbrev scopeBits (codes : List ℕ) := Encoding.encodeList Encoding.encodeNat (markedScope codes)

end Marked
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked branch appends one scope even when that scope is empty. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


def processCost (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (i : Fin clauses.length) : ℕ :=
  23*(Encoding.encodeList id clauses).length+SubexpScopeProducer.budget [true] (codes i)+
    8*(scopeBits (codes i)).length+51

def appended {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (mark : Option (Fin clauses.length)) (out : List Bool) : List Bool :=
  match mark with
  | none => out
  | some i => SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBits (codes i)) out

def optionalCost (clauses : List (List Bool)) (codes : Fin clauses.length → List ℕ)
    (mark : Option (Fin clauses.length)) (index : List Bool) : ℕ :=
  2*index.length+10+(mark.map (processCost clauses codes)).getD 0

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.TupleProgram

abbrev fix : Cmd 11 49 := .seq (.base (.atom (.set 8 false)))
  (.seq (.base (.atom (.set 9 true))) (.base (.atom (.set 10 false))))

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawFrame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct table adapter: raw clause-reference rows to deduplicated scope rows.
The original source table and all decoding parameters remain on their tapes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def inputBits {m : ℕ} (b : ℕ) (rows : Rows m) := Encoding.encodeList id (rows.map (rowBits b))

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed polynomial envelope for raw references plus the optional original
marked clause. The size parameter bounds stored byte lengths and row/slot counts. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.SubexpLayoutConstructionBounds

def rowCostBound (S : ℕ) : ℕ :=
  12*S*S+assemblyBound S+31+46*weightedBytesBound S+
    scopeProgramBound (weightedBytesBound S)+8*mappedScopeBytesBound (weightedBytesBound S)+37

def optionalCostBound (S : ℕ) : ℕ :=
  2*S+10+23*S+scopeProgramBound S+8*mappedScopeBytesBound (weightedBytesBound S)+51

def polynomialBound (S : ℕ) : ℕ :=
  10+S*rowCostBound S+optionalCostBound S+
    10*(1+(2*mappedScopeBytesBound (weightedBytesBound S)+2)*(S+1))

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed unary-counter controller for K greedy rounds. The round command
must supply a paid actual execution; the counter is runtime stack data. -/

namespace SubexponentialSAT.SqrtLog.HashSelectProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev readCounter {r s : ℕ} (p : LoopPorts r s) : Cmd r s :=
  .base (.atom (.pop p.counter p.value p.present))

def readCounterState {r s : ℕ} (p : LoopPorts r s) (a : State r s) : State r s :=
  ⟨readRegs a.regs p.value p.present (a.stacks p.counter).head?,
    Function.update a.stacks p.counter (a.stacks p.counter).tail⟩

abbrev rounds {r s : ℕ} (p : LoopPorts r s) (body : Cmd r s) : Cmd r s :=
  .seq (readCounter p) (.while p.present (.seq body (readCounter p)))

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisMetadata
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical packing metadata lookup

The raw packing table and query remain on stacks 0 and 1. A successful lookup
returns either a block/type pair on 2/3, or a leftover rank on 4. Register 4
distinguishes those cases; all other registers and stacks 5 through 11 are
cleared. Keys, indices, and type encodings are runtime words.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisMetadata

open BitProgram StructuredCalls


abbrev Code := Cmd 5 12

end SubexponentialSAT.Subexp.GlobalBasisMetadata

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeBitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

open BitProgram

abbrev program : Program 3 2 7 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 3, .pop 1 0 1 0,
    .pop 1 2 1 4, .pop 1 0 1 5, .branch 1 4 6, .halt]

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SupportSelectionData
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Ordered support records selected from the actual packing inverse. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open ConstructivePacking

variable {D r Q Δ : ℕ}

def record (n : ℕ) : List Bool := true :: Encoding.frame (unary n)

def supportPrefix (p : ℕ → Bool) (n : ℕ) : List Bool :=
  ((List.range n).filter p).flatMap record

@[simp] theorem prefix_zero (p : ℕ → Bool) : supportPrefix p 0 = [] := rfl

@[simp] theorem record_length (n : ℕ) : (record n).length = 2 * n + 2 := by
  simp [record]

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical head-identifier selection uses the original ambient word array.
No packing-coverage predicate participates in the scan. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

abbrev record := Subexp.SupportSelectionProgram.record
abbrev supportPrefix := Subexp.SupportSelectionProgram.supportPrefix

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

def count (p : ℕ → Bool) (n : ℕ) : ℕ := (chosenIds p n).length

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramLowMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit order conversion between the reverse high-incidence mask and the
forward low-variable mask consumed by head-identifier selection. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask
open SubexponentialSAT BitProgram StructuredCalls

abbrev Data := State 2 2

def state (regs : Fin 2 → Bool) (xs out : List Bool) : Data := ⟨regs,![xs,out]⟩

abbrev program : Program 2 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1,.branch 1 2 6,.branch 0 3 4,
    .set 0 false 5,.set 0 true 5,.push 1 0 0,.halt]

def stepRegs (regs : Fin 2 → Bool) (b : Bool) : Fin 2 → Bool :=
  Function.update (readRegs regs 0 1 (some b)) 0 (!b)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.LowMask

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev Code := Cmd 8 13

def popBit : Code := .base (.atom (.pop 1 0 1))
def pushBit : Code := .base (.atom (.push 4 0))

def popIndexTag : Code := .base (.atom (.pop 2 0 1))

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

abbrev zeroProgram : Program 8 13 5 where
  inputStack := 3
  outputStack := 0
  entry := 0
  code := ![.pop 3 0 1 1, .branch 1 2 4, .set 0 false 3, .push 0 0 0, .halt]

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

def peekBits : Code := .base (.atom (.peek 1 0 1))

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem chosenIds_bound (p : ℕ → Bool) (n : ℕ) : ∀ j ∈ chosenIds p n,j < n := by
  intro j hj
  exact List.mem_range.mp (List.mem_of_mem_filter hj)

theorem chosenIds_nodup (p : ℕ → Bool) (n : ℕ) : (chosenIds p n).Nodup :=
  (show (List.range n).Nodup from List.nodup_range).filter p

/-- Semantic naming of exactly the order already present in the emitted ID
stream; this definition does not perform an uncharged physical reindexing. -/
def headOrder (p : ℕ → Bool) (n : ℕ) (i : Fin (count p n)) : Fin n :=
  ⟨(chosenIds p n)[i.val],chosenIds_bound p n _ (List.getElem_mem i.isLt)⟩

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidence
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer high-incidence cutoff and disjoint branching on original coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def high (scope : E → Finset V) (cut : ℕ) : Finset V :=
  Finset.univ.filter fun v => cut < Incidence.degree scope v

omit [Fintype V] [DecidableEq E] in
@[simp] theorem degree_remainingScope (H : Finset V) (scope : E → Finset V)
    (v : {v : V // v ∉ H}) :
    Incidence.degree (remainingScope H scope) v = Incidence.degree scope v.val := by
  simp [Incidence.degree, Incidence.incident, remainingScope]

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceNeutral
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Neutral unary factors cover exactly the otherwise unused coordinates. -/
namespace SubexponentialSAT.SqrtLog.HighIncidence

open scoped BigOperators

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def uncovered (scope : E → Finset V) : Finset V :=
  Finset.univ.filter fun v => Incidence.degree scope v = 0

end SubexponentialSAT.SqrtLog.HighIncidence

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime Boolean branch initialization and exhaustive odometer traces.
The only parameter in the enumeration command is its fixed real callback.
The high dimension is data, not finite control. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev trueCount := Subexp.PaddedCompletion.trueCount

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Port relocation and paid bit-copy primitives for the dictionary builder. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpRecordScan

abbrev storageCopy (src dst tmp : Fin 7) : Cmd 5 7 :=
  .call (StackRoutines.copyProgram src dst tmp (0 : Fin 5) 1)

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed primitive bit-mask union. Both runtime input words have the same
length. The output is prepended in reverse order; no list operation is atomic
and the instruction table does not depend on the word length. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram

abbrev maskBody : Cmd 5 3 :=
  .seq (.atom (.pop 0 0 2))
    (.seq (.atom (.pop 1 1 3))
      (.seq (.atom (.bor 4 0 1))
        (.seq (.atom (.push 2 4)) (.atom (.peek 0 0 2)))))

abbrev maskLoop : Cmd 5 3 := .while 2 maskBody

abbrev maskUnion : Cmd 5 3 := .seq (.atom (.peek 0 0 2)) maskLoop

def maskUnionProgram := compiled maskUnion 0 2

@[simp] theorem maskUnion_control_size : size maskUnion = 7 := rfl

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramNat
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive unary-field reader used by encoded sparse-key joins.
The unary magnitude affects execution time, never the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def natPorts {s : ℕ} (src dst : Fin s) : Fin 2 → Fin s := ParserProgram.pair src dst

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def frameReadPorts {s : ℕ} (src dst : Fin s) : Fin 2 → Fin s := ParserProgram.pair src dst

abbrev transfer8 {s : ℕ} (src dst : Fin s) : Cmd 8 s :=
  .call (StackRoutines.transferProgram src dst (0 : Fin 8) 1)

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev copy (src dst : Fin 15) : Cmd 8 15 :=
  .call (copyProgram src dst 7 (0 : Fin 8) 1)

abbrev peek : Cmd 8 15 := .base (.atom (.peek 0 0 1))

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev prepareClip : Cmd 8 15 :=
  .seq (copy 10 5) (.seq (Program.transfer8 5 11) (.seq (copy 2 12) (copy 3 13)))

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev copy (src dst : Fin 40) : Cmd 8 40 :=
  .call (copyProgram src dst 31 (0 : Fin 8) 1)

abbrev peek : Cmd 8 40 := .base (.atom (.peek 32 0 7))

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/

/-! Emit stage. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

abbrev finish : Cmd 8 40 := Program.transfer8 33 38

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
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

abbrev transfer (src dst : Fin 56) : Cmd 8 56 := .call (transferProgram src dst 0 1)
abbrev peek : Cmd 8 56 := .base (.atom (.peek 40 0 7))

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end


