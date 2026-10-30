-- Prove2me | Definitions.Def_OAIQ081S119
-- name    : OAIQ081S119
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:34:24.121066+00:00
-- url     : https://prove2.me/theorems/97295432-85b4-4382-a2dd-b9341a99016a
-- title:
--   Definitions bundle OAIQ081S119 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 103 declarations of OpenAI's Lean: 96 definitions, 4 inductive types or structures and 3 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.payload`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.constantVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.outputBits`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.scopeWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.scopes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.cost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple.interpretedTerms`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.appendScopes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.callbackCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.loopCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.scopeBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.Clean`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable.input`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable.result`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable.setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.bitResult`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.choose`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.lookup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.loop`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.loopPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.readBit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.selected`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.setup`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.test`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.tested`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.popped`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.pushed`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.state`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Code`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.initial` and 60 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_HashMassAdapter`, `SubexponentialSAT_SqrtLog_DensePolynomialProgramReady`, `SubexponentialSAT_SqrtLog_HashInputProgramLift`, `SubexponentialSAT_SqrtLog_HashInputProgramLoop`, `SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTable`, `SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawCall`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawLoop`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgram`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramFullTable`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramLoop`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramRun`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramTest`, `SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit`, `SubexponentialSAT_SqrtLog_HighIncidenceProgram`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction`, `SubexponentialSAT_SqrtLog_HighIncidenceProgramScan`, `SubexponentialSAT_SqrtLog_HornerProgram`, `SubexponentialSAT_SqrtLog_HornerProgramControl`, `SubexponentialSAT_SqrtLog_HornerProgramLoop`, `SubexponentialSAT_SqrtLog_HornerProgramModel`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution`, `SubexponentialSAT_SqrtLog_IdempotentApplyProgramMachine`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgram`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun`, `SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan`, `SubexponentialSAT_SqrtLog_IdempotentProgramMachine`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryCode`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SubexpHeadColorProgram`, `SubexponentialSAT_Subexp_SupportSelectionPrimitives`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S100`, `OAIQ081S101`, `OAIQ081S102`, `OAIQ081S103` and `OAIQ081S114` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S139`, `OAIQ081S140`, `OAIQ081S141`, `OAIQ081S142`, `OAIQ081S144`, `OAIQ081S145`, `OAIQ081S146`, `OAIQ081S150`, `OAIQ081S151` and `OAIQ081S152`; the statements `OAI.Algorithms.SubexponentialSAT.SqrtLog.CRTLocalProgram.Native.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady.frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.accepted`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCorrect.marked`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.run`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.accepted_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeHashQueries.marked_replay`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.add_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.mul_spec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.BaseReady.frame`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec.pairSpec`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInputProgram.Loop.loop_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.Complete.runRows_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable.call_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.command_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HornerProgram.command_run`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.rawCommand_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontend.scopeCall_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary.insert_code_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S101
import Definitions.Def_OAIQ081S102
import Definitions.Def_OAIQ081S103
import Definitions.Def_OAIQ081S114

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HashMassAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual marked-clause collector generalized to the frozen 40/896 leaf
bank. Its parser and adder are the original measured finite programs. All
marked queries are executed; their integer results are added before argmin.
The temporary query execution premise must be discharged by the concrete
optional-mark evaluator, including its high-assignment loop and cleanup. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter

open BitProgram StructuredCalls RecordPrograms SqrtLog LeafProgram

abbrev Data := State 40 896


open LeafOuterProgram

open scoped BigOperators


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HashMassAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_DensePolynomialProgramReady
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Static native arithmetic readiness, independent of the final service
composition. The two polynomial caches do not participate in readiness. -/
namespace SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
attribute [local simp] Fin.coe_ofNat_eq_mod
variable (p t : ℕ) [Fact p.Prime] (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {degree : ℕ}
    (table : Fin degree → Fin degree → Fin degree → Word (baseWidth p t))

structure BaseReady (base : Store) (scalarWidth : List Bool)
    (frame : Fin 6 → List Bool) : Prop where
  high : ∀ j : Fin 32, j ≠ 8 → j ≠ 9 → base (RingCall.ports j) =
    (RingScan.serviceState (fun _ => false) M.bits [] [] [] [] scalarWidth
      cache.zero.val (RingTriple.tableEncoding table)).stacks j
  low : ∀ i : Fin 20,
    base (SubexponentialSAT.SubexpConvolutionPair.lowPort (SubexponentialSAT.SubexpJetCellProgram.scalarPorts i)) =
      (DensePolynomialLoop.ready (fun _ => false) M.bits [] [] scalarWidth [] frame).stacks i
  width : (base 104).length = degree * baseWidth p t
  scalarWidthLength : scalarWidth.length = baseWidth p t
  degreeLength : (base 204).length = degree
  scratch : base 120 = []
  work : ∀ j : Fin 256, 112 ≤ j.val → j.val ≤ 119 → base j = []


end SubexponentialSAT.SqrtLog.DensePolynomialProgram.PairSpec

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native integer-representative coefficient lifting. The only arithmetic
performed by the machine is the audited dynamic padding/clearing routine. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpSymbolicCost
open SubexponentialSAT.ModularArithmetic SubexponentialSAT.ModularRingPrograms

def constantVector (t d : ℕ) (c : ZMod 3) : RingProgram.Code (RingProgram.ScalarCode 3 t) (d+1) :=
  Fin.cases (RingProgram.liftCoefficientRun t c).1
    (fun _ => SubexponentialSAT.SubexpPreparedQuartic.zeroWord 3 t)

end SubexponentialSAT.SqrtLog.HashInputProgram

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

def payload (t d : ℕ) (clauses : List (List Bool))
    (a : Fin clauses.length × ZMod 3) : List Bool :=
  Encoding.frame (RingProgram.flat (constantVector t d a.2)) ++ clauses[a.1.val]

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

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
namespace FromTuple
/-- Semantic interpretation of original source clauses, used only in the proof. -/
def interpretedTerms (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ)
    (terms : List (Fin clauses.length × ZMod 3)) : List Term :=
  terms.map fun a => (RingProgram.flat (HashInputProgram.constantVector t d a.2),codes a.1)

end FromTuple
namespace RawTable

def scopeBytes (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (terms : List (Fin clauses.length × ZMod 3)) : List Bool :=
  Encoding.encodeList Encoding.encodeNat
    (scope (FromTuple.interpretedTerms (clauses := clauses) t d codes terms))

end RawTable
namespace Complete
def scopeWords (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) : List (List Bool) :=
  rows.map (RawTable.scopeBytes (clauses := clauses) t d codes) ++
    mark.toList.map (fun i => Marked.scopeBits (codes i))

def scopes (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) : List (List ℕ) :=
  rows.map (fun row => scope (FromTuple.interpretedTerms (clauses := clauses) t d codes row)) ++
    mark.toList.map (fun i => Marked.markedScope (codes i))

def outputBits (t d : ℕ) {clauses : List (List Bool)} (codes : Fin clauses.length → List ℕ)
    (rows : RawTable.Rows clauses.length) (mark : Option (Fin clauses.length)) : List Bool :=
  Encoding.encodeList id (scopeWords (clauses := clauses) t d codes rows mark)

end Complete
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct original-source-to-scope composition. The finite program first reads
raw tuple references and looks up original clauses, then extracts their scope.
No table of precomputed scopes is supplied to this machine. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

def cost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (terms : List (Fin clauses.length × ZMod 3)) : ℕ :=
  HashInputProgram.Loop.uniformBudget t d b modulus clauses terms.length+20+
    Single.cost (interpretedTerms (clauses := clauses) t d codes terms)

end SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One callback for the actual raw-row table. The original clause master,
word width, modulus and ring shape are persistent; all workspace is cleaned. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation (restrictState lifted_call)

def callbackCost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (terms : List (Fin clauses.length × ZMod 3)) : ℕ :=
  6*(rowBits b terms).length+FromTuple.cost t d b modulus clauses codes terms+
    8*(scopeBytes (clauses := clauses) t d codes terms).length+30

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

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



def appendScopes (t d : ℕ) {clauses : List (List Bool)}
    (codes : Fin clauses.length → List ℕ) (rows : Rows clauses.length) (out : List Bool) : List Bool :=
  rows.foldl (fun o terms => SubexponentialSAT.Subexp.TupleProgram.prependRecord (scopeBytes (clauses := clauses) t d codes terms) o) out

def loopCost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) : Rows clauses.length → ℕ
  | [] => 0
  | row::rows => 6*(rowBits b row).length+callbackCost t d b modulus clauses codes row+7+
      loopCost t d b modulus clauses codes rows

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical scope stream, including the optional marked factor.
The final row order is all raw hash rows followed by the marked clause if present. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls


def cost (t d b : ℕ) (modulus : List Bool) (clauses : List (List Bool))
    (codes : Fin clauses.length → List ℕ) (rows : RawTable.Rows clauses.length)
    (mark : Option (Fin clauses.length)) (index : List Bool) : ℕ :=
  10+RawTable.loopCost t d b modulus clauses codes rows+Marked.optionalCost clauses codes mark index+
    10*(outputBits (clauses := clauses) t d codes rows mark).length

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHeadColorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Read a head color from its physical one-hot type encoding

Ports 0, 1, and 2 hold the flat type bytes, unary position, and unary color
width. The fixed array reader preserves these inputs. A five-label bit loop
counts the false prefix of the selected one-hot word; the remaining suffix is
cleared. Only output port 3 changes, and scratch ports 4--9 are restored.
-/

namespace SubexponentialSAT.SubexpHeadColorProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.AssignmentAlphabetSemantics

abbrev copyIndex : Cmd 5 10 := .call (StackRoutines.copyProgram 1 4 6 (0 : Fin 5) 1)

abbrev readCell : Cmd 5 10 :=
  .call (ProgramLinking.liftProgram (ArrayUpdatePrograms.readProgram (0 : Fin 5) 1)
    id readPorts)

abbrev select : Cmd 5 10 := .seq copyIndex readCell

end SubexponentialSAT.SubexpHeadColorProgram

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

abbrev Code := Cmd 16 64

def copy (src dst : Fin 64) : Code :=
  .call (StackRoutines.copyProgram src dst 42 (0 : Fin 16) 1)

def emit (dst : Fin 64) (h : dst ≠ 34) : Code :=
  .seq (TupleProgram.pushConst dst 0 false)
    (.seq (TupleProgram.escape (emitPorts dst h)) (TupleProgram.pushConst dst 0 true))

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical head-identifier selection uses the original ambient word array.
No packing-coverage predicate participates in the scan. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

abbrev Code := Cmd 16 64
abbrev copy := Subexp.SupportSelectionProgram.copy

def lookup : Code := liftCommand SubexpHeadColorProgram.select 0 5 wordRegs wordPorts

def selected (d : Data) (word : List Bool) : Data :=
  ⟨readRegs d.regs 0 1 none,Function.update d.stacks 36 word⟩

def readBit (low : Bool) : Code :=
  .call (ProgramLinking.liftProgram Subexp.TypeBitProgram.program (bitRegs low) (bitPorts low))

def bitResult (d : Data) (low answer : Bool) : Data :=
  ⟨Function.update (readRegs d.regs 0 1 none) (bitFlag low) answer,
    Function.update (Function.update d.stacks 12 []) (bitSource low) []⟩

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

/-- Inputs 31/32/33/38/39 are low mask, bit index, flat head-word table,
word width and original variable index. Scratch is restored after the test. -/
def Clean (d : Data) : Prop :=
  ∀ i ∈ ([12,13,16,17,18,19,20,21,34,36,42] : List (Fin 64)),d.stacks i=[]

def test : Code := .seq (copy 39 12) (.seq (copy 31 13) (.seq (readBit true)
  (.seq lookup (.seq (copy 32 12) (readBit false)))))

def tested (d : Data) (low head : Bool) : Data :=
  ⟨Function.update (Function.update (readRegs d.regs 0 1 none) 6 low) 4 head,d.stacks⟩

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def emit : Code := .seq (copy 39 34)
  (.seq (Subexp.SupportSelectionProgram.emit 0 (by decide)) (Subexp.TupleProgram.pushConst 1 0 false))

def choose : Code := .ite 6 (.ite 4 emit (.base .skip)) (.base .skip)

def visit : Code := .seq test choose

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def loopPorts : UnaryForPrograms.Ports 16 64 := ⟨39,14,15⟩
def loop : Code := UnaryForPrograms.forCmd loopPorts visit

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def setup : Code := .seq (copy 30 39) (Subexp.TupleProgram.pushConst 0 0 false)
def command : Code := .seq setup (.seq loop RegisterResetProgram.all)
def program := compiled command 30 0

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramFullTable
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

def input (regs : Fin 16 → Bool) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  ⟨regs,baseStacks n rows low W z⟩

def result (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ) : Data :=
  ⟨fun _ => false,
    Function.update (Function.update (baseStacks n rows low W z) 0
      (ProgramEncoding.encodeRecords ((chosenIds (predicate rows low z) n).map unary)))
      1 (zeros (count (predicate rows low z) n))⟩

abbrev setup := HeadIdentifierProgram.setup
abbrev program := HeadIdentifierProgram.program

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram.FullTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical high-incidence selection from supplied explicit scopes

The input is a framed list of scopes with original natural-number identifiers.
Every query invokes the audited source-preserving record/membership scan. The
cutoff is a supplied unary integer in this module; no arithmetic or translation
from clauses to scopes is silently performed. The fixed program appends the
strict comparison bit and advances the original-coordinate counter.
-/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Code := Cmd 10 16

def state (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (v cut : ℕ) (mask fuel : List Bool) : Data :=
  ⟨regs, ![scopeBits scopes, unary scopes.length, unary v, [], [], [], [], [],
    [], [], [], [], [], unary (cut + 1), mask, fuel]⟩

def count : Code := .call (ProgramLinking.liftProgram
  SubexpIncidenceSlotProgram.program id countPorts)

def copy (src dst tmp : Fin 16) : Code :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)
def copied (src dst : Fin 16) (a : Data) : Data :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks src dst a.stacks⟩

def compare : Code := .call (ProgramLinking.liftProgram
  Subexp.UnaryCompare.program compareRegs comparePorts)

def pushTrue (dst : Fin 16) : Code :=
  .seq (.base (.atom (.set 0 true))) (.base (.atom (.push dst 0)))
def pushedTrue (dst : Fin 16) (a : Data) : Data :=
  ⟨Function.update a.regs 0 true, Function.update a.stacks dst (true :: a.stacks dst)⟩

def emitHigh : Code := .seq (.base (.atom (.bnot 3 3))) (.base (.atom (.push 14 3)))
def emittedHigh (a : Data) : Data :=
  ⟨Function.update a.regs 3 (!a.regs 3), Function.update a.stacks 14 ((!a.regs 3) :: a.stacks 14)⟩

def query : Code := .seq count (.seq (copy 13 4 8)
  (.seq compare (.seq emitHigh (.seq (WorkspaceCleanupProgram.command 0 1 [3, 4]) (pushTrue 2)))))

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

def state (regs : Fin 2 → Bool) (mask out : List Bool) : Data := ⟨regs, ![mask, out]⟩
def pushed (b : Bool) (a : Data) : Data :=
  ⟨Function.update a.regs 0 b, Function.update a.stacks 1 (b :: a.stacks 1)⟩
def popped (regs : Fin 2 → Bool) (mask out : List Bool) : Data :=
  state (readRegs regs 0 1 mask.head?) mask.tail out

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full original-coordinate scan using a runtime unary loop counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local irreducible] query count compare
  SubexpIncidenceSlotProgram.scopeBits Subexp.IncidencePlanSpec.degree

def scanPorts : UnaryForPrograms.Ports 10 16 where
  counter := 15
  bit := 0
  flag := 1

def scan : Code := UnaryForPrograms.forCmd scanPorts query

def scanInvariant (scopes : List (List ℕ)) (cut : ℕ) (mask : List Bool)
    (i : ℕ) (d : Data) : Prop :=
  ∃ regs fuel, d = state regs scopes i cut (highPrefix scopes cut i ++ mask) fuel

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete physical preparation from explicit scopes and binary n,t.
The input contains neither scope counts, mass, cutoff, nor unary loop fuel.
All are computed by fixed finite programs. The output mask retains all n
original coordinates and is in descending original-coordinate order. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

def initial (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n t : List Bool) : Data :=
  ⟨regs, fun i => if i = 0 then scopeBits scopes else
    if i = 16 then n else if i = 17 then t else []⟩

def scanCall : Code := liftCommand scan 0 14 id scanPorts

def command : Code := .seq countCall (.seq massCall (.seq binaryCall
  (.seq cutoffCall (.seq unaryCall (.seq bump (.seq fuelCall scanCall))))))
def program := compiled command 0 14

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramRestriction
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical merge of high and free Boolean assignments in original order.
This routine never renames a variable or drops an unused coordinate. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Code := Cmd 4 4

def state (regs : Fin 4 → Bool) (mask high low out : List Bool) : Data :=
  ⟨regs, ![mask, high, low, out]⟩

def popMask : Code := .base (.atom (.pop 0 0 1))
def loadBit : Code := .ite 0 (.base (.atom (.pop 1 2 3))) (.base (.atom (.pop 2 2 3)))
def pushBit : Code := .base (.atom (.push 3 2))
def body : Code := .seq loadBit (.seq pushBit popMask)
def loop : Code := .while 1 body
def command : Code := .seq popMask loop

def popped (regs : Fin 4 → Bool) (mask high low out : List Bool) : Data :=
  state (readRegs regs 0 1 mask.head?) mask.tail high low out

def program := compiled command 0 3

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Restriction

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native streaming Horner control for arbitrary-width coefficient
representations. Arithmetic callbacks are finite commands with exact framed
traces. No loop bound or ring dimension occurs in the control table. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update binaryStep )

/-- Read one reversed coefficient cell from the reversed polynomial stream. -/
def takeCoefficient : Code :=
  .seq (takeWord 250 251 252 246 241 0 1)
    (.call (StackRoutines.reverseProgram 241 251 252 (0 : Fin 16) 1))

/-- 240 accumulator; 246 stream; 247 point; 248 counter; 250 width.
241,244,245,251,252 are restored empty; all other stacks are framed. -/
def iteration (multiply add : Code) : Code :=
  .seq (copy 247 241) (.seq (binaryStep multiply)
    (.seq (clear 241) (.seq takeCoefficient (.seq (binaryStep add) (clear 241)))))

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramLoop
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec LowFrame lowFrame_update lowFrame_refl)

def counterPorts : UnaryForPrograms.Ports 16 256 := ⟨248, 0, 1⟩

def traversal (body : Code) : Code := UnaryForPrograms.forCmd counterPorts body

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact native evaluation of a dynamically sized dense polynomial. Input
coefficients are in increasing degree order. Every other persistent stack is
preserved; the input stream and runtime counter are consumed. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpConvolutionControl
open CRTLocalProgram (ServiceSpec serviceSpec_frame lowFrame_refl lowFrame_update)

def reverseStream : Code :=
  .call (StackRoutines.reverseProgram 246 251 252 (0 : Fin 16) 1)

def command (multiply add : Code) : Code :=
  .seq reverseStream (traversal (iteration multiply add))

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HornerProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native Horner evaluation in the actual arbitrary-degree unramified
RingModel. The instruction table is independent of precision, extension
degree and polynomial length. Ring caches are explicit runtime inputs. -/
namespace SubexponentialSAT.SqrtLog.HornerProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Actual fixed Horner command, using native arbitrary-degree arithmetic. -/
def modelCommand : Code := command Services.multiply Services.add

def modelValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (P : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d))
    (x : RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  let ops := RingProgram.modelProgram t a M cache
  fold (stepValue (fun x y => (ops.mulRun x y).1) (fun x y => (ops.addRun x y).1) x)
    P.reverse ops.zeroRun.1

end SubexponentialSAT.SqrtLog.HornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryCode
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

variable {K : Type*} [DecidableEq K]

/-- Concrete coefficient-code update. Coefficients are fixed-width words;
the actual native addition above refines this finite operation exactly. -/
def insertCode (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} (k : K)
    (x : RingProgram.Code (Word (baseWidth p t)) d)
    (entries : List (K × RingProgram.Code (Word (baseWidth p t)) d)) :=
  let value := match entries.lookup k with
    | none => x
    | some y => (RingProgram.addRun (RingProgram.scalarProgram p t M cache) x y).1
  (k,value) :: (Squarefree.Sparse.erase k entries).reverse

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

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

variable {K : Type*} [DecidableEq K]

/-- Streaming order agrees semantically with normalized sparse addition;
the fixed physical loop will realize this tail-recursive traversal. -/
def run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (cache : RingProgram.ScalarCache p t) {d : ℕ} :
    List (K × RingProgram.Code (Word (baseWidth p t)) d) →
    List (K × RingProgram.Code (Word (baseWidth p t)) d) →
    List (K × RingProgram.Code (Word (baseWidth p t)) d)
  | [], seed => seed
  | a::source, seed => run p t M cache source (Dictionary.insertCode p t M cache a.1 a.2 seed)

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native control for applying computed idempotent coefficients.
The input and output ABI is documented below. The semantic execution theorem
is a separate obligation; this module supplies concrete instructions only. -/
namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram

open BitProgram StructuredCalls
open HashCircuitProgram.Native

/-- H(H-1)(H-2)=H(1-H)(2-H). The latter form reuses the checked native
complement service, whose cached constants are ordinary ring data. -/
abbrev prepareMultiplier : Cmd 8 96 := sequence
  [copy 68 61 70, complement,
   copy 61 85 70, copy 61 67 70, clear 61,
   copy 69 61 70, add,
   copy 85 61 70, productAdapter product, clear 85,
   copy 68 61 70, productAdapter product,
   makeUKey, shiftU]

/-- Input68 is raw H;78 holds the forward computed coefficient tape;88 is
an ambient shape word. Cached one69 and minus-one76 and the low56 product
environment are preserved. Output67 is the raw indicator dictionary. Scratch
61,70,79..87,89..95 must be empty initially and is reclaimed before return. -/
noncomputable def command : Cmd 8 96 := sequence
  [prepareMultiplier,
   copy 78 84 70, transfer 84 79, peekCoefficients,
   .while 7 hornerStep,
   copy 87 67 70, clear 87, clear 86, clear 94]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentApplyProgramExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Native high-register services for the quadratic and Horner steps. -/


/-! Complete native evaluation of one degree-two coefficient digit. -/


/-! The native Horner accumulator update, including every move and cleanup. -/


/-! Measured descending Horner loop over the actual computed coefficient tape. -/

namespace SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram.Native
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

abbrev applyLoop : Cmd 8 96 := sequence
  [copy 78 84 70, transfer 84 79, peekCoefficients,
   .while 7 hornerStep, copy 87 67 70, clear 87, clear 86, clear 94]

end SubexponentialSAT.SqrtLog.IdempotentApplyProgram.Steps

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native, source-preserving scalar operations on the preparation ABI.
Only the selected output changes; all low arithmetic scratch is restored. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

open BitProgram StructuredCalls ModularRingPrograms ModularDivisionPrograms
open SubexpLiftRing SubexpQuarticRing
open IdempotentProgram (storeResult storeResult_eval storedResult_stacks)

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)

theorem mul_eval (d : Data) (target left right : Fin 41)
    (x y : Word (baseWidth p t)) (h : Rest d M.bits)
    (ht : 8 ≤ target.val) (hl : 8 ≤ left.val) (hr : 8 ≤ right.val)
    (ht38 : target ≠ 38) (hl38 : left ≠ 38) (hr38 : right ≠ 38)
    (hx : d.stacks left=x.val) (hy : d.stacks right=y.val) :
    ∃ n e, Eval (binary wordMulProgram target left right) n d e ∧
      e.stacks = Function.update d.stacks target (SubexpPreparedQuartic.wordMul p t M x y).1.val ∧
      n ≤ 6000*(baseWidth p t+1)^2+23*baseWidth p t+2*(d.stacks target).length+21 := by
  obtain ⟨rf,n,hn,run⟩ := SubexpScalarMachine.wordMul_run p t M (operands d left right).regs x y
  obtain ⟨e,he,hes⟩ := binary_eval wordMulProgram d M.bits x.val y.val _ target left right
    n rf h ht hl hr ht38 hl38 hr38 hx hy run
  refine ⟨_,e,he,hes,?_⟩
  rw [x.property,y.property,(SubexpPreparedQuartic.wordMul p t M x y).1.property]
  omega

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed register language for the twelve scalar cache/temporary words.
Its interpreter is actual finite code, not a unit-cost arithmetic oracle. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing ModularRingPrograms

def Op.command : Op → Cmd 8 41
  | .add o l r => binary wordAddProgram (port o) (port l) (port r)
  | .mul o l r => binary wordMulProgram (port o) (port l) (port r)

variable (p t : ℕ) [Fact p.Prime]

def Op.eval (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t) : Op → Values p t
  | .add o l r => Function.update v o (SubexpPreparedQuartic.wordAdd p t M (v l) (v r)).1
  | .mul o l r => Function.update v o (SubexpPreparedQuartic.wordMul p t M (v l) (v r)).1

def Encoded (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t) (d : Data) : Prop :=
  Rest d M.bits ∧ ∀ i, d.stacks (port i)=(v i).val

def Frame (d e : Data) : Prop := ∀ j, (∀ i, port i≠j) → e.stacks j=d.stacks j

omit [Fact (Nat.Prime p)] in
theorem encoded_update (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (d e : Data) (o : Reg) (w : Word (baseWidth p t)) (h : Encoded p t M v d)
    (he : e.stacks=Function.update d.stacks (port o) w.val) :
    Encoded p t M (Function.update v o w) e ∧ Frame d e := by
  constructor
  · constructor
    · constructor
      · intro i
        have hi : low i≠port o := by
          intro hh
          have hv := congrArg Fin.val hh
          have hg:=port_ge o
          dsimp [low] at hv
          omega
        simpa [he,hi] using h.1.1 i
      · simpa [he,Ne.symm (port_ne38 o)] using h.1.2
    · intro i
      by_cases hi : i=o
      · subst i; simp [he]
      · have hp : port i≠port o := fun hh => hi (port_injective hh)
        simpa [he,hi,hp] using h.2 i
  · intro j hj
    simp [he,Ne.symm (hj o)]

theorem Op.command_eval (M : SubexpPreparedQuartic.Modulus p t) (v : Values p t)
    (d : Data) (op : Op) (h : Encoded p t M v d) :
    ∃ n e, Eval op.command n d e ∧ Encoded p t M (op.eval p t M v) e ∧
      Frame d e ∧ n ≤ stepBudget p t := by
  cases op with
  | add o l r =>
      obtain ⟨n,e,he,hes,hn⟩:=add_eval p t M d (port o) (port l) (port r)
        (v l) (v r) h.1 (port_ge o) (port_ge l) (port_ge r)
        (port_ne38 o) (port_ne38 l) (port_ne38 r) (h.2 l) (h.2 r)
      have hx:=encoded_update p t M v d e o _ h hes
      refine ⟨n,e,he,hx.1,hx.2,?_⟩
      rw [h.2 o,(v o).property] at hn
      dsimp [stepBudget]
      omega
  | mul o l r =>
      obtain ⟨n,e,he,hes,hn⟩:=mul_eval p t M d (port o) (port l) (port r)
        (v l) (v r) h.1 (port_ge o) (port_ge l) (port_ge r)
        (port_ne38 o) (port_ne38 l) (port_ne38 r) (h.2 l) (h.2 r)
      have hx:=encoded_update p t M v d e o _ h hes
      refine ⟨n,e,he,hx.1,hx.2,?_⟩
      rw [h.2 o,(v o).property] at hn
      dsimp [stepBudget]
      omega

def sequence : List Op → Cmd 8 41
  | [] => .base .skip
  | a::as => .seq a.command (sequence as)

def run (M : SubexpPreparedQuartic.Modulus p t) : List Op → Values p t → Values p t
  | [], v => v
  | a::as, v => run M as (a.eval p t M v)

def loopPorts : UnaryForPrograms.Ports 8 41 := ⟨40,0,7⟩

abbrev halfLoop : Cmd 8 41 := UnaryForPrograms.forCmd loopPorts (sequence halfStep)

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalarRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing

def Output (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t) (v:Values 3 t) (d:Data) : Prop :=
  Rest d M.bits ∧ d.stacks 24=[] ∧ d.stacks 25=[] ∧
    ∀i:Reg,i≠6→i≠7→d.stacks (port i)=(v i).val

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native scalar preparation contract for the 41-stack H-adic setup.
All generated constants are canonical; the selector and array builder receive
exact functional words. The only unbounded iteration uses cached unary t. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar
open BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing BinaryArithmetic

structure Prepared (t:ℕ) (M:SubexpPreparedQuartic.Modulus 3 t)
    (cache:RingProgram.ScalarCache 3 t) (u:RingProgram.ScalarCode 3 t) (d:Data) : Prop where
  table : ∀i:Fin 6,d.stacks (port (tableRegister i))=
    (IdempotentProgram.integerRun (RingProgram.scalarProgram 3 t M cache)
      (IdempotentTableEntryProgram.codeValue i)).1.val
  zero : d.stacks 17=cache.zero.val
  one : d.stacks 18=cache.one.val
  half : d.stacks 27=u.val
  minusOne : d.stacks 28=cache.minusOne.val
  twice : d.stacks 30=(SubexpPreparedQuartic.wordAdd 3 t M u u).1.val
  minusThree : d.stacks 31=(SubexpPreparedQuartic.wordMul 3 t M
    (SubexpPreparedQuartic.wordAdd 3 t M (SubexpPreparedQuartic.wordAdd 3 t M u u).1 u).1 cache.minusOne).1.val
  inverse : (2:ZMod (3^t))*wordValue 3 t u=1
  minusOneCanonical : BinaryArithmetic.toNat cache.minusOne.val < 3^t
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  oneCanonical : BinaryArithmetic.toNat cache.one.val < 3^t
  rest : Rest d M.bits
  temporary24 : d.stacks 24=[]
  temporary25 : d.stacks 25=[]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native descending-index traversal. The remaining unary counter is the
runtime index passed to the callback. Prefixing each generated word therefore
materializes the final array in increasing index order, without a precomputed
array or a value-dependent control table. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 8 41

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram.Scan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentProgramMachine
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed four-array Newton machine. Its native services perform full dynamic
vector arithmetic, operand copying, and target replacement. -/
namespace SubexponentialSAT.SqrtLog.IdempotentProgram

open BitProgram StructuredCalls SubexpSymbolicCost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

structure RegistersEncoded {B d : ℕ} (modulus width zero table degree : List Bool)
    (minusOne : RingProgram.Code (Word B) d)
    (regs : Registers (RingProgram.Code (Word B) d)) (state : RegisterData) : Prop where
  context : ServiceContext state modulus width zero table
  values : ∀ i, state.stacks (arrayRegister i) = RingProgram.flat (regs i)
  negativeUnit : state.stacks 36 = RingProgram.flat minusOne
  degree : state.stacks 37 = degree
  copyScratch : state.stacks 38 = []

end SubexponentialSAT.SqrtLog.IdempotentProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgramEncoded
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open SubexpQuarticRing

def initialRegisters (t : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t) :
    IdempotentProgram.Registers (RingProgram.Code (RingProgram.ScalarCode 3 t) (3*t)) :=
  fun _ => (IdempotentProgram.initialRun (RingProgram.scalarProgram 3 t M cache) t u).1

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IdempotentPreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed native preparation command accepts only the runtime binary
precision. It constructs its modulus, scalar cache, table, arrays and counters
with charged bit instructions, ready for the fixed Newton program. -/
namespace SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

open BitProgram StructuredCalls SubexpQuarticRing

structure Ready (t inputWidth : ℕ) (M : SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (u : RingProgram.ScalarCode 3 t) (d : Data) : Prop where
  encoded : IdempotentProgram.RegistersEncoded M.bits (List.replicate (2*t) true) cache.zero.val
    (RingTriple.tableEncoding (IdempotentProgram.tableCode (t := t) (RingProgram.scalarProgram 3 t M cache)))
    (List.replicate (3*t) true)
    (IdempotentProgram.minusOneRun (RingProgram.scalarProgram 3 t M cache) t).1
    (initialRegisters t M cache u) d
  zeroCanonical : BinaryArithmetic.toNat cache.zero.val < 3^t
  inverse : (2 : ZMod (3^t))*wordValue 3 t u=1
  counter : CounterPrograms.value (d.stacks 39)=Nat.clog 2 t
  counterLength : (d.stacks 39).length ≤ inputWidth + 1
  loopScratch : d.stacks 40=[]

end SubexponentialSAT.SqrtLog.IdempotentPreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed local cache-producer instructions and framed native service calls.
The lower256 ports are the existing arithmetic ABI; controller streams and
copy scratch occupy disjoint higher ports. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives StackRoutines

abbrev Code := Cmd 16 320

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end


