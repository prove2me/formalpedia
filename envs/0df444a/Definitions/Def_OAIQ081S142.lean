-- Prove2me | Definitions.Def_OAIQ081S142
-- name    : OAIQ081S142
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T22:50:19.463021+00:00
-- url     : https://prove2.me/theorems/8a54bb48-8094-46d7-aeef-2e7edc9a2f62
-- title:
--   Definitions bundle OAIQ081S142 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 56 declarations of OpenAI's Lean: 28 definitions, 1 inductive type or structure and 27 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.copy`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.emit`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.inverseBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.inverseValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.peek`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.reverse`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.seq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.seq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.seq`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.InterpolationCacheProgram.take`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.BuildData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.FinalData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.FlatData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.NormalizeData`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.addState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.buildState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.flatState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.normalizeState`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.wide`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeLength`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutFiberSumProgram.nativeTime`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.NativeBytes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafRingSetupProgram.nodeWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram.OuterData`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter.Overlay.transfer`, `OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisEntryCore.copy`.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLogSpace_FactorTableProgram`, `SubexponentialSAT_SqrtLogSpace_HighQueryAdapter`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgram`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramBasic`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramLengths`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan`, `SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation`, `SubexponentialSAT_SqrtLog_IrreducibleSearchControl`, `SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan`, `SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell`, `SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQuery`, `SubexponentialSAT_SqrtLog_LayoutFiberSumProgramNative`, `SubexponentialSAT_SqrtLog_LayoutProgramEntryBank`, `SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache`, `SubexponentialSAT_SqrtLog_LeafProgramConstantsModel`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase`, `SubexponentialSAT_SqrtLog_LeafRingSetupProgramNative`, `SubexponentialSAT_Subexp_GlobalBasisEntryCore`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S116`, `OAIQ081S118`, `OAIQ081S119`, `OAIQ081S120`, `OAIQ081S121`, `OAIQ081S122` and `OAIQ081S126` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S154`, `OAIQ081S155`, `OAIQ081S156`, `OAIQ081S157`, `OAIQ081S158`, `OAIQ081S159`, `OAIQ081S161`, `OAIQ081S162`, `OAIQ081S164` and `OAIQ081S165`; the statement `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalFlatten_eval`; the proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.shift_eval`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader.resume_candidate_ready`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalFlatten_eval` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S116
import Definitions.Def_OAIQ081S118
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S120
import Definitions.Def_OAIQ081S121
import Definitions.Def_OAIQ081S122
import Definitions.Def_OAIQ081S126

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_GlobalBasisEntryCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete framed-word, comparison, and scalar-cell services for the
global matrix entry callback. Register 6 is the persistent row-kind flag. -/

namespace SubexponentialSAT.Subexp.GlobalBasisEntryCore

open BitProgram StructuredCalls SubexpScanPrimitives

def copy (src dst : Fin 32) : Code := .call (StackRoutines.copyProgram src dst 31 0 1)

end SubexponentialSAT.Subexp.GlobalBasisEntryCore

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.Subexp.MatrixProgramSupport

@[simp] theorem saved_nil (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue : List Bool) :
    saved regs acc prior old queue [] = state regs acc (prior,[]) (old,[]) queue := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext j
  by_cases hj : j = 14
  · subst j; simp [ state]
  · simp [ state, hj]

def addState (regs : Fin 8 → Bool) (prior old : List Bool) : State 8 3 :=
  ⟨regs, BinaryPrograms.Add.stackState prior old []⟩

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

abbrev BuildData := State 8 19

def buildState (regs : Fin 8 → Bool) (a r queue : List Bool) : BuildData :=
  ⟨regs,fun j => if j = 15 then queue else if j = 17 then a else if j = 18 then r else []⟩

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.LayoutProgram

abbrev NormalizeData := State 8 9

def normalizeState (regs : Fin 8 → Bool) (word width buffer : List Bool) : NormalizeData :=
  ⟨regs,![word,width,buffer,[],[],[],[],[],[]]⟩

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev FlatData := State 8 19

def wide (width : List Bool) (d : State 8 18) : FlatData :=
  ⟨d.regs,fun j => if h : j.val < 18 then d.stacks ⟨j.val,h⟩ else width⟩

def flatState (regs : Fin 8 → Bool) (width : List Bool)
    (acc work next : WordPair) (queue : List Bool) : FlatData :=
  wide width (state regs acc work next queue)

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

abbrev FinalData := State 8 20

def finalState (regs : Fin 8 → Bool) (h r width queue positive negative : List Bool) : FinalData :=
  ⟨regs,fun j => if j=0 then positive else if j=1 then negative else
    if j=15 then queue else if j=17 then h else if j=18 then r else if j=19 then width else []⟩

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Values computed by the physical interpolation-cache producer. Every
entry is a typed output of an executable ring program. The uniform inverse
routine has an explicit zero-diagonal interpretation. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram

open SubexponentialSAT
open scoped BigOperators

def inverseValue (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne x : Coeff t d) : Coeff t d :=
  CRTLocalProgram.NativeInverse.value t a M cache x
    (RingProgram.modelProgram t a M cache).zeroRun.1 minusOne

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_FactorTableProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual selected-factor table runs over ambient variable IDs. Each low
payload is specialized immediately before its framed table entry is retained.
The source scratch embedding excludes persistent layout masters. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI BitProgram StructuredCalls SubexpConvolutionControl SubexpScanPrimitives
open SubexpPolynomialConstructor PerturbationAssembly OAI.Algorithms.SubexponentialSAT.SubexpLiftRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev OuterData := State 16 896

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace Overlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

def transfer : Code := .call (transferProgram 7 9 0 1)

end Overlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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

def copy (src dst : Fin 320) : Code := .call (copyProgram src dst 270 0 1)
def emit (src dst : Fin 320) : Code := .call (transferProgram src dst 0 1)
def reverse (src : Fin 320) : Code := .call (reverseProgram src 270 271 0 1)
def take (src dst : Fin 320) : Code := takeWord 104 270 271 src dst 0 1
def peek (src : Fin 320) : Code := .base (.atom (.peek src 0 15))

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed-width physical map scan. The service is an ordinary finite
subprogram, and its output is transferred into the actual packed table. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines

theorem peek_eval (s : Store) (r : Fin 16 → Bool) (src : Fin 320) :
    Eval (peek src) 1 (⟨r,s⟩ : Data) ⟨readRegs r 0 15 (s src).head?,s⟩ := by
  simpa [peek,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,
    execInstr,readRegs] using
    Eval.base (StructuredProgram.Eval.atom (StructuredProgram.Atom.peek src 0 15) (⟨r,s⟩ : Data))

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramPairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Nested native scans producing the full row-major difference-inverse
array. Every diagonal cell is computed by the same total inverse routine. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls StackRoutines
open SubexpLiftRing
def seq_p1 (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramTables
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Complete ordered native tables; all working streams are empty again. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing
def seq_p3 (a b : Code) : Code := .seq a b

def inverseBytes (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :=
  xs.flatMap fun x => RingProgram.flat (inverseValue t a M cache minusOne x)

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single fixed native interpolation-cache producer. The only data
inputs are the actual node stream and already prepared ring constants.
No inverse, negative, or pairwise table is supplied to this program. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT BitProgram StructuredCalls
open SubexpLiftRing
def seq_p0 (a b : Code) : Code := .seq a b

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_InterpolationCacheProgramLengths
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact physical output lengths for relocation and cleanup costs. -/
namespace SubexponentialSAT.SqrtLog.InterpolationCacheProgram
open SubexponentialSAT SubexpLiftRing

@[simp] theorem inverseBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :
    (inverseBytes t a M cache minusOne xs).length=xs.length*(d*baseWidth 3 t) :=
  flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs

@[simp] theorem negativeBytes_length (t : ℕ) {d : ℕ} (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (minusOne : Coeff t d) (xs : List (Coeff t d)) :
    (negativeBytes t a M cache minusOne xs).length=xs.length*(d*baseWidth 3 t) :=
  flatMap_length _ _ (fun _ => RingProgram.flat_length _) xs

end SubexponentialSAT.SqrtLog.InterpolationCacheProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrapPreparation
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed framed call generates an ordered table from a runtime unary depth.
Only its output and depth ports change; the generator's sentinel is paid for
and cleared before returning. -/


/-! Paid construction of both search tables from a single unary depth word. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls


/-- Only the input depth is supplied. The tables, count, scratch cleanup, and
register reset are all produced by the displayed fixed command. -/
theorem command_eval (depth : List Bool) (regs : Fin 22 → Bool) :
    ∃ t, t ≤ cost depth.length ∧
      Eval command t (state depth [] [] [] [] [] regs)
        (state depth (false :: depth) (tableWord depth.length)
          (tableWord ((depth.length + 1) + (depth.length + 1))) [] [] (fun _ => false)) := by
  let a0 := state depth [] [] [] [] [] regs
  let r1 := readRegs regs 0 1 none
  let a1 := state depth depth [] [] [] [] r1
  have e1 : Eval (copyCmd 14 22) (7 * depth.length + 5) a0 a1 := by
    simpa only [a0, a1, r1, state, layout14, layout22, List.append_nil, layout_update22]
      using copyCmd_eval 14 22 a0 (by decide) (by decide) (by decide) rfl
  let r2 := Function.update r1 0 false
  let a2 := state depth (false :: depth) [] [] [] [] r2
  have e2 : Eval (Subexp.TupleProgram.pushConst 22 0 false) 2 a1 a2 := by
    simpa only [a1, a2, r2, state, Subexp.TupleProgram.pushedState, layout22, layout_update22]
      using Subexp.TupleProgram.pushConst_eval 22 (0 : Fin 22) false a1
  obtain ⟨r3, e3'⟩ := pushWord_eval 10 alphabetWord a2
  let a3 := state depth (false :: depth) [] [] alphabetWord [] r3
  have e3 : Eval (pushWord 10 alphabetWord) (2 * alphabetWord.length) a2 a3 := by
    simpa only [a2, a3, state, layout10, List.append_nil, layout_update10] using e3'
  let r4 := readRegs r3 0 1 none
  let a4 := state depth (false :: depth) [] [] alphabetWord depth r4
  have e4 : Eval (copyCmd 14 6) (7 * depth.length + 5) a3 a4 := by
    simpa only [a3, a4, r4, state, layout14, layout6, List.append_nil, layout_update6]
      using copyCmd_eval 14 6 a3 (by decide) (by decide) (by decide) rfl
  have ready4 : GeneratorReady true a4 := by
    refine ⟨rfl, ?_, rfl⟩
    exact layout_low _ _ _ _ _ _
  obtain ⟨t5, r5, e5', ht5⟩ := generateAt_eval true a4 ready4
  let a5 := state depth (false :: depth) (tableWord depth.length) [] alphabetWord [] r5
  have e5 : Eval (generateAt true) t5 a4 a5 := by
    simpa [a4, a5, state, generatorOut] using e5'
  have ht5' : t5 ≤ IrreducibleSearchEnumeration.cost depth.length + 5 := ht5
  let r6 := readRegs r5 0 1 none
  let a6 := state depth (false :: depth) (tableWord depth.length) [] alphabetWord
    (false :: depth) r6
  have e6 : Eval (copyCmd 22 6) (7 * (depth.length + 1) + 5) a5 a6 := by
    simpa only [a5, a6, r6, state, layout22, layout6, List.append_nil,
      List.length_cons, layout_update6]
      using copyCmd_eval 22 6 a5 (by decide) (by decide) (by decide) rfl
  let r7 := readRegs r6 0 1 none
  let a7 := state depth (false :: depth) (tableWord depth.length) [] alphabetWord
    ((false :: depth) ++ (false :: depth)) r7
  have e7 : Eval (copyCmd 22 6) (7 * (depth.length + 1) + 5) a6 a7 := by
    simpa only [a6, a7, r7, state, layout22, layout6, List.length_cons, layout_update6]
      using copyCmd_eval 22 6 a6 (by decide) (by decide) (by decide) rfl
  have ready7 : GeneratorReady false a7 := by
    refine ⟨rfl, ?_, rfl⟩
    exact layout_low _ _ _ _ _ _
  obtain ⟨t8, r8, e8', ht8⟩ := generateAt_eval false a7 ready7
  let a8 := state depth (false :: depth) (tableWord depth.length)
    (tableWord ((depth.length + 1) + (depth.length + 1))) alphabetWord [] r8
  have e8 : Eval (generateAt false) t8 a7 a8 := by
    simpa [a7, a8, state, generatorOut, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using e8'
  have ht8' : t8 ≤ IrreducibleSearchEnumeration.cost
      ((depth.length + 1) + (depth.length + 1)) + 5 := by
    simpa only [a7, state, layout6, List.length_append, List.length_cons] using ht8
  let r9 := readRegs r8 0 1 none
  let a9 := state depth (false :: depth) (tableWord depth.length)
    (tableWord ((depth.length + 1) + (depth.length + 1))) [] [] r9
  have e9 : Eval (clearCmd 10) (2 * alphabetWord.length + 3) a8 a9 := by
    simpa only [a8, a9, r9, state, layout10, layout_update10] using clearCmd_eval 10 a8
  have e10 := RegisterResetProgram.all_eval a9
  refine ⟨_, ?_, e1.seq (e2.seq (e3.seq (e4.seq (e5.seq (e6.seq
    (e7.seq (e8.seq (e9.seq e10))))))))⟩
  dsimp only [cost]
  omega

end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact output of the fixed first-success record iterator. The measured
callback contract is discharged by the concrete coefficient checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open BitProgram StructuredCalls SubexpEnumerationPayload SubexpTupleRefinement

/-- The generic measured iterator returns precisely the original selected
coefficient vector when its concrete callback agrees with `passes`. -/
theorem encoded_searchCommand_eval {r s d : ℕ} (hd : 0 < d)
    (p : RecordPrograms.Ports r s) (predicate : Cmd r s) (output : Fin s)
    (test : List Bool → Bool) (cost : List Bool → ℕ)
    (invariant : State r s → Prop) (valid : List Bool → Prop)
    (contract : RecordPrograms.CallbackContractWithOn p predicate test cost invariant
      (fun bits _ b => b.stacks output = bits) valid)
    (hcheck : ∀ c : Fin d → F, test (encodeTuple (scalarCode 3) c) = passes c)
    (suffix : List Bool) (base : State r s)
    (hvalid : ∀ c : Fin d → F, valid (encodeTuple (scalarCode 3) c))
    (hbase : invariant base) (v pr result : Bool) :
    ∃ n next,
      n ≤ 3 + RecordPrograms.budget cost
        ((candidates d).map (encodeTuple (scalarCode 3))) ∧
      invariant next ∧
      next.stacks output = encodeTuple (scalarCode 3) (coefficients d) ∧
      Eval (Subexp.BlockSearchProgram.anyCommand p predicate) n
        (RecordPrograms.state p base v pr result
          (ProgramEncoding.encodeRecords
            ((candidates d).map (encodeTuple (scalarCode 3))) ++ suffix) [])
        (RecordPrograms.state p next false true true
          (RecordPrograms.unread test
            ((candidates d).map (encodeTuple (scalarCode 3))) suffix) []) := by
  let records := (candidates d).map (encodeTuple (scalarCode 3))
  have hf : records.find? test =
      some (encodeTuple (scalarCode 3) (coefficients d)) :=
    find_encoded_eq_coefficients hd test hcheck
  have hr : ∀ bits ∈ records, valid bits := by
    intro bits hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
    exact hvalid c
  have hany : records.any test = true := by
    apply List.any_eq_true.mpr
    exact ⟨_, List.mem_of_find?_eq_some hf, List.find?_some hf⟩
  obtain ⟨n, next, hn, hnext, history, run⟩ := RecordPrograms.iterate_run_with_on
    p predicate test cost invariant (fun bits _ b => b.stacks output = bits) valid
    contract records suffix base hr hbase v pr result
  refine ⟨n, next, hn, hnext, selected_of_visits_find output test history hf, ?_⟩
  simpa only [Subexp.BlockSearchProgram.anyCommand, hany] using run

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchNativeScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native irreducible-polynomial search: concrete factor callbacks,
saved universal scans, exact ordered candidate selection, and measured cost. -/

/-! A fixed factor-pair callback and universal scan. All checker arithmetic,
record extraction, array splitting, and cleanup use explicit bit programs. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem pair_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (hd : depth.length = d)
    (regs : Fin 16 → Bool) :
    ∃ n rf, n ≤ 14000 * (d + 1)^2 + 1 ∧ rf 3 = IrreducibleSearch.pairPass c (a,b) ∧
      Eval checkPair n
      (wide (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        false false false source [] saved count extra)
      (wide (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] rf)
        false false false source [] saved count extra) := by
  obtain ⟨rf, hv, hr⟩ := pairProgram_run c a b depth hd regs
  have hrestrict : restrictState lowRegs lowStacks
      (wide (pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs)
        false false false source [] saved count extra) =
      pairState (List.ofFn a) (List.ofFn b) (List.ofFn c) depth [] [] [] regs := by
    apply SubexpScanPrimitives.state_ext
    · funext i; simp [restrictState, wide, lowRegs]
    · funext i; simp [restrictState, wide, lowStacks]
  obtain ⟨n, hn, he⟩ := lifted_call pairProgram lowRegs lowStacks lowRegs_injective
    lowStacks_injective _ _ _ (by rw [hrestrict]; exact hr)
  exact ⟨n, rf, hn, hv, by simpa only [checkPair, embed_wide] using he⟩


theorem callback_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (a b : Fin (d + 1) → IrreducibleSearch.F)
    (depth count source saved extra : List Bool) (hd : depth.length = d)
    (hc : count.length = d + 1) (regs : Fin 16 → Bool) :
    ∃ n rf, n ≤ 15000 * (d + 1)^2 ∧ Eval callback n
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
        false true false source
        (coefficientArray (List.ofFn a ++ List.ofFn b)).reverse saved count extra)
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
        false true (IrreducibleSearch.pairPass c (a,b)) source [] saved count extra) := by
  have e1 := unpack_eval (List.ofFn a) (List.ofFn b) (List.ofFn c)
    depth count source saved extra regs
  obtain ⟨m, r2, hm, e2⟩ := split_eval (List.ofFn a) (List.ofFn b) (List.ofFn c)
    depth count source saved extra (by simpa using hc) regs
  obtain ⟨n, r3, hn, hv, e3⟩ := pair_eval c a b depth count source saved extra hd r2
  have e4 := tail_eval (List.ofFn a) (List.ofFn b) (List.ofFn c)
    depth count source saved extra r3
  rw [hv] at e4
  refine ⟨_, r3, ?_, e1.seq (e2.seq (e3.seq e4))⟩
  simp only [coefficientArray_length, List.length_append, List.length_ofFn, hc] at *
  have hd : d ≤ (d + 1) ^ 2 := by nlinarith
  have hone : 1 ≤ (d + 1) ^ 2 := by nlinarith
  omega


theorem callback_contract {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count saved extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1) :
    RecordPrograms.CallbackContractOn ports callback (factorTest c)
      (fun _ => 15000 * (d + 1)^2) (Ready c depth count saved extra)
      (fun bits => ∃ ab, pairEncode (d := d) ab = bits) := by
  intro bits tail base hb hbase
  obtain ⟨⟨a,b⟩, rfl⟩ := hb
  obtain ⟨regs, tag, present, found, source, payload, rfl⟩ := hbase
  obtain ⟨n, rf, hn, he⟩ := callback_eval c a b depth count tail saved extra hd hc regs
  let next := wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
    false true false [] [] saved count extra
  refine ⟨n, next, hn, ?_, ?_⟩
  · exact ⟨rf, false, true, false, [], [], rfl⟩
  · have hv : factorTest c (coefficientArray (List.ofFn a ++ List.ofFn b)) =
        IrreducibleSearch.pairPass c (a,b) := factorTest_encode c (a,b)
    simpa only [record_state_wide, next, pairEncode, hv] using he

theorem savedAll_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ n rf, n ≤ scanCost d ∧ Eval savedAll n
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
        tag present found [] [] (ProgramEncoding.encodeRecords (factorRecords d)) count extra)
      (wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
        false true (IrreducibleSearch.passes c) [] []
        (ProgramEncoding.encodeRecords (factorRecords d)) count extra) := by
  let saved := ProgramEncoding.encodeRecords (factorRecords d)
  let base := wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
    tag present found [] [] saved count extra
  have hbase : Ready c depth count saved extra base :=
    ⟨regs, tag, present, found, [], [], rfl⟩
  have hr : ∀ bits ∈ factorRecords d, ∃ ab, pairEncode (d := d) ab = bits := by
    intro bits hb
    obtain ⟨ab, hab, rfl⟩ := List.mem_map.mp hb
    exact ⟨ab, rfl⟩
  obtain ⟨n, next, hn, hnext, he⟩ := Subexp.BlockSearchProgram.savedAllCommand_eval
    savedPorts callback (factorTest c) (fun _ => 15000 * (d + 1)^2)
    (Ready c depth count saved extra) (fun bits => ∃ ab, pairEncode (d := d) ab = bits)
    (callback_contract c depth count saved extra hd hc) (factorRecords d) base hr hbase
    (by simp [base, wide, savedPorts, saved]) (by simp [base, wide, savedPorts]) tag present found
  obtain ⟨rf, nt, np, nf, ns, no, rfl⟩ := hnext
  refine ⟨n, rf, hn, ?_⟩
  simpa only [savedAll, savedPorts, record_state_wide, factorRecords_all, base] using he

theorem savedProgram_runsIn {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ rf, RunsIn savedProgram (scanCost d + 1)
      ((wide (pairState [] [] (List.ofFn c) depth [] [] [] regs)
        tag present found [] [] (ProgramEncoding.encodeRecords (factorRecords d)) count extra).withPC
          (some savedProgram.entry))
      ((wide (pairState [] [] (List.ofFn c) depth [] [] [] rf)
        false true (IrreducibleSearch.passes c) [] []
        (ProgramEncoding.encodeRecords (factorRecords d)) count extra).withPC none) := by
  obtain ⟨n, rf, hn, he⟩ := savedAll_eval c depth count extra hd hc regs tag present found
  exact ⟨rf, n + 1, by omega, compiled_halt_trace he 20 13⟩

end SubexponentialSAT.SqrtLog.IrreducibleSearchFactorControl

/-! Fixed first-success scan using the concrete saved factor checker. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

open BitProgram StructuredCalls IrreducibleSearchProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)
open SubexpEnumerationPayload SubexpTupleRefinement
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem check_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (depth count source extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ n rf, n ≤ IrreducibleSearchFactorControl.scanCost d + 1 ∧ Eval checkCandidate n
      (wide (readyLow (List.ofFn c) depth count d regs tag present found)
        false false false source [] extra)
      (wide (readyLow (List.ofFn c) depth count d rf false true (IrreducibleSearch.passes c))
        false false false source [] extra) := by
  obtain ⟨rf, hr⟩ := IrreducibleSearchFactorControl.savedProgram_runsIn
    c depth count [] hd hc regs tag present found
  have hrestrict : restrictState lowRegs lowStacks
      (wide (readyLow (List.ofFn c) depth count d regs tag present found)
        false false false source [] extra) = readyLow (List.ofFn c) depth count d regs tag present found := by
    apply SubexpScanPrimitives.state_ext
    · funext i; simp [restrictState, wide, lowRegs]
    · funext i; simp [restrictState, wide, lowStacks]
  obtain ⟨n, hn, he⟩ := lifted_call IrreducibleSearchFactorControl.savedProgram
    lowRegs lowStacks lowRegs_injective lowStacks_injective _ _ _
    (by rw [hrestrict]; exact hr)
  exact ⟨n, rf, hn, by simpa only [checkCandidate, embed_wide, readyLow] using he⟩

theorem callback_eval {d : ℕ} (c : Fin d → IrreducibleSearch.F)
    (old : List IrreducibleSearch.F) (hold : old.length ≤ d)
    (depth count source extra : List Bool) (hd : depth.length = d) (hc : count.length = d + 1)
    (regs : Fin 16 → Bool) (tag present found : Bool) :
    ∃ n rf, n ≤ candidateCost d ∧ Eval callback n
      (wide (readyLow old depth count d regs tag present found)
        false true false source (coefficientArray (List.ofFn c)).reverse extra)
      (wide (readyLow (List.ofFn c) depth count d rf false true (IrreducibleSearch.passes c))
        false true (IrreducibleSearch.passes c) source [] extra) := by
  have ep := prepare_eval c old depth count source extra regs tag present found
  obtain ⟨n, rf, hn, ec⟩ := check_eval c depth count source extra hd hc regs tag present found
  have ef := finish_eval c depth count source extra rf
  exact ⟨_, rf, by dsimp [candidateCost]; omega, ep.seq (ec.seq ef)⟩


theorem Ready.controls {d : ℕ} {depth count extra : List Bool} {base : Data}
    (h : Ready d depth count extra base) :
    base.stacks 14 = depth ∧ base.stacks 22 = count ∧ base.stacks 27 = extra := by
  obtain ⟨old, hold, regs, it, ip, found, ot, op, ofd, source, payload, rfl⟩ := h
  simp [wide, readyLow, IrreducibleSearchFactorControl.wide, pairState]

theorem Ready.scratch {d : ℕ} {depth count extra : List Bool} {base : Data}
    (h : Ready d depth count extra base) :
    base.stacks 15 = [] ∧ base.stacks 21 = [] ∧ base.stacks 23 = [] ∧ base.stacks 26 = [] := by
  obtain ⟨old, hold, regs, it, ip, found, ot, op, ofd, source, payload, rfl⟩ := h
  simp [wide, readyLow, IrreducibleSearchFactorControl.wide, pairState]

theorem callback_contract (d : ℕ) (depth count extra : List Bool)
    (hd : depth.length = d) (hc : count.length = d + 1) :
    RecordPrograms.CallbackContractWithOn ports callback (candidateTest d)
      (fun _ => candidateCost d) (Ready d depth count extra)
      (fun bits _ next => next.stacks 13 = bits)
      (fun bits => ∃ c : Fin d → IrreducibleSearch.F, encodeTuple (scalarCode 3) c = bits) := by
  intro bits tail base hb hbase
  obtain ⟨c, rfl⟩ := hb
  obtain ⟨old, hold, regs, it, ip, iff, ot, op, ofd, source, payload, rfl⟩ := hbase
  obtain ⟨n, rf, hn, he⟩ := callback_eval c old hold depth count tail extra hd hc regs it ip iff
  let next := wide (readyLow (List.ofFn c) depth count d rf false true (IrreducibleSearch.passes c))
    false true (IrreducibleSearch.passes c) [] [] extra
  refine ⟨n, next, hn, ?_, ?_, ?_⟩
  · exact ⟨List.ofFn c, by simp, rf, false, true, IrreducibleSearch.passes c,
      false, true, IrreducibleSearch.passes c, [], [], rfl⟩
  · simp [next, wide, readyLow, IrreducibleSearchFactorControl.wide, pairState,
      coefficientArray_ofFn]
  · simpa only [record_state_wide, next, coefficientArray_ofFn, candidateTest_encode] using he

theorem program_runsIn_ready {d : ℕ} (hd : 0 < d) (depth count extra : List Bool)
    (hdepth : depth.length = d) (hcount : count.length = d + 1) :
    ∃ final : Data, final.stacks 13 = encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients d) ∧
      Ready d depth count extra final ∧ final.stacks 25 = [] ∧ RunsIn program (searchCost d)
        ((input d depth count extra).withPC (some program.entry)) (final.withPC none) := by
  let base := wide (readyLow [] depth count d (fun _ => false) false false false)
    false false false [] [] extra
  have hb : Ready d depth count extra base :=
    ⟨[], by simp, (fun _ => false), false, false, false, false, false, false, [], [], rfl⟩
  obtain ⟨n, next, hn, hnext, hout, he⟩ := IrreducibleSearch.encoded_searchCommand_eval hd
    ports callback 13 (candidateTest d) (fun _ => candidateCost d) (Ready d depth count extra)
    (fun bits => ∃ c : Fin d → IrreducibleSearch.F, encodeTuple (scalarCode 3) c = bits)
    (callback_contract d depth count extra hdepth hcount) candidateTest_encode [] base
    (fun c => ⟨c, rfl⟩) hb false false false
  let final := RecordPrograms.state ports next false true true
    (RecordPrograms.unread (candidateTest d) (candidateRecords d) []) []
  have he' : Eval command n (input d depth count extra) final := by
    simpa only [command, Subexp.BlockSearchProgram.anyCommand, base, record_state_wide,
      List.append_nil, input, final, candidateRecords] using he
  refine ⟨final, ?_, ?_, ?_, n + 1, by dsimp [searchCost, candidateRecords]; omega, ?_⟩
  · simpa [final, RecordPrograms.state, ports] using hout
  · exact hnext.record_state false true true _ _
  · simp [final, RecordPrograms.state, ports]
  · exact compiled_halt_trace he' 24 13

end SubexponentialSAT.SqrtLog.IrreducibleSearchCandidateControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBootstrap
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


namespace SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

open BitProgram StructuredCalls
open SubexpEnumerationPayload SubexpTupleRefinement IrreducibleSearchProgram
attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod

theorem finalState_eq (depth : List Bool) :
    state depth (false :: depth) (tableWord depth.length)
      (tableWord ((depth.length + 1) + (depth.length + 1))) [] [] (fun _ => false) =
    IrreducibleSearchCandidateControl.input depth.length depth (false :: depth) [] := by
  rw [tableWord_factor]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [
 IrreducibleSearchCandidateControl.readyLow,
      IrreducibleSearchFactorControl.wide, pairState]
  · funext i
    fin_cases i <;> simp [layout,

      IrreducibleSearchCandidateControl.readyLow, IrreducibleSearchFactorControl.wide,
      pairState, tableWord, IrreducibleSearchCandidateControl.candidateRecords]

theorem bootstrap_eval (depth : List Bool) :
    ∃ t, t ≤ cost depth.length ∧ Eval command t (input depth)
      (IrreducibleSearchCandidateControl.input depth.length depth (false :: depth) []) := by
  simpa only [← input_eq, finalState_eq] using command_eval depth (fun _ => false)

theorem searchCommand_eval (depth : List Bool) (hd : 0 < depth.length) :
    ∃ (t : ℕ) (final : Data), t + 1 ≤ totalCost depth.length ∧
      final.stacks 13 = encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients depth.length) ∧
      IrreducibleSearchCandidateControl.Ready depth.length depth (false :: depth) [] final ∧
      final.stacks 25 = [] ∧ Eval searchCommand t (input depth) final := by
  obtain ⟨t, ht, he⟩ := bootstrap_eval depth
  obtain ⟨final, hout, hready, h25, u, hu, hr⟩ :=
    IrreducibleSearchCandidateControl.program_runsIn_ready hd depth (false :: depth) [] rfl rfl
  refine ⟨t + u, final, ?_, hout, hready, h25,
    he.seq (.call IrreducibleSearchCandidateControl.program hr)⟩
  dsimp only [totalCost]
  omega

theorem searchProgram_runsIn (depth : List Bool) (hd : 0 < depth.length) :
    ∃ final : Data, final.stacks 13 =
        encodeTuple (scalarCode 3) (IrreducibleSearch.coefficients depth.length) ∧
      IrreducibleSearchCandidateControl.Ready depth.length depth (false :: depth) [] final ∧
      final.stacks 25 = [] ∧ RunsIn searchProgram (totalCost depth.length)
        ((input depth).withPC (some searchProgram.entry)) (final.withPC none) := by
  obtain ⟨t, final, ht, hout, hready, h25, he⟩ := searchCommand_eval depth hd
  exact ⟨final, hout, hready, h25, t + 1, ht, compiled_halt_trace he 14 13⟩


end SubexponentialSAT.SqrtLog.IrreducibleSearchBootstrap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramConstantsModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The generated dynamic vectors are constants in the supplied ring model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Constants

open SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.SubexpLiftRing RingProgramTable
open scoped BigOperators

theorem constantCode_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) (seed zeroWord : RingProgram.ScalarCode 3 t)
    (hz : wordValue 3 t zeroWord = 0) :
    (RingProgram.modelRing t ht hd model M cache).decode (constantCode d seed zeroWord) =
      SubexponentialSAT.LiftRing.of (model.F t) (wordValue 3 t seed) := by
  classical
  change (∑ i : Fin d, SubexponentialSAT.LiftRing.of (model.F t)
    (wordValue 3 t (constantCode d seed zeroWord i)) * RingBasis.basis (model.F t) i) = _
  rw [Finset.sum_eq_single (⟨0,hd⟩ : Fin d)]
  · simp [constantCode,RingBasis.basis]
  · intro i _ hi
    have hv : i.val ≠ 0 := by intro h; apply hi; exact Fin.ext h
    simp [constantCode,hv,hz]
  · simp

theorem one_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (RingProgram.modelRing t ht hd model M cache).decode
      (constantCode d cache.one cache.zero) = 1 := by
  rw [constantCode_decode t ht hd model M cache _ _ cache.zero_correct,cache.one_correct,map_one]

theorem zero_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (RingProgram.modelRing t ht hd model M cache).decode
      (constantCode d cache.zero cache.zero) = 0 := by
  rw [constantCode_decode t ht hd model M cache _ _ cache.zero_correct,cache.zero_correct,map_zero]

theorem minusOne_decode (t : ℕ) (ht : 0 < t) {d : ℕ} (hd : 0 < d)
    (model : RingModel.Data d) (M : SubexponentialSAT.SubexpPreparedQuartic.Modulus 3 t)
    (cache : RingProgram.ScalarCache 3 t) :
    (RingProgram.modelRing t ht hd model M cache).decode
      (constantCode d cache.minusOne cache.zero) = -1 := by
  rw [constantCode_decode t ht hd model M cache _ _ cache.zero_correct,cache.minusOne_correct,
    map_neg,map_one]

end SubexponentialSAT.SqrtLog.LeafProgram.Constants

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafRingSetupProgramBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/- Component: LeafRingSetupProgramScalar.lean -/

/-! The first concrete stage of ring setup.  Only the runtime binary
precision is supplied.  The generated scalar cache remains exposed while
the extension-ring table and constants are built.  The idempotent producer
later uses a separately framed preparation, with its own charged cost. -/

/-! Actual irreducible search followed by coefficient padding.  The model
below is the one selected by the finite search, not a supplied polynomial. -/

/-! Table generation for the cache produced by the native scalar stage.
The cache is not replaced by a separately chosen mathematical cache. -/

/-! Physical node generation and record framing at the ring-setup ports. -/
namespace SubexponentialSAT.SqrtLog.LeafRingSetupProgram

open BitProgram StructuredCalls SubexpLiftRing

def nodeWords (t d Q : ℕ) : List (RingProgram.Code (RingProgram.ScalarCode 3 t) d) :=
  (List.finRange Q).map fun i => RingNodeProgram.nodeCode t d (i.val+1)

@[simp] theorem nodeWords_length (t d Q : ℕ) : (nodeWords t d Q).length = Q := by
  simp [nodeWords]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

/- Component: LeafRingSetupProgramConstants.lean -/

/-! Actual constant-vector and idempotent calls in the setup workspace. -/

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
open SubexpLiftRing SubexpQuarticRing

structure NativeBytes (t d : ℕ) (model : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (a : Data) : Prop where
  modulus : a.stacks 194 = M.bits
  width : (a.stacks 202).length = baseWidth 3 t
  zero : a.stacks 203 = cache.zero.val
  table : a.stacks 201 = RingTriple.tableEncoding (HornerProgram.modelTable t model M cache)
  degree : (a.stacks 204).length = d
  fullZeroLength : (a.stacks 280).length = d*baseWidth 3 t
  clean : ∀ i ∈ ReconstructionProgram.InputReady.emptyPorts,
    a.stacks (i.castLE (by decide))=[]

end SubexponentialSAT.SqrtLog.LeafRingSetupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutDenominatorProgramQuery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A denominator constructor consuming the actual ring-setup certificate.
The inverse-half fact comes from that executed setup, and the power is then
computed by the fixed native multiplication loop in the private bank. -/
namespace SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery
open SubexponentialSAT BitProgram StructuredCalls SubexpSetupStorage
open SubexpLiftRing SubexpQuarticRing IntegerRingLiftProgram

/-- The storage cost is linear in the largest physically present word. The
remaining budget is the checked polynomial native denominator budget. -/
theorem budget_polynomial (R t d W : ℕ) :
    budget R t d W ≤ LayoutDenominatorProgram.polynomialBudget R (baseWidth 3 t) d + 600*(W+2) :=
  Nat.add_le_add_right (LayoutDenominatorProgram.budget_polynomial R t d) _

end SubexponentialSAT.SqrtLog.LayoutDenominatorProgramQuery

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramEntryBank
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The concrete incidence-entry program. Its read-only cache bank is200..211,
its input indices252/253, and the returned signed pair254/255. Ports212..251
belong to the caller and are outside every local subroutine map. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

abbrev Data := State 16 256

end SubexponentialSAT.SqrtLog.LayoutProgram.EntryBank

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutFiberSumProgramNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Discharge the fiber loop's callback by the concrete integer-entry machine.
All remaining assumptions describe its actual caches and numerical bounds. -/
namespace SubexponentialSAT.SqrtLog.LayoutFiberSumProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp SubexponentialSAT.MulticolorTypes
open SubexponentialSAT.Subexp.ConstructivePacking RowSelectionProgram

def nativeLength (R : ℕ) (width : List Bool) (power : WordPair) : ℕ :=
  LayoutProgram.EntryBank.integerLength R width.length (pairLength power) power.1.length

def nativeTime (r Q R : ℕ) (width : List Bool) (power : WordPair)
    (aWord : List Bool) (S U : ℕ) : ℕ :=
  U+LayoutProgram.EntryBank.integerBudget r Q aWord.length R width.length
    (pairLength power) power.1.length+550*S+450*nativeLength R width power+1200

end SubexponentialSAT.SqrtLog.LayoutFiberSumProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramIntegerCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid reusable integer-cache initialization. The runtime parameters A, R
and common width remain on20/21/22. Outputs are H-positive0, H-negative1,
binary clearing denominator2, and retained local width19. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram LayoutProgramScalar

abbrev Data := State 8 24

end SubexponentialSAT.SqrtLog.LayoutProgram.IntegerCache

end OAI.Algorithms
end


