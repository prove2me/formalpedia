-- Prove2me | Definitions.Def_OAIQ081S008
-- name    : OAIQ081S008
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:23:11.94623+00:00
-- url     : https://prove2.me/theorems/743ecc47-0213-4717-8739-45af7a0c021e
-- title:
--   Definitions bundle OAIQ081S008 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 150 declarations of OpenAI's Lean: 140 definitions, 1 inductive type or structure and 9 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.bytesBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.fetchBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.literalBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negativeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.normalizeBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.payloadBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.productBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.programBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.rowBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.scaleBound`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold.value`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold.work`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.baseHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause.recordHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback.outputHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.highPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.lowPort`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory.tapes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.ProductCallback.resultHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.baseHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.recordHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.accumulatedHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks.complementedHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.arithmeticPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.literalStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.openedHigh`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.productPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.rowStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.canonicalRegs`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.decodeRegisters`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.decodeStacks`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily.Candidate`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily.CoeffTuple`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily.IndexTuple`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily.candidateDigitsEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily.candidateEquivFin`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashFamily.decodeDigits` and 101 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative`, `SubexponentialSAT_SqrtLog_HashCircuitProgramCanonical`, `SubexponentialSAT_SqrtLog_HashCircuitProgramCostModel`, `SubexponentialSAT_SqrtLog_HashCircuitProgramDynamicFold`, `SubexponentialSAT_SqrtLog_HashCircuitProgramFrame`, `SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter`, `SubexponentialSAT_SqrtLog_HashCircuitProgramLiteralMemory`, `SubexponentialSAT_SqrtLog_HashCircuitProgramMemory`, `SubexponentialSAT_SqrtLog_HashCircuitProgramRowMemory`, `SubexponentialSAT_SqrtLog_HashFamily`, `SubexponentialSAT_SqrtLog_HashFamilyDigits`, `SubexponentialSAT_SqrtLog_HashFamilyEnumeration`, `SubexponentialSAT_SqrtLog_HashInput`, `SubexponentialSAT_SqrtLog_HashInputProgramFrame`, `SubexponentialSAT_SqrtLog_HashInputProgramLoop`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopDecode`, `SubexponentialSAT_SqrtLog_HashInputProgramLoopTerm`, `SubexponentialSAT_SqrtLog_HashInputProgramSource`, `SubexponentialSAT_SqrtLog_HashParametersProgramFinal`, `SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource`, `SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls`, `SubexponentialSAT_SqrtLog_HashScopeProgramNativeCost`, `SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawCall`, `SubexponentialSAT_SqrtLog_HashScopeProgramRawTable`, `SubexponentialSAT_SqrtLog_HashScopeProgramSemantics`, `SubexponentialSAT_SqrtLog_HashScopeProgramSingle`, `SubexponentialSAT_SqrtLog_HashSelectProgramGenerate`, `SubexponentialSAT_SqrtLog_LeafParametersProgramNative`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase`, `SubexponentialSAT_SqrtLog_MomentsProgramDictionaryCode`, `SubexponentialSAT_SqrtLog_MomentsProgramNormalize`, `SubexponentialSAT_SqrtLog_MomentsProgramProduct`, `SubexponentialSAT_SqrtLog_MomentsProgramProductBounds`, `SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram`, `SubexponentialSAT_SqrtLog_SquarefreeMask`, `SubexponentialSAT_SqrtLog_SquarefreeProgramErase`, `SubexponentialSAT_SqrtLog_SquarefreeProgramLess`, `SubexponentialSAT_SqrtLog_SquarefreeProgramLookup`, `SubexponentialSAT_SqrtLog_SquarefreeProgramNat`, `SubexponentialSAT_SqrtLog_SquarefreeProgramRead`, `SubexponentialSAT_SqrtLog_SquarefreeProgramReplace`, `SubexponentialSAT_SqrtLog_SquarefreeScaleProgram`, `SubexponentialSAT_SqrtLog_SquarefreeSparse`, `SubexponentialSAT_SubexpChunkRecordMap`, `SubexponentialSAT_SubexpLayoutFactorBounds`, `SubexponentialSAT_SubexpLiteralChunkProgram`, `SubexponentialSAT_SubexpRecordScan`, `SubexponentialSAT_SubexpScopeProducer`, `SubexponentialSAT_Subexp_SelectorProgram`, `SubexponentialSAT_Truncation`.
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S030`, `OAIQ081S031`, `OAIQ081S032`, `OAIQ081S035`, `OAIQ081S036`, `OAIQ081S037`, `OAIQ081S038`, `OAIQ081S039`, `OAIQ081S042` and `OAIQ081S043`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Truncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Canonical truncation before substitution

Polynomials are represented with U outermost, Z in the middle, and the X variables
innermost.  Truncation is an operation on canonical polynomial representatives;
we never assert that U = 1 defines a map out of the truncated quotient.
-/

namespace SubexponentialSAT.Truncation

noncomputable section

open scoped BigOperators

variable {R ι : Type*} [CommSemiring R]

/-- Apply an additive map to every polynomial coefficient. -/
def mapCoeffs {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) : Polynomial A →+ Polynomial B where
  toFun P := Polynomial.ofFinsupp (.ofCoeff (P.toFinsupp.coeff.mapRange f f.map_zero))
  map_zero' := by ext j; simp [Polynomial.coeff]
  map_add' P Q := by
    ext j
    rw [Polynomial.coeff_add]
    change f ((P + Q).coeff j) = f (P.coeff j) + f (Q.coeff j)
    rw [Polynomial.coeff_add, map_add]

@[simp] theorem coeff_mapCoeffs {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (P : Polynomial A) (j : ℕ) :
    (mapCoeffs f P).coeff j = f (P.coeff j) := by
  rfl

@[simp] theorem mapCoeffs_monomial {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+ B) (j : ℕ) (a : A) :
    mapCoeffs f (Polynomial.monomial j a) = Polynomial.monomial j (f a) := by
  ext r
  simp only [coeff_mapCoeffs, Polynomial.coeff_monomial]
  split_ifs <;> simp_all

end

end SubexponentialSAT.Truncation

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSparse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Computable normalized sparse coefficient lists. Zero coefficients may stay
in the list; keys are unique, so this does not enlarge the finite index bound.
No equality decision for coefficients or full ambient Boolean table is used. -/

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {K R A : Type*} [DecidableEq K] [AddCommMonoid R]

abbrev Data (K R : Type*) := List (K × R)

def keys (l : Data K R) : List K := l.map Prod.fst

def fetch (k : K) : Data K R → R
  | [] => 0
  | (j, c) :: l => (if j = k then c else 0) + fetch k l

def erase (k : K) (l : Data K R) : Data K R := l.filter (fun a => decide (a.1 ≠ k))

section Decode

variable [AddCommMonoid A]

def decode (atom : K → R → A) : Data K R → A
  | [] => 0
  | (k, c) :: l => atom k c + decode atom l

end Decode
end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpRecordScan
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

def lowRegs : Fin 2 → Fin 5 := Fin.castAdd 3

def onlyInput : Fin 1 → Fin 6 := fun _ => 0

abbrev storage (input key query work tmp output : List Bool) : Fin 6 → List Bool :=
  fun j => if j = 0 then input else if j = 1 then key else if j = 2 then query
    else if j = 3 then work else if j = 4 then tmp else output

/-- The exact structured execution bound for one serialized inner record. -/
def recordCost (key query payload : List Bool) : ℕ :=
  17 * key.length + 9 * query.length + 13 * payload.length + 36

end SubexponentialSAT.SubexpRecordScan

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SelectorProgram
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

open SubexponentialSAT.SubexpRecordScan

abbrev scanBudget (query : List Bool) : List (List Bool × List Bool) → ℕ
  | [] => 1
  | (key, value) :: records => recordCost key query value + 4 + scanBudget query records

end SubexponentialSAT.Subexp.SelectorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLookup
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

open SubexponentialSAT.SubexpRecordScan

variable {K C : Type*} [DecidableEq K]

def encodeDictionary (key : K → List Bool) (coeff : C → List Bool)
    (entries : Sparse.Data K C) : List (List Bool × List Bool) :=
  entries.map (fun a => (key a.1, coeff a.2))

abbrev lookupBudget := SubexponentialSAT.Subexp.SelectorProgram.scanBudget

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramCanonical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct native incidence evaluation from original unary CNF literal records.
This module composes the paid literal decoder with the paid dictionary lookup;
no preprocessing assumption converts literal numbers into variable keys. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram

def decodeRegisters : Fin 4 → Fin 6 := ![0,1,2,5]
def decodeStacks : Fin 2 → Fin 7 := ![2,0]

def canonicalRegs (regs : Fin 5 → Bool) : Fin 5 → Bool := ![false,false,true,regs 3,regs 4]

end SubexponentialSAT.SqrtLog.HashCircuitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

def literalRegisters : Fin 6 → Fin 8 := Fin.castAdd 2
def literalStacks (i : Fin 7) : Fin 96 := ⟨56+i.val,by omega⟩

/-- The weighted record opener consumes50 and writes original clause bytes47
and reversed flat weight49. Ports41,59,60 are scratch shared with lookup. -/
def rowRegisters : Fin 5 → Fin 8 := Fin.castAdd 3
def rowStacks : Fin 6 → Fin 96 := ![66,57,63,59,60,65]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Split-memory rules for composing the actual low arithmetic workspace with
persistent high interpreter data. All movement lemmas retain primitive costs. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

def lowPort : Fin 56 → Fin 96 := Fin.castAdd 40
def highPort : Fin 40 → Fin 96 := Fin.natAdd 56

def tapes (low : Fin 56 → List Bool) (high : Fin 40 → List Bool) : Fin 96 → List Bool :=
  fun i => Fin.addCases (m := 56) (n := 40) low high i

@[simp] theorem tapes_low (low high) (i : Fin 56) : tapes low high (lowPort i) = low i := by
  simp [tapes,lowPort]
@[simp] theorem tapes_high (low high) (i : Fin 40) : tapes low high (highPort i) = high i := by
  simp [tapes,highPort]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramErase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete one-record deletion for sparse coefficient dictionaries. The
selected key is saved before comparison; retained records are emitted intact. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.SubexpRecordScan

def frameRegPorts : Fin 3 → Fin 5 := Fin.castAdd 2
def frameStackPorts : Fin 2 → Fin 7 := ![6,5]

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramReplace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual dictionary replacement: delete all old matching keys, then prepend
one supplied coefficient. This is the storage phase of additive insertion;
the coefficient addition itself is a separately measured ring operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

def replaceRegPorts : Fin 3 → Fin 5 := Fin.castAdd 2
def replaceStackPorts : Fin 3 → Fin 8 := ![2,7,5]

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed physical dictionary-insertion program. All dictionary/key/vector
lengths are input data. The complete semantic composition is proved separately;
this file defines the finite table and its paid stack primitives. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

def smallRegs : Fin 5 → Fin 8 := Fin.castAdd 3
def lookupStacks : Fin 6 → Fin 27 := ![18,19,16,20,21,22]
def replaceStacks : Fin 8 → Fin 27 := ![15,19,16,20,21,25,18,26]
def nativeStacks : Fin 15 → Fin 27 := Fin.castAdd 12

/-- The parser's destination is reversed; transferring it to native stack9
restores the old coefficient vector to forward order before addition. -/
def parseRegisters : Fin 5 → Fin 8 := smallRegs
def parseStacks : Fin 6 → Fin 27 := ![22,8,19,20,21,23]

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramDictionaryCode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

variable {K : Type*} [DecidableEq K]

def codeBranchBudget (B d : ℕ) : ℕ := d * (6000 * (B+1)^2 + 50*B + 36) + 23

end SubexponentialSAT.SqrtLog.MomentsProgram.Dictionary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree

def encodeMask {n : ℕ} (s : Finset (Fin n)) : List Bool :=
  List.ofFn (fun i => decide (i ∈ s))

@[simp] theorem encodeMask_length {n : ℕ} (s : Finset (Fin n)) : (encodeMask s).length = n := by
  simp [encodeMask]

end SubexponentialSAT.SqrtLog.Squarefree

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramNat
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed primitive unary-field reader used by encoded sparse-key joins.
The unary magnitude affects execution time, never the instruction table. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

def natRegs : Fin 2 → Fin 5 := Fin.castAdd 3

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramRead
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A native two-frame reader for the 28-stack dictionary normalization ABI.
All ports outside 16,17,18,27 and registers outside 0,1 are preserved. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

def frameReadRegs : Fin 2 → Fin 8 := Fin.castAdd 6

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramNormalize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms



namespace SubexponentialSAT.SqrtLog.MomentsProgram.Normalize

def lower : Fin 27 → Fin 28 := Fin.castSucc

end SubexponentialSAT.SqrtLog.MomentsProgram.Normalize


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeProgramLess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed unary comparison with explicit residual-length bounds and paid
cleanup. Register 4 is a caller-owned Boolean saved across this operation. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program

def lessRegs : Fin 4 → Fin 5 := Fin.castAdd 1

end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeKeyMapProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

def regs5 : Fin 5 → Fin 8 := Fin.castAdd 3
def regs3 : Fin 3 → Fin 8 := Fin.castAdd 5
def joinPorts : Fin 3 → Fin 15 := ![9,8,10]
def clipPorts : Fin 4 → Fin 15 := ![11,12,13,14]
def emitPorts : Fin 3 → Fin 15 := ![10,6,4]

end SubexponentialSAT.SqrtLog.Squarefree.KeyMapProgram

/-! Public native sparse-key mapper. The instruction table is independent of
the keys, clipping limits, coefficient width, and dictionary length. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeScaleProgram
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

def nativePorts : Fin 32 → Fin 40 := Fin.castAdd 8

def frameRegs : Fin 3 → Fin 8 := Fin.castAdd 5
def framePorts (src : Fin 40) : Fin 2 → Fin 40 := ![src, 37]

end SubexponentialSAT.SqrtLog.Squarefree.ScaleProgram

/-! Moves stage. -/

/-! Emit stage. -/

/-! Native stage. -/

/-! Loop stage. -/

/-! Cost stage. -/

/-! Semantics stage. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! A fixed sparse-product instruction table. Its three subservices perform
coefficient scaling, key join/clipping, and additive normalization, respectively.
All outer source lengths and ring dimensions live on tape. -/
namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product

def scalePorts : Fin 40 → Fin 56 := Fin.castAdd 16

def keyPorts : Fin 15 → Fin 56 := ![0,1,2,3,4,6,7,8,9,10,11,13,14,15,16]

def normalizePorts (i : Fin 28) : Fin 56 :=
  if i = 15 then 42 else if i = 17 then 49 else if i = 22 then 50 else
  if i = 24 then 51 else Fin.castAdd 28 i

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product

structure Store where
  modulus : List Bool := []
  width : List Bool := []
  zero : List Bool := []
  table : List Bool := []
  degree : List Bool := []
  left : List Bool := []
  right : List Bool := []
  acc : List Bool := []
  key : List Bool := []
  coeff : List Bool := []
  uCap : List Bool := []
  zCap : List Bool := []
  scaled : List Bool := []
  mapped : List Bool := []
  scaleSource : List Bool := []
  scalar : List Bool := []
  keySource : List Bool := []
  keyLeft : List Bool := []
  keyUCap : List Bool := []
  keyZCap : List Bool := []
  normalSource : List Bool := []
  normalCount : List Bool := []
  reversedCoeff : List Bool := []

def tapes (s : Store) : Fin 56 → List Bool := fun i =>
  if i=0 then s.keySource else if i=1 then s.keyLeft else
  if i=2 then s.keyUCap else if i=3 then s.keyZCap else
  if i=4 then s.mapped else if i=5 then s.modulus else
  if i=12 then s.width else if i=17 then s.zero else
  if i=22 then s.table else if i=27 then s.normalSource else
  if i=32 then s.scaleSource else if i=34 then s.scalar else
  if i=38 then s.scaled else if i=39 then s.degree else
  if i=40 then s.left else if i=41 then s.right else
  if i=42 then s.acc else if i=43 then s.key else
  if i=44 then s.coeff else if i=45 then s.uCap else
  if i=46 then s.zCap else if i=48 then s.reversedCoeff else
  if i=51 then s.normalCount else []

end SubexponentialSAT.SqrtLog.MomentsProgram.Product


end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative
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

def arithmeticPorts : Fin 56 → Fin 96 := Fin.castAdd 40

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-! Component: HashCircuitProgram. All public namespaces and APIs are retained. -/


/-! The fixed native sparse-hash row instruction table. All arithmetic
components are now concrete native programs: there are no operation-valued
parameters in `command` or `program`. The complete serialized semantic and
primitive-time theorem must additionally discharge the local callback
contracts for this table; no such theorem is asserted merely by compilation. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

def productPorts : Fin 56 → Fin 96 := Fin.castAdd 40

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-! Component: HashCircuitProgramMemoryExtra. All public namespaces and APIs are retained. -/


namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

@[simp] theorem update_product_left (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 40 w =
      MomentsProgram.Product.tapes {s with left := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
@[simp] theorem update_product_right (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 41 w =
      MomentsProgram.Product.tapes {s with right := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
@[simp] theorem update_product_acc (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 42 w =
      MomentsProgram.Product.tapes {s with acc := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]
@[simp] theorem update_product_coeff (s : MomentsProgram.Product.Store) (w : List Bool) :
    Function.update (MomentsProgram.Product.tapes s) 44 w =
      MomentsProgram.Product.tapes {s with coeff := w} := by
  funext i; fin_cases i <;> simp [MomentsProgram.Product.tapes]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

/-! Component: HashCircuitProgramWeightedCallbacks. All public namespaces and APIs are retained. -/


/-! The two concrete weighted arithmetic adapters used by the hash evaluator.
The statements expose exact dictionary bytes and restoration of the common
arithmetic workspace. In particular they do not assume callback correctness. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks
open MomentsProgram
open Memory

variable {K : Type*} [DecidableEq K]

def complementedHigh (high : Fin 40 → List Bool) (result : List Bool) :=
  Function.update (Function.update high (5 : Fin 40) []) (5 : Fin 40) result

def accumulatedHigh (high : Fin 40 → List Bool) (result : List Bool) :=
  Function.update (Function.update (Function.update (Function.update high
    (9 : Fin 40) []) (11 : Fin 40) []) (12 : Fin 40) []) (12 : Fin 40) result

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.WeightedCallbacks

/-! Component: HashCircuitProgramProduct. All public namespaces and APIs are retained. -/


/-! Concrete product callback refinement. Both sparse operands are copied from
persistent interpreter stacks into the real product program. The result is
copied back, and all temporary operands are physically reclaimed. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
namespace ProductCallback

def resultHigh (high : Fin 40 → List Bool) (result : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update high 11 []) 5 []) 11 result

end ProductCallback
end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_MomentsProgramProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.MomentsProgram.Product

/-- Explicit polynomial envelope for one outer product iteration. -/
def stepEnvelope (B d n u J N r : ℕ) : ℕ :=
  let W := n+u+J
  let C := d*B
  11*W+20*C+9*u+9*J+9*d+100 + r *
    (25*(2*W+2*C+2) +
     (40000*(d+1)^3*(B+1)^2+35*C+7*d+22*W+57) +
     (100*(n+u+J+C+2)+2) +
     (220*(N+1)*(W+C+1)+Dictionary.codeBranchBudget B d+2))

end SubexponentialSAT.SqrtLog.MomentsProgram.Product

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramCostModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical polynomial envelopes for the native hash-row program.
HashCircuitProgramCost relates these expressions to actual execution. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost
open MomentsProgram

/-- Bit length of a normalized dictionary with at most S retained keys. -/
def bytesBound (B d n u J S : ℕ) : ℕ := S*(2*(n+u+J)+2*(d*B)+2)
def scaleBound (B d n u J S : ℕ) : ℕ :=
  S*(40000*(d+1)^3*(B+1)^2+35*(d*B)+7*d+22*(n+u+J)+57)+5
def normalizeBound (B d n u J S : ℕ) : ℕ :=
  S*(220*(2*S+1)*(n+u+J+d*B+1)+Dictionary.codeBranchBudget B d+2)+1
def productBound (B d n u J S : ℕ) : ℕ :=
  S*(Product.stepEnvelope B d n u J (S*S) S+2)+1
def fetchBound (n P : ℕ) : ℕ := n*(44*n+31*P+58)+2*n+16
def negativeBound (B d n u J S : ℕ) : ℕ :=
  52*bytesBound B d n u J S+18*(d*B)+9*d+
    scaleBound B d n u J S+normalizeBound B d n u J S+73
def literalBound (B d n u J S : ℕ) : ℕ :=
  let P := bytesBound B d n u J S
  8*n+16+fetchBound n P+9*P+10+negativeBound B d n u J S+1+
    29*P+productBound B d n u J S+29+3
def payloadBound (B d n k : ℕ) : ℕ := 2*(d*B)+2+(4*n+4)*k
def rowBound (B d n u J S k : ℕ) : ℕ :=
  let P := bytesBound B d n u J S
  3*payloadBound B d n k+6*(d*B)+8+(7*P+5)+
    (3+k*(6*(2*n+1)+literalBound B d n u J S+7))+
    (54*P+14*(d*B)+9*d+scaleBound B d n u J S+normalizeBound B d n u J S+74)+3
def programBound (B d n u J S k m : ℕ) : ℕ :=
  7+m*(6*payloadBound B d n k+rowBound B d n u J S k+7)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramDynamicFold
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured physical record fold with accumulator-dependent cost. This
retains the actual fixed callback and parser; the cost recurrence can account
for changing sparse dictionary lengths without postulating a uniform bound. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold

variable {r s : ℕ} {R A : Type*}

abbrev value (step : R → A → A) : List R → A → A
  | [], a => a
  | x::xs, a => value step xs (step x a)

abbrev work (encode : R → List Bool) (step : R → A → A) (cost : R → A → ℕ) : List R → A → ℕ
  | [], _ => 0
  | x::xs, a => 6*(encode x).length+cost x a+7+work encode step cost xs (step x a)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramLiteralMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

/-- The fetcher resets its six work words and retains the saved incidence table. -/
def literalHigh (high : Fin 40 → List Bool) (payload table : List Bool) : Fin 40 → List Bool :=
  fun i => Fin.addCases (m := 7) (n := 33) ![[],[],[],[],[],payload,table] (fun j => high (Fin.natAdd 7 j)) i

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramRowMemory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact frame for unpacking an inline weighted clause into the two physical
operands used by the clause loop and weighted accumulator. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

def openedHigh (high : Fin 40 → List Bool) (clause weight : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update high 10 []) 1 []) 7 clause) 3 []) 4 []) 9 weight

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff


/-! Component: HashCircuitProgramLiteralCallback. All public namespaces and APIs are retained. -/


/-! Literal callback with actual lookup, polarity, sparse product, and return.
The represented minus-one and one values are explicit cached inputs. All work
is performed by the fixed native commands wired into the row interpreter. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback
open MomentsProgram

variable (p t : ℕ)
  [Fact p.Prime]
variable {n d : ℕ}

def outputHigh (high : Fin 40 → List Bool) (table result : List Bool) : Fin 40 → List Bool :=
  Function.update (literalHigh high [] table) 11 result

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback

/-! Component: HashCircuitProgramClause. All public namespaces and APIs are retained. -/


/-! Typed clause traversal using the fixed native literal callback. Input is
still the original unary literal encoding; the type is used only to specify
which dictionary entry the native decoder and lookup retrieve. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open MomentsProgram

def baseHigh (high : Fin 40 → List Bool) (acc : List Bool) : Fin 40 → List Bool :=
  Function.update (literalHigh high [] (high 6)) 11 acc

def recordHigh (high : Fin 40 → List Bool) (acc src payload : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (baseHigh high acc) 7 src) 2 payload

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

/-! Component: HashCircuitProgramRow. All public namespaces and APIs are retained. -/


/-! The actual nested hash-row interpreter. The only inputs below are serialized
literal clauses, flat represented scalars, the selected incidence dictionary,
and the ring/cache words used by the native services. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open MomentsProgram

def baseHigh (high : Fin 40 → List Bool) (acc : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Clause.baseHigh high []) 7 []) 9 []) 10 []) 12 acc

def recordHigh (high : Fin 40 → List Bool) (acc src payload : List Bool) : Fin 40 → List Bool :=
  Function.update (Function.update (baseHigh high acc) 8 src) 10 payload

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

abbrev IndexTuple (m d : ℕ) := Fin d → Fin m
abbrev CoeffTuple (d : ℕ) := Fin d → ZMod 3
abbrev Candidate (m d : ℕ) := IndexTuple m d × CoeffTuple d

def eval {m d : ℕ} (h : Candidate m d) (v : Fin m → ZMod 3) : ZMod 3 :=
  ∑ j, h.2 j * v (h.1 j)

def supportCard {m : ℕ} (v : Fin m → ZMod 3) : ℕ :=
  (univ.filter fun i => v i ≠ 0).card

def detectingCard {m d : ℕ} (v : Fin m → ZMod 3) : ℕ :=
  (univ.filter fun h : Candidate m d => eval h v ≠ 0).card

/-- Repeated coordinate occurrences are combined in the ternary field. -/
def row {m d : ℕ} (h : Candidate m d) : Fin m → ZMod 3 := fun i =>
  ∑ j, if h.1 j = i then h.2 j else 0

def hitCard {m d : ℕ} (v : Fin m → ZMod 3) : ℕ :=
  (univ.filter fun e : IndexTuple m d => ∃ j, v (e j) ≠ 0).card

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

/-- Explicit mixed-radix indexing: the coordinate tuple is encoded in base
`m`, and the coefficient tuple in base three. No choice is used by the map. -/
def candidateEquivFin (m d : ℕ) : Candidate m d ≃ Fin ((3 * m) ^ d) :=
  (Equiv.prodCongr
    (finFunctionFinEquiv : IndexTuple m d ≃ Fin (m ^ d))
    ((Equiv.piCongrRight fun _ : Fin d => (ZMod.finEquiv 3).symm.toEquiv).trans
      (finFunctionFinEquiv : (Fin d → Fin 3) ≃ Fin (3 ^ d)))).trans
    (finProdFinEquiv.trans (finCongr (by simp [mul_pow, Nat.mul_comm])))

/-- The finite hash family, in a computable order suitable for `List.ofFn`. -/
def enumerate (m d : ℕ) : Fin ((3 * m) ^ d) → Candidate m d :=
  (candidateEquivFin m d).symm

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashFamilyDigits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashFamily

open scoped BigOperators
open Finset

/-- A combined alphabet digit is `coordinate + m * coefficient`. -/
def digitEquiv (m : ℕ) : (Fin m × ZMod 3) ≃ Fin (3 * m) :=
  (Equiv.prodCongr (Equiv.refl (Fin m)) (ZMod.finEquiv 3).symm.toEquiv).trans
    ((Equiv.prodComm (Fin m) (Fin 3)).trans finProdFinEquiv)

/-- Coordinate/coefficient tuples are equivalent to strings in the combined
alphabet, keeping every occurrence separately even when coordinates repeat. -/
def candidateDigitsEquiv (m d : ℕ) : Candidate m d ≃ (Fin d → Fin (3 * m)) :=
  (Equiv.arrowProdEquivProdArrow (Fin d) (fun _ => Fin m) (fun _ => ZMod 3)).symm.trans
    (Equiv.piCongrRight fun _ => digitEquiv m)

def decodeDigits {m d : ℕ} (a : Fin d → Fin (3 * m)) : Candidate m d :=
  (candidateDigitsEquiv m d).symm a

end SubexponentialSAT.SqrtLog.HashFamily

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInput
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

def boolValue (b : Bool) : R := if b then 1 else 0

end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramFrame
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid construction of the agreed inline record payload: a framed flat ring
coefficient followed by the ORIGINAL canonical literal-list payload. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Frame
def emitPorts : Fin 2 → Fin 3 := ![2,1]

end SubexponentialSAT.SqrtLog.HashInputProgram.Frame

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramSource
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

def skipCost (xs : List (List Bool)) : ℕ :=
  (xs.map (fun bits => 5*bits.length+10)).sum

end SubexponentialSAT.SqrtLog.HashInputProgram.Source

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopDecode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed native decoding of one raw hash digit.  The width and modulus are
runtime data.  A digit is split into its coefficient quotient and original
clause-index remainder; the latter is emitted in the source list's canonical
natural-field syntax.  No expanded clause payload is an input. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

abbrev tapes (raw width modulus chunk remainder quotient index : List Bool) : Fin 14 → List Bool :=
  ![raw,width,[],[],chunk,remainder,quotient,modulus,[],[],[],[],index,[]]

def divisionPorts : Fin 8 ↪ Fin 14 := ⟨![5,8,9,10,11,7,4,6],by decide⟩

def conversionRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def conversionStacks : Fin 3 → Fin 14 := ![5,12,8]

def budget (width modulusLength modulusValue : ℕ) : ℕ :=
  14*width+11 + 100*(modulusLength+width+1)^2 +
    32*(modulusValue+1)*(modulusLength+width+1)

end SubexponentialSAT.SqrtLog.HashInputProgram.LoopDecode

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoopTerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Assembly of one raw tuple term. All source lookup, coefficient lifting,
and record framing are executed by fixed native programs. The only persistent
data are the unexpanded original source, word width, modulus, ring shape,
unread raw bytes, and the already emitted output. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop

def tapes (raw width modulus master shape acc quotient index payload shapeTmp : List Bool) :
    Fin 24 → List Bool :=
  ![raw,width,[],[],[],[],quotient,modulus,[],[],[],[],index,[],master,shape,
    acc,[],payload,shapeTmp,[],[],[],[]]

def decoderStacks : Fin 14 → Fin 24 := Fin.castAdd 10

def lowRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def lookupStacks : Fin 6 → Fin 24 := ![14,8,12,9,10,18]

def normalizationStacks : Fin 8 → Fin 24 := ![6,8,9,10,11,13,20,19]

def frameStacks : Fin 3 → Fin 24 := ![6,18,8]

def recordStacks : Fin 3 → Fin 24 := ![18,16,8]

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashInputProgramLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed raw-tuple assembler. The machine traverses raw digit bytes, not a
pre-expanded clause table. Each step looks up one ORIGINAL source clause and
emits its lifted coefficient plus unchanged canonical literal bytes. -/
namespace SubexponentialSAT.SqrtLog.HashInputProgram.Loop

def termBudget (b ml m sourceLength weightLength clauseLength : ℕ) : ℕ :=
  LoopDecode.budget b ml m + 9*b+8 +
  (23*sourceLength+19) + (7*weightLength+5) +
  (7*weightLength+2*b+9) + (7*weightLength+10) +
  (7*(2*weightLength+1+clauseLength)+10) + 2

end SubexponentialSAT.SqrtLog.HashInputProgram.Loop

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashParametersProgramFinal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Production hash-parameter program. The arithmetic, ABI, and cost proofs
are checked together; the former split module paths remain compatibility
imports of this file. -/

/-! Fixed native arithmetic for alphabet size, sparse-code distance parameter,
and selector round cap. Every operation is a proved finite Boolean program. -/

namespace SubexponentialSAT.SqrtLog.HashParametersProgram

def width (n m B : List Bool) : ℕ := n.length + m.length + B.length + 1

end SubexponentialSAT.SqrtLog.HashParametersProgram


/-! Exact metadata loading and selector-port installation. Metadata is outside
all fourteen selector ports. The fixed scratch bank is physically cleared. -/


/-! Polynomial step budget for the complete physical parameter setup. -/


/-! Exported fixed program and the selector's actual fourteen-port interface. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLiteralChunkProgram
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

def decodeRegisters : Fin 4 → Fin 8 := Fin.castAdd 4
def decodeStacks : Fin 10 → Fin 19 := Fin.castAdd 9

def lengthRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def lengthStacks : Fin 3 → Fin 19 := ![2, 4, 5]

def divisionPorts : Fin 8 ↪ Fin 19 := ⟨![0, 1, 2, 3, 5, 18, 4, 7], by decide⟩

def conversionRegisters : Fin 3 → Fin 8 := Fin.castAdd 5
def conversionStacks : Fin 3 → Fin 19 := ![7, 10, 8]

end SubexponentialSAT.SubexpLiteralChunkProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpChunkRecordMap
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

def convertRegisters : Fin 8 → Fin 11 := Fin.castAdd 3
def convertStacks : Fin 19 → Fin 22 := Fin.castAdd 3

def emitRegisters : Fin 3 → Fin 11 := ![8, 9, 10]
def emitStacks : Fin 4 → Fin 22 := ![19, 21, 20, 9]

end SubexponentialSAT.SubexpChunkRecordMap

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeProducer
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

open SubexpChunkRecordMap

def reverseStacks : Fin 4 → Fin 22 := ![20, 21, 19, 9]

def dedupRegisters : Fin 10 → Fin 11 := Fin.castAdd 1
def dedupStacks : Fin 8 → Fin 22 := ![19, 9, 20, 0, 1, 2, 3, 21]

end SubexponentialSAT.SubexpScopeProducer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Raw hash scopes include every referenced literal, irrespective of its
coefficient. The physical materializer preserves these exact original codes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram

abbrev Word := List Bool
abbrev Term := Word × List ℕ

end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact scopes of the physically stored sparse raw rows and optional original
marked clause. These definitions are shared by the machine and resource proofs. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram
namespace RawTable
abbrev Rows (m : ℕ) := List (List (Fin m × ZMod 3))

end RawTable
end SubexponentialSAT.SqrtLog.HashScopeProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramSingle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed program turns a physically materialized weighted raw row into
its deduplicated original-variable scope. All constant initialization is paid. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Single

def registers : Fin 3 → Fin 11 := ![8,9,10]
def stackPorts : Fin 6 → Fin 22 := ![19,9,0,1,20,21]

end SubexponentialSAT.SqrtLog.HashScopeProgram.Single

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramFromTuple
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct original-source-to-scope composition. The finite program first reads
raw tuple references and looks up original clauses, then extracts their scope.
No table of precomputed scopes is supplied to this machine. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple

def assemblyRegisters : Fin 8 → Fin 11 := Fin.castAdd 3
def assemblyStacks : Fin 24 → Fin 46 := Fin.castAdd 22

def scopeStacks (i : Fin 22) : Fin 46 :=
  if i=19 then 16 else ⟨i.val+24,by omega⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.FromTuple

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedSource
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native lookup of the optional original marked clause. Local ports49/50
stage original masters705/706; source14 stages original formula700. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

def sourceRegisters : Fin 3 → Fin 11 := ![8,9,10]
def sourceStacks : Fin 6 → Fin 80 := ![14,51,49,52,53,73]

def scopeStacks (i : Fin 22) : Fin 80 := ⟨54+i.val,by omega⟩

end SubexponentialSAT.SqrtLog.HashScopeProgram.Marked

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawCall
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One callback for the actual raw-row table. The original clause master,
word width, modulus and ring shape are persistent; all workspace is cleaned. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable


def callStacks : Fin 46 → Fin 49 := Fin.castAdd 3

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramRawTable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Direct table adapter: raw clause-reference rows to deduplicated scope rows.
The original source table and all decoding parameters remain on their tapes. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

def reverseRegisters : Fin 3 → Fin 11 := ![8,9,10]
def reverseStacks : Fin 4 → Fin 49 := ![48,45,46,47]

end SubexponentialSAT.SqrtLog.HashScopeProgram.RawTable

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramMarkedTableCalls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

def lowStacks : Fin 49 → Fin 80 := Fin.castAdd 31

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLayoutFactorBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Numerical bounds for the actual clause-factor calls.  All envelopes are
polynomials in a common bound on the represented sizes and word lengths. -/

namespace SubexponentialSAT.SubexpLayoutConstructionBounds

def mappedScopeBytesBound (S : ℕ) := 1 + (2 * (S + 1) + 2) * S

end SubexponentialSAT.SubexpLayoutConstructionBounds

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashScopeProgramNativeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed polynomial envelope for raw references plus the optional original
marked clause. The size parameter bounds stored byte lengths and row/slot counts. -/
namespace SubexponentialSAT.SqrtLog.HashScopeProgram.Complete
open SubexponentialSAT.SubexpLayoutConstructionBounds

def weightedBytesBound (S : ℕ) : ℕ := 1+(6*S+4)*S

def assemblyBound (S : ℕ) : ℕ :=
  3+S*(HashInputProgram.Loop.termBudget S S S S S S+4)

end SubexponentialSAT.SqrtLog.HashScopeProgram.Complete

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashSelectProgramGenerate
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

open SubexponentialSAT.Subexp

abbrev Records := List (List Bool)

end SubexponentialSAT.SqrtLog.HashSelectProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafParametersProgramNative
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

def allChecks : List (Fin 10) := List.finRange 10

end SubexponentialSAT.SqrtLog.LeafParametersProgram.BitGuard


/- Component: SubexponentialSAT.SqrtLog.LeafParametersProgramCircuit -/


end OAI.Algorithms
end


