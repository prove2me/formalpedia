-- Prove2me | Definitions.Def_OAIQ081S027
-- name    : OAIQ081S027
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-29T21:27:46.754551+00:00
-- url     : https://prove2.me/theorems/b08c5771-7162-4ec6-a7f0-f44f76e5a57a
-- title:
--   Definitions bundle OAIQ081S027 of the split of OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math) at commit 7ef5c0c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 76 declarations of OpenAI's Lean: 50 definitions, 1 inductive type or structure and 25 theorems. The definitions and types are `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.canonical`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.choiceAdd`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.choiceAddProgram`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.choicePorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixScanCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.preMatrixStepCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowKey`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.rowValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftAddPorts`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.shiftedWord`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureStepCost`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signatureValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.signedWords`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete.freeAssignmentEquiv`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete.freeOrder`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.candidateEntry`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.mulX`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.powerVector`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.structureTable`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.residuePolynomial`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.addRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.coordinateMulRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.denote`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.entryCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.mulRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.mulXRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.negRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.oneVectorRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.powerVectorRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.program`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.represented`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.structureTableRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.sumRun`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.tripleRun`, `OAI.Algorithms.SubexponentialSAT.Subexp.MatrixProgramSupport.copy` and 11 more.
--
--   **Sources.** They come from these modules of lean/OAI/Algorithms, in whole or in part: `SubexponentialSAT_SqrtLog_BucketProgramArithmetic`, `SubexponentialSAT_SqrtLog_BucketProgramNormalize`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix`, `SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep`, `SubexponentialSAT_SqrtLog_BucketProgramRow`, `SubexponentialSAT_SqrtLog_BucketProgramShift`, `SubexponentialSAT_SqrtLog_BucketProgramSignature`, `SubexponentialSAT_SqrtLog_BucketTupleProgramHeadOrder`, `SubexponentialSAT_SqrtLog_IrreducibleSearchBasic`, `SubexponentialSAT_SqrtLog_IrreducibleSearchCompanion`, `SubexponentialSAT_SqrtLog_RingModel`, `SubexponentialSAT_SqrtLog_RingProgramAlgebra`, `SubexponentialSAT_SqrtLog_RingProgramBasic`, `SubexponentialSAT_SqrtLog_RingProgramCompanion`, `SubexponentialSAT_SqrtLog_RingProgramModel`, `SubexponentialSAT_SubexpConvolutionControl`, `SubexponentialSAT_SubexpConvolutionPair`, `SubexponentialSAT_SubexpDensePolynomial`, `SubexponentialSAT_SubexpJetInitProgram`, `SubexponentialSAT_SubexpLinearFactorProgram`, `SubexponentialSAT_SubexpLocalCRTSetup`, `SubexponentialSAT_SubexpPolynomialAddService`, `SubexponentialSAT_SubexpSymbolicCost`, `SubexponentialSAT_Subexp_MatrixProgramSupport`, `SubexponentialSAT_Subexp_TupleProgram`.
--
--   **Imports.** It imports the published bundle `Def_SubexponentialSAT`; the bundles `OAIQ081S000`, `OAIQ081S001`, `OAIQ081S002`, `OAIQ081S003` and `OAIQ081S004` of this split.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ081S047`, `OAIQ081S048`, `OAIQ081S049`, `OAIQ081S050`, `OAIQ081S052`, `OAIQ081S053`, `OAIQ081S054`, `OAIQ081S055`, `OAIQ081S056`, `OAIQ081S057`, `OAIQ081S058`, `OAIQ081S059`, `OAIQ081S060` and `OAIQ081S063`.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Algorithms at commit 7ef5c0c

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S000
import Definitions.Def_OAIQ081S001
import Definitions.Def_OAIQ081S002
import Definitions.Def_OAIQ081S003
import Definitions.Def_OAIQ081S004

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed binary conditional-add kernel for exact offset signatures. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls
open scoped BigOperators

def choicePorts (bit : Bool) : Ports 9 where
  left := 2
  right := if bit then 1 else 0
  out := 3
  work := addWork
  out_ne_left := by decide
  out_ne_right := by cases bit <;> decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; cases bit <;> fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

abbrev choiceAdd : Cmd 8 9 := .ite 0 (addAt (choicePorts true)) (addAt (choicePorts false))

def choiceAddProgram := compiled choiceAdd 0 3

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
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

/-- Consume a reversed payload and prepend its escaped forward payload.
The caller supplies frame/list delimiters. -/
abbrev escapeProgram : Program 2 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 5, .push 1 0 3,
    .set 0 true 4, .push 1 0 0, .halt]

/-! The fixed ABI uses ten Boolean registers and nine Boolean stacks:
0 prior tuples, 1 saved alphabet, 2 current reversed tuple, 3 alphabet cursor,
4 reversed word, 5 output, 6 copied tuple, 7 copy scratch, 8 unary depth.
Registers 0--2 and 3--5 belong to the two framed iterators, 6--7 are scratch,
and 8--9 belong to the eventual depth loop. -/

end SubexponentialSAT.Subexp.TupleProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_MatrixProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed stack and frame-reading routines used by the encoded matrix checker. -/

namespace SubexponentialSAT.Subexp.MatrixProgramSupport

open BitProgram StructuredCalls

variable {s : ℕ}

abbrev transfer (src dst : Fin s) : Cmd 8 s :=
  .call (StackRoutines.transferProgram src dst 0 1)

abbrev move (src dst tmp : Fin s) : Cmd 8 s :=
  .seq (transfer src tmp) (transfer tmp dst)

abbrev copy (src dst tmp : Fin s) : Cmd 8 s :=
  .call (StackRoutines.copyProgram src dst tmp 0 1)

def words : List (List Bool) → List Bool
  | [] => []
  | x :: xs => Encoding.frame x ++ words xs

end SubexponentialSAT.Subexp.MatrixProgramSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete measured coefficient scan for one integer signature row.
Runtime EOF controls the loop; no instruction count depends on row length. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

def rowValue (W : List Bool) (coeffs : List (List Bool)) (bits : List Bool) : ℕ :=
  (List.zipWith (fun c b => if b then SubexponentialSAT.BinaryArithmetic.toNat c
    else SubexponentialSAT.BinaryArithmetic.toNat W) coeffs bits).sum

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Canonical, positive encodings for exact integer row signatures.  The
added one is common to all assignments and makes the normalizer total on
all legitimate row results, including the empty head. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def canonical (n : ℕ) : List Bool :=
  SubexponentialSAT.SubexpLiftRing.fixedBits (Nat.log2 n+1) n

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramShift
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Primitive preparation of a nonnegative shifted integer coefficient.
The input signed integer is a pair P-N; W dominates N. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

def shiftAddPorts : Ports 10 where
  left := 2
  right := 8
  out := 9
  work := shiftWork
  out_ne_left := by decide
  out_ne_right := by decide
  work_ne_left := by intro i; fin_cases i <;> decide
  work_ne_right := by intro i; fin_cases i <;> decide
  work_ne_out := by intro i; fin_cases i <;> decide

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete decoding and shifting of one signed coefficient pair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def signedWords : List SignedWord → List Bool
  | [] => []
  | (P,N)::xs => Encoding.frame P ++ Encoding.frame N ++ signedWords xs

def shiftedWord (W : List Bool) (a : SignedWord) (out : List Bool) : Prop :=
  SubexponentialSAT.BinaryArithmetic.toNat out = SubexponentialSAT.BinaryArithmetic.toNat W -
    SubexponentialSAT.BinaryArithmetic.toNat a.2 + SubexponentialSAT.BinaryArithmetic.toNat a.1 ∧
  out.length ≤ W.length+a.2.length+a.1.length+1

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessMatrix
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A concrete row-major signed matrix preprocessor. All input and output
frames are scanned by fixed instructions; the original bound word is retained. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def preMatrixStepCost (W : List Bool) (row : List SignedWord) : ℕ :=
  9*(signedWords row).length+preRowCost W row+
    16*preOutputLength W row+8*row.length+16

def preMatrixScanCost (W : List Bool) (rows : List (List SignedWord)) : ℕ :=
  (rows.map (fun row => preMatrixStepCost W row+2)).sum+1

def preMatrixCost (W : List Bool) (rows : List (List SignedWord)) : ℕ :=
  preMatrixScanCost W rows+29*preMatrixPayload W rows+23*rows.length+20

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramSignature
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed nested row scanner.  The input matrix is a raw list of framed
rows, and each row is itself a raw list of framed coefficient words. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

def rowKey (W bits : List Bool) (row : List (List Bool)) : List Bool :=
  canonical (1+rowValue W row bits)

def signatureStepCost (W bits : List Bool) (row : List (List Bool)) : ℕ :=
  9*(words row).length+7 + (7*bits.length+5) + 2 +
    (canonicalRowBudget W row+1) + (8*(rowKey W bits row).length+8)

def signatureValue (W bits : List Bool) (rows : List (List (List Bool))) : List Bool :=
  words ((rows.map (rowKey W bits)).reverse)

def signatureCost (W bits : List Bool) (rows : List (List (List Bool))) : ℕ :=
  ((rows.map (fun row => signatureStepCost W bits row+2)).sum)+1

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketTupleProgramHeadOrder
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The selected variable IDs give a canonical order on a typed free head. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete

noncomputable section

variable {n r : ℕ} (H : Finset (Fin n))
  (head : {v : Fin n // v ∉ H} → Fin r) (g : Fin r)
  (js : List ℕ) (hb : ∀ v ∈ js, v < n) (hn : js.Nodup)
  (hs : ∀ v : Fin n, v.val ∈ js ↔ ∃ hv : v ∉ H, head ⟨v, hv⟩ = g)

def freeOrder : Fin js.length ≃ Moments.Head head g :=
  Equiv.ofBijective (freeOrderFun H head g js hb hs) (by
    constructor
    · intro i j he
      apply idOrder_injective js hb hn
      simpa only [freeOrderFun_val] using
        congrArg (fun x : Moments.Head head g => x.val.val) he
    · intro v
      have hv : v.val.val.val ∈ js :=
        (hs v.val.val).mpr ⟨v.val.property, v.property⟩
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hv
      refine ⟨i, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply Fin.ext
      simpa only [freeOrderFun_val, idOrder] using hi)

def freeAssignmentEquiv : (Moments.Head head g → Bool) ≃ (Fin js.length → Bool) where
  toFun a i := a (freeOrder H head g js hb hn hs i)
  invFun x v := x ((freeOrder H head g js hb hn hs).symm v)
  left_inv a := by funext v; simp
  right_inv x := by funext i; simp

end

end OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketTupleProgram.Concrete
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Finite coefficient tests for arbitrary-degree irreducible search

Only vectors, finite lists, and scalar arithmetic are executed. `ofFn` and
the polynomial interpretation occur solely in the correctness proofs.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial
open scoped BigOperators

/-- A monic candidate consists of its `d` lower coefficients. -/
def candidateEntry {R : Type*} [Semiring R] {d : ℕ}
    (c : Fin d → R) (j : ℕ) : R :=
  (if j = d then 1 else 0) + entry c j

theorem ofFn_coeff_entry {R : Type*} [Semiring R] [DecidableEq R] {n : ℕ}
    (a : Fin n → R) (j : ℕ) : (Polynomial.ofFn n a).coeff j = entry a j := by
  by_cases h : j < n
  · simp [entry, h]
  · simp [entry, h, ofFn_coeff_eq_zero_of_ge a (Nat.le_of_not_gt h)]

theorem poly_eq_X_pow_add_ofFn {R : Type*} [Semiring R] [DecidableEq R] {d : ℕ}
    (c : Fin d → R) :
    QuarticSearch.poly c = X ^ d + Polynomial.ofFn d c := by
  simp only [QuarticSearch.poly, ofFn_eq_sum_monomial, C_mul_X_pow_eq_monomial]

theorem candidateEntry_eq_coeff {R : Type*} [Semiring R] [DecidableEq R] {d : ℕ}
    (c : Fin d → R) (j : ℕ) : candidateEntry c j = (QuarticSearch.poly c).coeff j := by
  rw [poly_eq_X_pow_add_ofFn, coeff_add, coeff_X_pow, ofFn_coeff_entry]
  simp only [candidateEntry, eq_comm]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_IrreducibleSearchCompanion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Explicit companion recurrence for the supplied monic polynomial

This module supplies the structure constants needed by the dynamic ring
program. It executes only coefficient-vector operations; polynomial
remainder is used solely to state and prove its meaning.
-/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

open Polynomial

def mulX {R : Type*} [Ring R] {d : ℕ} (c a : Fin d → R) : Fin d → R :=
  fun i => (if i.val = 0 then 0 else entry a (i.val - 1)) - entry a (d - 1) * c i

def powerVector {R : Type*} [Ring R] {d : ℕ} (c : Fin d → R) : ℕ → (Fin d → R)
  | 0 => cacheVector (oneVector d)
  | n + 1 => cacheVector (mulX c (powerVector c n))

def structureTable {R : Type*} [Ring R] {d : ℕ} (c : Fin d → R)
    (i j k : Fin d) : R := powerVector c (i.val + j.val) k

section Correctness

variable {R : Type*} [CommRing R] [Nontrivial R] [DecidableEq R]
variable {d : ℕ} (hd : 0 < d) (c a : Fin d → R)
include hd

omit [Nontrivial R] in
theorem ofFn_oneVector : Polynomial.ofFn d (oneVector (R := R) d) = 1 := by
  apply Polynomial.ext
  intro j
  by_cases hj : j = 0
  · subst j
    simp [ oneVector, hd]
  · by_cases hlt : j < d
    · simp [ oneVector, hlt, hj, coeff_one]
    · simp [ofFn_coeff_entry, entry, hlt, hj, coeff_one]

end Correctness

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingModel
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Unramified ring attached to a supplied irreducible ternary polynomial

`Data.coefficients` is execution data. An irreducible-search correctness proof
can supply `Data.irreducible`; no separate choice of a minimum polynomial is
made in this model. All polynomial lifts use coefficient representatives.
-/

noncomputable section
namespace SubexponentialSAT.SqrtLog.RingModel

open Polynomial

structure Data (d : ℕ) where
  coefficients : Fin d → ZMod 3
  irreducible : Irreducible (QuarticSearch.poly coefficients)

namespace Data

variable {d : ℕ} (a : Data d) (t : ℕ)

abbrev Base (t : ℕ) := LiftRing.Base 3 t

def residuePolynomial : (ZMod 3)[X] := QuarticSearch.poly a.coefficients

def F : (Base t)[X] :=
  QuarticSearch.poly (fun i => ((a.coefficients i).val : Base t))

theorem residuePolynomial_monic : a.residuePolynomial.Monic := QuarticSearch.poly_monic _
@[simp] theorem residuePolynomial_degree : a.residuePolynomial.natDegree = d :=
  QuarticSearch.poly_natDegree _

theorem F_monic (_ht : 0 < t) : (a.F t).Monic := by
  let _ : Fact (1 < 3 ^ t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt _ht) (by decide)⟩
  exact QuarticSearch.poly_monic _

@[simp] theorem F_degree (ht : 0 < t) : (a.F t).natDegree = d := by
  let _ : Fact (1 < 3 ^ t) := ⟨Nat.one_lt_pow (Nat.ne_of_gt ht) (by decide)⟩
  exact QuarticSearch.poly_natDegree _

theorem F_map (ht : 0 < t) :
    (a.F t).map (LiftRing.baseReduction 3 t ht) = a.residuePolynomial := by
  rw [F, QuarticSearch.map_poly]
  apply congrArg QuarticSearch.poly
  funext i
  simp only [map_natCast, ZMod.natCast_zmod_val]

end Data

end SubexponentialSAT.SqrtLog.RingModel

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSymbolicCost
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Uniform symbolic list costs for growing parameters

The old canonical-list algorithm has an explicit fixed-degree event bound. This
module retains its interfaces and makes all parameter dependence visible. It also
refines exponent addition to an actual unary bit-string algorithm. Unary is used
only for exponent indices, whose values are O(D), never for ring coefficients.

Counters below are charged operations/bit inspections. A primitive tape-machine
execution certificate is a separate requirement.
-/

namespace SubexponentialSAT.SubexpSymbolicCost

abbrev RepresentedRing.program {C R : Type*} [CommRing R] (ops : RepresentedRing C R) :
    RingProgram C :=
  ⟨ops.zeroRun, ops.oneRun, ops.addRun, ops.mulRun, ops.negRun⟩

end SubexponentialSAT.SubexpSymbolicCost

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dynamic-degree coefficient arithmetic

These executable callbacks operate on a runtime-sized coefficient vector.
Their counters include all scalar callbacks and one event per vector/list
entry. A separate flat-stack refinement must account for scanning serialized
vectors; callback event counts alone are not claimed to be primitive time.
-/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

/-- Evaluate and sum a list of measured scalar computations. -/
def sumRun (ops : RingProgram C) : List (C × ℕ) → C × ℕ
  | [] => ops.zeroRun
  | x :: xs =>
    let s := sumRun ops xs
    let out := ops.addRun x.1 s.1
    (out.1, x.2 + s.2 + out.2 + 1)

theorem sumRun_correct (ops : RepresentedRing C A) (xs : List (C × ℕ)) :
    ops.decode (sumRun ops.program xs).1 = (xs.map fun x => ops.decode x.1).sum := by
  induction xs with
  | nil => exact ops.zero_correct
  | cons x xs ih =>
    change ops.decode (ops.addRun x.1 (sumRun ops.program xs).1).1 = _
    rw [ops.add_correct, ih]
    rfl

def addRun (ops : RingProgram C) {d : ℕ} (x y : Code C d) : Code C d × ℕ :=
  tabulateRun fun i => ops.addRun (x i) (y i)

def negRun (ops : RingProgram C) {d : ℕ} (x : Code C d) : Code C d × ℕ :=
  tabulateRun fun i => ops.negRun (x i)

/-- Two scalar multiplications, with both measured costs retained. -/
def tripleRun (ops : RingProgram C) (a b c : C) : C × ℕ :=
  let ab := ops.mulRun a b
  let abc := ops.mulRun ab.1 c
  (abc.1, ab.2 + abc.2)

def coordinateMulRun (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) : C × ℕ :=
  sumRun ops ((List.ofFn fun i : Fin d =>
    List.ofFn fun j : Fin d => tripleRun ops (x i) (y j) (table i j k)).flatten)

def mulRun (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) : Code C d × ℕ :=
  tabulateRun fun k => coordinateMulRun ops table x y k

@[simp] theorem tripleRun_correct (ops : RepresentedRing C A) (a b c : C) :
    ops.decode (tripleRun ops.program a b c).1 =
      ops.decode a * ops.decode b * ops.decode c := by
  simp only [tripleRun, ops.mul_correct]

theorem coordinateMulRun_correct (ops : RepresentedRing C A) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (x y : Code C d) (k : Fin d) :
    ops.decode (coordinateMulRun ops.program table x y k).1 =
      ∑ i, ∑ j, ops.decode (x i) * ops.decode (y j) * ops.decode (table i j k) := by
  rw [coordinateMulRun, sumRun_correct]
  simp [List.map_flatten, List.sum_flatten, List.map_ofFn, List.sum_ofFn]

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramAlgebra
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A R : Type*} [CommRing A] [CommRing R]

/-- A coefficient vector interpreted in a supplied finite basis. -/
def denote (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (x : Code C d) : R :=
  ∑ i, scalar (ops.decode (x i)) * basis i

theorem denote_add (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (x y : Code C d) :
    denote ops scalar basis (addRun ops.program x y).1 =
      denote ops scalar basis x + denote ops scalar basis y := by
  simp only [denote, addRun, tabulateRun, List.Vector.get_ofFn, ops.add_correct,
    map_add, add_mul, Finset.sum_add_distrib]

theorem denote_neg (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (x : Code C d) :
    denote ops scalar basis (negRun ops.program x).1 = -denote ops scalar basis x := by
  simp only [denote, negRun, tabulateRun, List.Vector.get_ofFn, ops.neg_correct,
    map_neg, neg_mul, Finset.sum_neg_distrib]

theorem denote_mul (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (table : Fin d → Fin d → Fin d → C)
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (ops.decode (table i j k)) * basis k) (x y : Code C d) :
    denote ops scalar basis (mulRun ops.program table x y).1 =
      denote ops scalar basis x * denote ops scalar basis y := by
  conv_lhs => simp only [denote, mulRun, tabulateRun_eq]
  simp_rw [coordinateMulRun_correct, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))
    (t := (Finset.univ : Finset (Fin d))) (f := fun k j =>
      scalar (ops.decode (x _)) * scalar (ops.decode (y j)) *
        scalar (ops.decode (table _ j k)) * basis k)]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← htable]
  simp only [denote, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Constants are supplied cached coefficient vectors, not semantic encodings
computed by this callback. Copying a constant charges its coefficient count. -/
def program (ops : RingProgram C) {d : ℕ}
    (table : Fin d → Fin d → Fin d → C) (zero one : Code C d) :
    RingProgram (Code C d) where
  zeroRun := (zero, d)
  oneRun := (one, d)
  addRun := addRun ops
  mulRun := mulRun ops table
  negRun := negRun ops

def represented (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (table : Fin d → Fin d → Fin d → C)
    (zero one : Code C d)
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (ops.decode (table i j k)) * basis k)
    (hzero : denote ops scalar basis zero = 0)
    (hone : denote ops scalar basis one = 1) : RepresentedRing (Code C d) R where
  decode := denote ops scalar basis
  zeroRun := (zero, d)
  oneRun := (one, d)
  addRun := addRun ops.program
  mulRun := mulRun ops.program table
  negRun := negRun ops.program
  zero_correct := hzero
  one_correct := hone
  add_correct := denote_add ops scalar basis
  mul_correct := denote_mul ops scalar basis table htable
  neg_correct := denote_neg ops scalar basis

@[simp] theorem represented_program (ops : RepresentedRing C A) (scalar : A →+* R)
    {d : ℕ} (basis : Fin d → R) (table : Fin d → Fin d → Fin d → C)
    (zero one : Code C d) (htable hzero hone) :
    (represented ops scalar basis table zero one htable hzero hone).program =
      program ops.program table zero one := rfl

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramCompanion
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Executable measured generation of dynamic monic-quotient multiplication
constants. Polynomial remainder occurs only in the correctness theorem. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost

variable {C A : Type*} [CommRing A]

def entryCode (ops : RingProgram C) {d : ℕ} (a : Code C d) (n : ℕ) : C :=
  if h : n < d then a ⟨n, h⟩ else ops.zeroRun.1

@[simp] theorem entryCode_correct (ops : RepresentedRing C A) {d : ℕ}
    (a : Code C d) (n : ℕ) :
    ops.decode (entryCode ops.program a n) =
      IrreducibleSearch.entry (fun i => ops.decode (a i)) n := by
  unfold entryCode IrreducibleSearch.entry
  split <;> simp_all only [ ops.zero_correct]

def oneVectorRun (ops : RingProgram C) (d : ℕ) : Code C d × ℕ :=
  tabulateRun fun i => if i.val = 0 then ops.oneRun else ops.zeroRun

theorem oneVectorRun_correct (ops : RepresentedRing C A) (d : ℕ) :
    (fun i => ops.decode ((oneVectorRun ops.program d).1 i)) =
      IrreducibleSearch.oneVector d := by
  funext i
  simp only [oneVectorRun, tabulateRun, List.Vector.get_ofFn, IrreducibleSearch.oneVector]
  split <;> simp_all only [ ops.one_correct, ops.zero_correct]

def mulXRun (ops : RingProgram C) {d : ℕ} (c a : Code C d) : Code C d × ℕ :=
  tabulateRun fun i =>
    let m := ops.mulRun (entryCode ops a (d - 1)) (c i)
    let n := ops.negRun m.1
    let v := ops.addRun
      (if i.val = 0 then ops.zeroRun.1 else entryCode ops a (i.val - 1)) n.1
    (v.1, m.2 + n.2 + v.2 + 2 * ops.zeroRun.2 + 2)

theorem mulXRun_correct (ops : RepresentedRing C A) {d : ℕ}
    (c a : Code C d) :
    (fun i => ops.decode ((mulXRun ops.program c a).1 i)) =
      IrreducibleSearch.mulX (fun i => ops.decode (c i)) (fun i => ops.decode (a i)) := by
  funext i
  simp only [mulXRun, tabulateRun, List.Vector.get_ofFn, RepresentedRing.program, ops.add_correct,
    ops.neg_correct, ops.mul_correct, IrreducibleSearch.mulX, sub_eq_add_neg]
  change ops.decode (if i.val = 0 then ops.zeroRun.1 else entryCode ops.program a (i.val - 1)) +
    -(ops.decode (entryCode ops.program a (d - 1)) * ops.decode (c i)) = _
  rw [entryCode_correct]
  split <;> simp_all only [ops.zero_correct, entryCode_correct]

def powerVectorRun (ops : RingProgram C) {d : ℕ} (c : Code C d) : ℕ → Code C d × ℕ
  | 0 => oneVectorRun ops d
  | n + 1 =>
    let a := powerVectorRun ops c n
    let b := mulXRun ops c a.1
    (b.1, a.2 + b.2 + 1)

theorem powerVectorRun_correct (ops : RepresentedRing C A) {d : ℕ}
    (c : Code C d) (n : ℕ) :
    (fun i => ops.decode ((powerVectorRun ops.program c n).1 i)) =
      IrreducibleSearch.powerVector (fun i => ops.decode (c i)) n := by
  induction n with
  | zero => simpa only [powerVectorRun, IrreducibleSearch.powerVector,
      IrreducibleSearch.cacheVector_eq] using oneVectorRun_correct ops d
  | succ n ih =>
    simp only [powerVectorRun, mulXRun_correct, IrreducibleSearch.powerVector,
      IrreducibleSearch.cacheVector_eq, ih]

/-- All powers are generated by the companion recurrence, not by calling a
semantic polynomial-remainder operation. -/
def structureTableRun (ops : RingProgram C) {d : ℕ} (c : Code C d) :
    (Fin d → Fin d → Fin d → C) × ℕ :=
  let stored := List.Vector.ofFn fun i : Fin d =>
    List.Vector.ofFn fun j : Fin d => powerVectorRun ops c (i.val + j.val)
  (fun i j k => ((stored.get i).get j).1 k,
    (∑ i : Fin d, (∑ j : Fin d, (((stored.get i).get j).2 + d))) + d * d)

@[simp] theorem structureTableRun_correct (ops : RepresentedRing C A) {d : ℕ}
    (c : Code C d) (i j k : Fin d) :
    ops.decode ((structureTableRun ops.program c).1 i j k) =
      IrreducibleSearch.structureTable (fun i => ops.decode (c i)) i j k := by
  simpa only [structureTableRun, List.Vector.get_ofFn, IrreducibleSearch.structureTable] using
    congrFun (powerVectorRun_correct ops c (i.val + j.val)) k

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RingProgramModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete ternary coefficient input and the executable represented arithmetic
for the supplied-polynomial unramified ring model. -/
namespace SubexponentialSAT.SqrtLog.RingProgram

open scoped BigOperators
open SubexponentialSAT.SubexpSymbolicCost SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing SubexponentialSAT.BinaryArithmetic

@[simp] theorem ternaryLiteral_value (a : ZMod 3) : BinaryArithmetic.toNat (ternaryLiteral a) = a.val := by
  have ha := a.val_lt
  interval_cases h : a.val <;> simp [ternaryLiteral, h, BinaryArithmetic.toNat, bitVal]

@[simp] theorem ternaryLiteral_length (a : ZMod 3) : (ternaryLiteral a).length ≤ 2 := by
  unfold ternaryLiteral
  split <;> simp_all
  split <;> simp

end SubexponentialSAT.SqrtLog.RingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite control for triangular, truncated convolution

Polynomial coefficients occupy equal-width flat cells. Both input arrays have
D cells. The left array is consumed; the right array is retained. The output
array is preallocated with D zero cells. Unary loop counters and indices are
runtime stacks, so changing D does not change this control program.

The scalar product-and-accumulate command is inserted as a fixed command. Its
concrete implementation uses the quartic multiplier and the persistent cell
updater; it is never a semantic-function instruction.
-/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls

abbrev Code := Cmd 16 256

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpConvolutionPair
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# One actual product-and-accumulate step for packed jet convolution

The global state has sixteen Boolean registers and 256 Boolean-word stacks.
The multiplier occupies the fixed high bank beginning at 128. Its result is
moved, with order preserved, to the low-bank jet-cell accumulator service.
-/

namespace SubexponentialSAT.SubexpConvolutionPair

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing

attribute [local simp] Fin.coe_ofNat_eq_mod

abbrev Code := Cmd 16 256

end SubexponentialSAT.SubexpConvolutionPair

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpDensePolynomial
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Dense univariate arithmetic through represented coefficient callbacks

Code words need no ring structure. Every scalar operation is a call to the
supplied implementation, and the returned counters are added along the actual
execution. These are callback counters, not a primitive-machine runtime theorem.
-/

namespace SubexponentialSAT.SubexpDensePolynomial

section Programs

variable {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)

def addProgram : List C → List C → List C × ℕ
  | [], Q => (Q, 0)
  | P, [] => (P, 0)
  | a :: P, b :: Q =>
      let head := ops.addRun a b
      let rest := addProgram P Q
      (head.1 :: rest.1, head.2 + rest.2)

end Programs

section ProgramRefinement

variable {C R : Type*} [CommRing R] (ops : SubexpSymbolicCost.RepresentedRing C R)

@[simp] theorem addProgram_run (P Q : List C) :
    addProgram ops.program P Q = addRun ops P Q := by
  induction P generalizing Q with
  | nil => simp [addProgram, addRun]
  | cons a P ih =>
      cases Q with
      | nil => rfl
      | cons b Q => simp only [addProgram, addRun, ih]

end ProgramRefinement

end SubexponentialSAT.SubexpDensePolynomial

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpJetInitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Initializing the packed output jet

The input dimension is a unary word on stack 109 and the scalar word width is
the length of stack 10.  The fixed program constructs one four-word zero
coefficient on stack 104 and copies it D times to stack 102.  It preserves both
input words.  No zero array is supplied as an input certificate.
-/

namespace SubexponentialSAT.SubexpJetInitProgram

open BitProgram StructuredCalls

abbrev Code := Cmd 16 128

end SubexponentialSAT.SubexpJetInitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLinearFactorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime construction of a padded linear polynomial. The low and high
coefficient cells occupy stacks 100 and 101. The unary dimension is on 109,
the base-word width is on 10, and the output array is on 102. -/

namespace SubexponentialSAT.SubexpLinearFactorProgram

open BitProgram StructuredCalls

abbrev Code := Cmd 16 128

end SubexponentialSAT.SubexpLinearFactorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpLocalCRTSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual cache initialization for one local CRT correction. The zero and
one arrays are physically built from scalar cells and the runtime dimension;
the complete node stream and unary skip index are then copied into work.
-/

namespace SubexponentialSAT.SubexpLocalCRTSetup

open BitProgram StructuredCalls SubexpConvolutionControl

def seq (a b : Code) : Code := .seq a b

end SubexponentialSAT.SubexpLocalCRTSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpPolynomialAddService
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Cached dense addition for the local CRT controller. The fixed service
copies operands 240/241, invokes the actual dense-add instruction table, and
moves its output to 244. All native workspace is restored. -/

namespace SubexponentialSAT.SubexpPolynomialAddService

open BitProgram StructuredCalls SubexpConvolutionControl
open SubexpLiftRing SubexpQuarticRing

theorem addProgram_length {C : Type*} (ops : SubexpSymbolicCost.RingProgram C)
    (P Q : List C) :
    (SubexpDensePolynomial.addProgram ops P Q).1.length = max P.length Q.length := by
  induction P generalizing Q with
  | nil => simp [SubexpDensePolynomial.addProgram]
  | cons a P ih =>
      cases Q with
      | nil => simp [SubexpDensePolynomial.addProgram]
      | cons b Q =>
          have h := ih Q
          change (SubexpDensePolynomial.addProgram ops P Q).1.length + 1 =
            max (P.length + 1) (Q.length + 1)
          omega

end SubexponentialSAT.SubexpPolynomialAddService

end OAI.Algorithms
end


