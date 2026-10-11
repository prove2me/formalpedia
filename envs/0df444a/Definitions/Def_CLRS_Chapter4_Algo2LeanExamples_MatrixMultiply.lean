-- Prove2me | Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiply
-- name    : CLRS_Chapter4_Algo2LeanExamples_MatrixMultiply
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:03:08.308776+00:00
-- url     : https://prove2.me/theorems/2d6a3e84-64a0-4c51-8ffc-396b92d9f12e
-- title:
--   Value and heap-effect specifications for ordinary matrix multiplication
-- statement:
--   This bundle supplies the mathematical value functions, allocation and heap-effect transformers, exact counter vectors, and local invariants used to analyze ordinary matrix multiplication. It retains the source-facing generated call relations. Substantial execution, matrix-correctness and runtime proofs are separate theorem nodes. Inputs contain arbitrary unbounded integers and may share row references; specific separation hypotheses are stated by the lemmas that need them. The measured cost is explicit source ticks, excluding uncharged allocation, bookkeeping and integer bit complexity.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Algo2LeanExamples.MatrixMultiply, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/matrix_multiply.algo; https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/analysis/matrix_multiply.lean

import Definitions.Def_CLRS_Chapter4_Algo2Lean
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyPoints
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_MatrixHeap
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

open MatrixMultiplyLibrary MatrixMultiplyLibrary.Algo2LeanGenerated

/-!
CLRS 4.1 on genuine arrays of row arrays. The inputs may share rows, including
with each other. A fresh row is allocated for every output row. The proof
constructs terminating executions and proves preservation of all pre-existing
objects, the mathematical matrix product, and exactly n³ scalar multiply-adds.
-/
open Algo2LeanCore Algo2LeanGenerated
open Algo2LeanCore.MatrixHeap

namespace MatrixMultiplyAnalysis

/-- The finite row-by-column sum, at arbitrary integer coordinates. -/
def dotFrom (a b : Values) (row column first : Int) : Nat → Int
  | 0 => 0
  | count + 1 => a row first * b first column + dotFrom a b row column (first + 1) count

def entry (a b : Values) (n : Nat) (row column : Int) : Int :=
  dotFrom a b row column 0 n

/-- Both coordinates outside the finite square have value zero. -/
def product (a b : Values) (n : Nat) : Values :=
  fun row column => if 0 ≤ row ∧ row < n ∧ 0 ≤ column ∧ column < n
    then entry a b n row column else 0

/-- Consecutive writes of a mathematical row to one fresh output object. -/
def fill (h : Heap) (r : SeqRef) (values : Seq) (first : Int) : Nat → Heap
  | 0 => h
  | count + 1 => fill (h.write r first (values first)) r values (first + 1) count



























/-- The completed fresh row and its exact cost. -/
def rowHeap (h : Heap) (av bv : Values) (n : Nat) (row : Int) : Heap :=
  (fill (h.allocate (fun _ => 0)) h.nextRef (entry av bv n row) 0 n).tick
    "multiply_add" (n * n)

def rowValues (av bv : Values) (n : Nat) (row : Int) : Seq :=
  fun column => if 0 ≤ column ∧ column < n then entry av bv n row column else 0















/-- The prefix of rows already completed by the outer loop. -/
def partialProduct (av bv : Values) (n : Nat) (limit : Int) : Values :=
  fun row column => if 0 ≤ row ∧ row < limit then rowValues av bv n row column else 0







/-- Each completed row has its own consecutive fresh identity. -/
def RowReferences (h : Heap) (result : CollectionRef) (base count : Nat) : Prop :=
  ∀ i : Nat, i < count → rows.get h result i = some (base + i)



def costs (n : Nat) : Clocks := Clocks.single "multiply_add" (n ^ 3)











-- Main result: Correctness






-- Main result: Running time




end MatrixMultiplyAnalysis

end CLRS


