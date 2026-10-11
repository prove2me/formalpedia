-- Prove2me | Definitions.Def_CLRS_Chapter4_Publication_MatrixContracts
-- name    : CLRS_Chapter4_Publication_MatrixContracts
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:04:00.293362+00:00
-- url     : https://prove2.me/theorems/6be1b90c-f5ee-45c9-9882-e1a6ded248af
-- title:
--   Common matrix product and runtime measures for Chapter 4 contracts
-- statement:
--   The common finite matrix product is the ordinary row-column dot product inside a natural n by n square, and zero outside it. Runtime measures select the multiply_add clock for ordinary multiplication; multiplications plus calls for eight-way recursion; and products, calls, linear_cells, and copied_cells for Strassen. These are source clock increments. The combined correctness and runtime theorems are published separately and quantify a uniform positive constant before all represented inputs.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Publication.MatrixContracts, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/proofs/chapter4/Publication/MatrixContracts.lean

import Definitions.Def_CLRS_Chapter4_Algo2Lean
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiply
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixMultiplyPoints
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursive
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursiveGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassen
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassenGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixStrassenPoints
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_CallCost
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_MatrixHeap
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

/-!
Publication-facing total-correctness contracts for the three CLRS Chapter 4
matrix programs. Every result uses the actual generated `Call` relation and the
same final heap for its mathematical answer, preservation, allocation, and cost.
The positive runtime constant is chosen before all dimensions and input heaps.

Inputs are genuine arrays of integer row arrays. `Stored` requires allocated
outer and row references at every integer index; the rows may share references.
The returned finite rows are fresh and pairwise distinct. Outside the finite
square the returned values are zero. Work counts the explicitly named source
ticks, excluding uncharged allocation/bookkeeping and integer bit complexity.
-/

open Algo2LeanCore Algo2LeanGenerated Algo2LeanCore.MatrixHeap

namespace Chapter4Publication

/-- The ordinary finite row-column dot product, with zero outside the square. -/
def product (n : Nat) (a b : Values) : Values := fun row column =>
  if 0 ≤ row ∧ row < n ∧ 0 ≤ column ∧ column < n then
    Chapter4Math.dot n (fun inner => a row inner) (fun inner => b inner column)
  else 0











namespace MatrixMultiply

/-- One unit per scalar multiplication with accumulation. -/
def runtime (charged : Clocks) : Nat := charged "multiply_add"

-- Main result: Correctness and running time


end MatrixMultiply

namespace MatrixRecursive

/-- Scalar products and every recursion node both contribute one unit. -/
def runtime (charged : Clocks) : Nat := charged "multiplications" + charged "calls"

-- Main result: Correctness and running time


end MatrixRecursive

namespace Strassen

/-- All four source clocks: products, recursive calls, combinations and copies. -/
def runtime (charged : Clocks) : Nat :=
  charged "products" + charged "calls" + charged "linear_cells" + charged "copied_cells"



-- Main result: Correctness and running time


end Strassen
end Chapter4Publication

end CLRS


