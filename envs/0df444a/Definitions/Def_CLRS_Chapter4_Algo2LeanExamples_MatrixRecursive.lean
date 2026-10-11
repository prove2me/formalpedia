-- Prove2me | Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursive
-- name    : CLRS_Chapter4_Algo2LeanExamples_MatrixRecursive
-- status  : Definition
-- author  : @Chutong
-- created : 2026-10-11T05:02:47.113752+00:00
-- url     : https://prove2.me/theorems/d96b0df1-adbf-4cbd-bfc4-025d70d9c9d7
-- title:
--   Value and heap-effect specifications for eight-way recursive matrix multiplication
-- statement:
--   This bundle supplies the mathematical value functions, allocation and heap-effect transformers, exact counter vectors, and local invariants used to analyze eight-way recursive matrix multiplication. It retains the source-facing generated call relations. Substantial execution, matrix-correctness and runtime proofs are separate theorem nodes. Inputs contain arbitrary unbounded integers and may share row references; specific separation hypotheses are stated by the lemmas that need them. The measured cost is explicit source ticks, excluding uncharged allocation, bookkeeping and integer bit complexity.
--
--   **Formalization Note.** This content is transcribed from Algo2Lean development snapshot `fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41`, with explicit platform import and namespace adaptation. It is not attributed to public compiler v0.1.4. The submitted definition bundle must be checked without unfinished-proof assumptions.
-- source:
--   Algo2Lean Chapter 4 development, module Algo2LeanExamples.MatrixRecursive, immutable source fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41: https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/matrix_recursive.algo; https://github.com/chutongyang98/Lean_formalization/blob/fd33cf959b39f9e4a9fcfda4ef31d5a36b784d41/examples/analysis/matrix_recursive.lean

import Definitions.Def_CLRS_Chapter4_Algo2Lean
import Definitions.Def_CLRS_Chapter4_Algo2LeanExamples_MatrixRecursiveGenerated
import Definitions.Def_CLRS_Chapter4_Algo2LeanLib_MatrixHeap
import Std

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace CLRS

open MatrixRecursiveLibrary MatrixRecursiveLibrary.Algo2LeanGenerated

open Algo2LeanCore Algo2LeanGenerated
namespace MatrixRecursiveAnalysis

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- A matrix view records row identities and their validity; rows may alias. -/
def HasRows (heap : Heap) (matrix : CollectionRef) (rows : Int → SeqRef) : Prop :=
  seq_Seq_Int.valid heap matrix ∧ ∀ i,
    seq_Seq_Int.get heap matrix i = some (rows i) ∧ rows i < heap.nextRef







/-- A complete eight-way block multiplication, modeled by its heap effect. -/
def blockEffect (a b c : Int → SeqRef) (stride : Int) : Nat → Heap → Int → Int → Int → Heap
  | 0, heap, row, col, inner =>
    ((heap.tick "calls").tick "multiplications").write (c row) col
      (heap.read (c row) col + heap.read (a row) inner *
        heap.read (b inner) col)
  | depth + 1, heap, row, col, inner =>
    let heap := heap.tick "calls"
    let half : Int := (2 ^ depth : Nat)
    let h1 := blockEffect a b c stride depth heap (row) (col) (inner)
    let h2 := blockEffect a b c stride depth h1 (row) (col) (inner + half)
    let h3 := blockEffect a b c stride depth h2 (row) (col + half) (inner)
    let h4 := blockEffect a b c stride depth h3 (row) (col + half) (inner + half)
    let h5 := blockEffect a b c stride depth h4 (row + half) (col) (inner)
    let h6 := blockEffect a b c stride depth h5 (row + half) (col) (inner + half)
    let h7 := blockEffect a b c stride depth h6 (row + half) (col + half) (inner)
    let h8 := blockEffect a b c stride depth h7 (row + half) (col + half) (inner + half)
    h8















/-- Recursion includes the current call and eight children. -/
def callCount : Nat → Nat
  | 0 => 1
  | depth + 1 => 1 + 8 * callCount depth






/-- The ordinary inner-product sum, split into equal halves. -/
def innerProduct (a b : Int → Seq) (stride queryRow queryCol : Int) : Nat → Int → Int
  | 0, first => a queryRow first * b first queryCol
  | depth + 1, first =>
    innerProduct a b stride queryRow queryCol depth first +
    innerProduct a b stride queryRow queryCol depth (first + (2 ^ depth : Nat))

/-- The contribution of one block to a fixed output entry. -/
def contribution (a b : Int → Seq) (stride queryRow queryCol : Int)
    (depth : Nat) (row col inner : Int) : Int :=
  if row ≤ queryRow ∧ queryRow < row + (2 ^ depth : Nat) ∧
     col ≤ queryCol ∧ queryCol < col + (2 ^ depth : Nat)
  then innerProduct a b stride queryRow queryCol depth inner else 0











/-- Conventional finite summation over indices 0, ..., n-1. -/
def finiteSum : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, f => finiteSum n f + f n






open Algo2LeanCore.MatrixHeap

/-- Allocate a separate zero row for each matrix index in the interval. -/
def initializeRows (heap : Heap) (c : CollectionRef) (first : Int) : Nat → Heap
  | 0 => heap
  | count + 1 => initializeRows
      (seq_Seq_Int.set (heap.allocate (fun _ => 0)) c first heap.nextRef) c (first + 1) count







 

 

 

 







/-- The actual heap after allocating the default row and all n independent rows. -/
def zeroHeap (heap : Heap) (n : Nat) : Heap :=
  initializeRows (seq_Seq_Int.const (heap.allocate (fun _ => 0)) heap.nextRef).1 heap.nextCollection 0 n

def outputRows (heap : Heap) (n : Nat) (i : Int) : SeqRef :=
  if 0 ≤ i ∧ i < n then heap.nextRef + 1 + i.toNat else heap.nextRef













def inputRows (heap : Heap) (matrix : CollectionRef) (i : Int) : SeqRef :=
  (seq_Seq_Int.get heap matrix i).getD 0







/-- Deterministic resulting heap, including the independent output rows. -/
def resultHeap (heap : Heap) (a b : CollectionRef) (depth : Nat) : Heap :=
  blockEffect (inputRows heap a) (inputRows heap b) (outputRows heap (2 ^ depth))
    (2 ^ depth : Nat) depth (zeroHeap heap (2 ^ depth)) 0 0 0



 def initializationState (heap : Heap) (a b : CollectionRef) (n : Int) : State_matrix_recursive :=
  { v0 := a, v1 := b, v2 := n, v3 := heap.nextCollection,
    t20 := heap.nextCollection, t21 := heap.nextRef }





/-- Conventional matrix product; cells outside its n-by-n extent are zero. -/
def matrixProduct (a b : Values) (n : Nat) : Values := fun row col =>
  if 0 ≤ row ∧ row < n ∧ 0 ≤ col ∧ col < n then
    finiteSum n (fun inner => a row inner * b inner col)
  else 0





/-- Only the named multiplication and recursion counters change. -/
def costs (depth : Nat) : Clocks := fun name =>
  if name = "multiplications" then 8 ^ depth else
  if name = "calls" then callCount depth else 0










-- Main result: Running time


-- Main result: Correctness






end MatrixRecursiveAnalysis

end CLRS


