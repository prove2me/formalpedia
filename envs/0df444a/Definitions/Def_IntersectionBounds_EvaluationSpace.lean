-- Prove2me | Definitions.Def_IntersectionBounds_EvaluationSpace
-- name    : IntersectionBounds_EvaluationSpace
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T12:36:59.641024+00:00
-- url     : https://prove2.me/theorems/5dbccbdc-eaac-4527-a381-f7889985d548
-- title:
--   Evaluation Space
-- statement:
--   Definitions and structural lemmas for Evaluation Space, from Juan Pablo Traverso Gianini (jtraverso/restricted-intersections; see pinned Apache-2.0 LICENSE and source headers)'s pinned Ray-Chaudhuri-Wilson theorem for uniform families with restricted intersections development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/restricted-intersections/blob/ebb90800eda4ec83cc18c6da2135b8718757f6e2/IntersectionBounds/EvaluationSpace.lean

module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.NormNum
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace IntersectionBounds
open Finset Submodule
universe u v
variable {V : Type u} {K : Type v} [Field K]
variable (F : Finset (Finset V))
open Classical in
/-- A squarefree monomial evaluated at the characteristic vectors of the family. -/
noncomputable def indicator (T : Finset V) : F → K := fun B => if T ⊆ B.val then 1 else 0
noncomputable def degreeSpace (d : ℕ) : Submodule K (F → K) :=
  span K ((indicator F) '' {T : Finset V | T.card ≤ d})
noncomputable def exactSpace (d : ℕ) : Submodule K (F → K) :=
  span K ((indicator F) '' {T : Finset V | T.card = d})
open Classical in
/-- The separating polynomial, evaluated at every member of the family. -/
noncomputable def separator (L : Finset K) (A : Finset V) : F → K :=
  ∏ l ∈ L, (fun B => ((A ∩ B.val).card : K) - l)
end IntersectionBounds


