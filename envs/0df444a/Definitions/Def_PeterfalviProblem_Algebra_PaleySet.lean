-- Prove2me | Definitions.Def_PeterfalviProblem_Algebra_PaleySet
-- name    : PeterfalviProblem_Algebra_PaleySet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T04:56:00.37726+00:00
-- url     : https://prove2.me/theorems/18e519a9-0415-40d7-8201-050f1e9ba7cf
-- title:
--   Paley Set
-- statement:
--   Definitions and structural lemmas for Paley Set, from Yawara Ishida (yawara/peterfalvi-problem; see pinned Apache-2.0 LICENSE and source headers)'s pinned Resolution of Péterfalvi problem for p = 3 and SL(2, 2^q) witness for p = 2 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/yawara/peterfalvi-problem/blob/698b7ae0af649f7fad48c482aa8ff0d2d14336bb/PeterfalviProblem/Algebra/PaleySet.lean

import Mathlib.FieldTheory.Finite.Basic
set_option autoImplicit false
namespace PeterfalviProblem.Paley
open Finset
variable {F : Type*} [Field F]
def paleySet (F : Type*) [Field F] : Set F :=
  {a | a ≠ 0 ∧ IsSquare a ∧ a + 1 ≠ 0 ∧ IsSquare (a + 1)}
section PowDiff
variable {E : ℕ}
def powDiff (E : ℕ) (a : F) : F := (a + 1) ^ E - a ^ E
section Conjugation
def powDiffConj (E : ℕ) (a : F) : F := a ^ E * (powDiff E a)⁻¹
def powDiffConjNeg (E : ℕ) (a : F) : F := -(a + 1) ^ E * (powDiff E a)⁻¹
end Conjugation
end PowDiff
end PeterfalviProblem.Paley


