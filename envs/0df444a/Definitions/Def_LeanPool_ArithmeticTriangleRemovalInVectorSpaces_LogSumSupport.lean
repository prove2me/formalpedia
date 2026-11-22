-- Prove2me | Definitions.Def_LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
-- name    : LeanPool_ArithmeticTriangleRemovalInVectorSpaces_LogSumSupport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T10:08:38.382412+00:00
-- url     : https://prove2.me/theorems/9afaee9d-6b3d-4e1f-b226-56c810ddb2b3
-- title:
--   Log Sum Support
-- statement:
--   Definitions and structural lemmas for Log Sum Support, from Gabriel Dahia; LeanPool contributors; Terence Tao (pinned Mathlib Log.Sum support)'s pinned A tight bound for Green's arithmetic triangle removal lemma in vector spaces development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/ArithmeticTriangleRemovalInVectorSpaces/LogSumSupport.lean

module
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Analysis.SumIntegralComparisons
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open Nat hiding log log_pos
open Finset intervalIntegral MeasureTheory
namespace Real
variable {x : ℝ} (N : ℕ)
end Real


