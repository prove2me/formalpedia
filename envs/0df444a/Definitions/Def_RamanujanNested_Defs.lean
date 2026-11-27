-- Prove2me | Definitions.Def_RamanujanNested_Defs
-- name    : RamanujanNested_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-27T04:56:05.762923+00:00
-- url     : https://prove2.me/theorems/20471cf1-e4d9-4637-af8d-45fa7d6534c1
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from Flaman55 (Flaman55/RamanujanNestedRadicals; see pinned Apache-2.0 LICENSE and source headers)'s pinned Convergence and exact values of Ramanujan-type nested radicals development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Flaman55/RamanujanNestedRadicals/blob/2b932baf2e72426583ef47a1bb23b4458879e959/RamanujanNested/Defs.lean

module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic
set_option autoImplicit true
@[expose] public section
namespace RamanujanNested
@[expose] public noncomputable def rollUp (a : ℕ → ℝ) (T : ℝ) : ℕ → ℝ
  | 0 => T
  | (n + 1) => Real.sqrt (1 + a 1 * rollUp (fun k => a (k + 1)) T n)
@[expose] public noncomputable def truncRadical (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  rollUp a 1 N
@[expose] public noncomputable def rStar (A : ℝ) : ℝ :=
  (A + Real.sqrt (A ^ 2 + 4)) / 2
end RamanujanNested


