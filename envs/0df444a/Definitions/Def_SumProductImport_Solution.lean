-- Prove2me | Definitions.Def_SumProductImport_Solution
-- name    : SumProductImport_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T01:08:26.772873+00:00
-- url     : https://prove2.me/theorems/1e22ff6f-e8ed-4cb4-9dad-b2b4e07c4f63
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/Solution.lean

import Definitions.Def_SumProduct
set_option autoImplicit true
open scoped NumberField
open Pointwise
def MartinetTotallyRealTowers : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d


