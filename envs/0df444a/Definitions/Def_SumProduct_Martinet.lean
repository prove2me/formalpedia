-- Prove2me | Definitions.Def_SumProduct_Martinet
-- name    : SumProduct_Martinet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:45:12.724594+00:00
-- url     : https://prove2.me/theorems/2faf9e4a-de70-4ba2-823a-4f0f40263eb1
-- title:
--   Martinet
-- statement:
--   Definitions and structural lemmas for Martinet, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/Martinet.lean

import Mathlib
set_option autoImplicit true
namespace SumProduct
def MartinetTotallyRealTowers : Prop :=
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d
end SumProduct


