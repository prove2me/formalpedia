-- Prove2me | Definitions.Def_SumProduct_CubeSection
-- name    : SumProduct_CubeSection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T23:48:19.569996+00:00
-- url     : https://prove2.me/theorems/844ed2ee-e26e-40ea-8fe0-fa8e6666cff7
-- title:
--   Cube Section
-- statement:
--   Definitions and structural lemmas for Cube Section, from Mathlib Initiative and contributors's pinned A real sum-product counterexample conditional on Martinet’s tower theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/mathlib-initiative/sum_product/blob/80e4127a67742659d521466204c6d2d7e0ca2b3f/SumProduct/CubeSection.lean

import Definitions.Def_SumProduct_Boxes
set_option autoImplicit true
open MeasureTheory
open scoped Pointwise
namespace SumProduct
def cubeSection (ι : Type*) [Fintype ι] (r : ℝ) : Set (ι → ℝ) :=
  {y | (∀ i, |y i| ≤ r) ∧ |∑ i, y i| ≤ r}
variable {ι : Type*} [Fintype ι]
end SumProduct


