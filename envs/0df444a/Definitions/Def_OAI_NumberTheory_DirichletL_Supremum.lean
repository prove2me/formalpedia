-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Supremum
-- name    : OAI_NumberTheory_DirichletL_Supremum
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:06.558573+00:00
-- url     : https://prove2.me/theorems/7a817dbc-79aa-4fbd-a160-75b3b5fcc297
-- title:
--   Supremum
-- statement:
--   Definitions and structural lemmas for Supremum, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Supremum.lean

import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace OAI
namespace SevenEighths.Supremum
noncomputable section
def continuationMargin (β ω σ : ℝ) : ℝ := min (β - 7 / 8 - ω) σ
end
end SevenEighths.Supremum
end OAI


