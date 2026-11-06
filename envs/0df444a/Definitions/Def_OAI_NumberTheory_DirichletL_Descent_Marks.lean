-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Marks
-- name    : OAI_NumberTheory_DirichletL_Descent_Marks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:11.506201+00:00
-- url     : https://prove2.me/theorems/0f6b4c77-1b4e-451c-a5e1-59739cac6b26
-- title:
--   Marks
-- statement:
--   Definitions and structural lemmas for Marks, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Marks.lean

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace OAI
namespace SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]
def primeSlot (L : Finset ι) (a : ι → ℂ) (A : Finset ι) : ℂ :=
  ∑ p ∈ L, if p ∈ A then a p else 0
def primeMark (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : ℂ := ∏ i ∈ I, primeSlot (L i) (a i) A
end
end SevenEighths.InverseMoment
end OAI


