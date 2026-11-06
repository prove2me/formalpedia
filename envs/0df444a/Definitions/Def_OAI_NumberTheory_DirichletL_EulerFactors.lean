-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_EulerFactors
-- name    : OAI_NumberTheory_DirichletL_EulerFactors
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:44.432932+00:00
-- url     : https://prove2.me/theorems/6726527b-3d44-41de-93dc-393a472aca49
-- title:
--   Euler Factors
-- statement:
--   Definitions and structural lemmas for Euler Factors, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/EulerFactors.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace OAI
namespace SevenEighths.EulerFactors
noncomputable section
def factor (N : ℝ) (a s : ℂ) : ℂ := 1 - a * (N : ℂ) ^ (-s)
def deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a : ι → ℂ)
    (s : ℂ) : ℂ := ∏ p ∈ S, factor (N p) (a p) s
end
end SevenEighths.EulerFactors
end OAI


