-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Basic
-- name    : OAI_NumberTheory_DirichletL_Detector_Basic
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:49.435598+00:00
-- url     : https://prove2.me/theorems/d87d98a4-5dcf-4bc1-a487-5b3a282ab213
-- title:
--   Basic
-- statement:
--   Definitions and structural lemmas for Basic, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Basic.lean

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace OAI
namespace SevenEighths.Probe
noncomputable section
def principalScalar {ι : Type*} (slots : Finset ι) (Z ℓ : ℝ) (S : ι → ℝ) : ℝ :=
  (-1) ^ slots.card * Z ^ (-ℓ / 6) * ∏ i ∈ slots, S i
def normalizedProbe (I A : ℝ → ℂ) (c : ℂ) (Z : ℝ) : ℂ := I Z / (c * A Z)
end
end SevenEighths.Probe
end OAI


