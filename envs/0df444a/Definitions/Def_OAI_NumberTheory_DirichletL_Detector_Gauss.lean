-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Gauss
-- name    : OAI_NumberTheory_DirichletL_Detector_Gauss
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:19.582202+00:00
-- url     : https://prove2.me/theorems/d5404d7e-3beb-4251-9ddd-631f159a274f
-- title:
--   Gauss
-- statement:
--   Definitions and structural lemmas for Gauss, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Gauss.lean

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace OAI
namespace SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section
def frequencyGauss {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ v : F, ξ v * ψ (h * v)
def normalizedGauss {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F) : ℂ)
end
end SevenEighths.ProbeGauss
end OAI


