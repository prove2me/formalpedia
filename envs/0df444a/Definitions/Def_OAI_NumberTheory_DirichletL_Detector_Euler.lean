-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Detector_Euler
-- name    : OAI_NumberTheory_DirichletL_Detector_Euler
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:31.438234+00:00
-- url     : https://prove2.me/theorems/c9f9ef9f-1083-484e-9a9b-8374a6e86cbf
-- title:
--   Euler
-- statement:
--   Definitions and structural lemmas for Euler, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Detector/Euler.lean

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace OAI
noncomputable section
namespace SevenEighths.ProbeEuler
def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)
def markedTableSeries (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ∑' r : ℕ, R ^ r *
    ((∑' m : ℕ, (R * (1 - qInv) * V ^ m - K * V ^ (m + a))) + J)
end SevenEighths.ProbeEuler
end
end OAI


