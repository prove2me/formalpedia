-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_Endpoint
-- name    : OAI_NumberTheory_DirichletL_Endpoint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:48.978287+00:00
-- url     : https://prove2.me/theorems/77dfb361-8c19-4e50-b0e3-677c50191650
-- title:
--   Endpoint
-- statement:
--   Definitions and structural lemmas for Endpoint, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Endpoint.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
set_option autoImplicit false
namespace OAI
namespace SevenEighths.Endpoint
noncomputable section
def denominator (y : ℝ) : ℝ := (37 + 34 * y) / 18
def primeWeight (y : ℝ) : ℝ := (7 + 18 * y + 8 * y ^ 2) / 9
def balanceDenominator (δ y : ℝ) : ℝ :=
  (5 / 6 - δ) * denominator y + δ * primeWeight y
def certificateWeight (y : ℝ) : ℝ := 51 + 41 * y
def balancedCutoff (δ y : ℝ) : ℝ :=
  1 + δ * primeWeight y / (2 * balanceDenominator δ y)
def balancedRowCount (δ y : ℝ) : ℝ :=
  1 - 5 / 6 + (5 / 6 - δ) * balancedCutoff δ y
def balancedExponent (δ y : ℝ) : ℝ :=
  -(1 / 48) + (2 / 3) * δ + δ * (1 / 2 - y) / 6 -
    (13 / 16) * (1 - balancedRowCount δ y)
end
end SevenEighths.Endpoint
end OAI


