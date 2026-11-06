-- Prove2me | Definitions.Def_Transport_ReflectedExponent
-- name    : Transport_ReflectedExponent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:34:49.417179+00:00
-- url     : https://prove2.me/theorems/5888da5c-5f42-42d8-829d-05899f427697
-- title:
--   Reflected Exponent
-- statement:
--   Definitions and structural lemmas for Reflected Exponent, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/ReflectedExponent.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace RH.Transport.Reflected
noncomputable section
def hybridSaving (v za : ℝ) : ℝ := min v (min za ((v + za) / 3))
def reflectedExponent (O₀ H S₀ B₀ za v ell el Td : ℝ) : ℝ :=
  O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - hybridSaving v za - ell -
    2 * el / 3 - max 0 (Td - v - 3 * ell - el) / 2
def reflectedLoss (E d : ℝ) : ℝ := max 0 (5 * E - 1 + d) / 4
end
end RH.Transport.Reflected


