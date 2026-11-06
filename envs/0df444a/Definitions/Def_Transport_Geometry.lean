-- Prove2me | Definitions.Def_Transport_Geometry
-- name    : Transport_Geometry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:33:04.176773+00:00
-- url     : https://prove2.me/theorems/b0877ff5-de93-42f4-b4d9-261d8d2778a5
-- title:
--   Geometry
-- statement:
--   Definitions and structural lemmas for Geometry, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Geometry.lean

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
namespace RH.Transport.Geometry
noncomputable section
def ell (p : ℝ) : ℝ := 1 / 6 + p
def width (p : ℝ) : ℝ := 5 / 6 - p
def lx (p : ℝ) : ℝ := 17 / 48 - p / 2
def ly (p : ℝ) : ℝ := 23 / 48 - p / 2
def h (p : ℝ) : ℝ := 13 / 16 + 3 * p / 2
def b : ℝ := 1 / 8
def boundary (p : ℝ) : ℝ := 7 / 8 - p / 4
def signal (p s : ℝ) : ℝ := s + lx p / 2 - 1 + h p / 6
def lowExponent (p : ℝ) : ℝ := lx p / 2 + b / 12
def subsetWidth (p d : ℝ) : ℝ := width p - 2 * d
def subsetEll (p d : ℝ) : ℝ := ell p - d
def subsetLoss (p d : ℝ) : ℝ :=
  -d + max 0 (5 * ell p - 1 + d) / 8
end
end RH.Transport.Geometry


