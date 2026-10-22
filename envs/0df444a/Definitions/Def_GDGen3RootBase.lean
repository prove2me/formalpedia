-- Prove2me | Definitions.Def_GDGen3RootBase
-- name    : GDGen3RootBase
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-12T06:07:45.606767+00:00
-- url     : https://prove2.me/theorems/e62276ae-f28f-4c5d-8c61-3acd77ca587d
-- title:
--   General-N explicit roots and small-step expressions
-- statement:
--   Explicit positive quadratic roots, reference roots, comparison polynomials, positivity recurrence and the small-step history expressions, all for arbitrary N.
-- source:
--   C:/Users/17632/Desktop/GD最终梯度紧界_任意N通用证明.md

import Definitions.Def_GDGen3Base
import Mathlib

noncomputable section

open Finset

namespace GDGen3

def rootXi (r : ℝ) (N i : ℕ) : ℝ :=
  if i = 0 then 0 else if i < N then
    (-(1 + C r N i) + Real.sqrt ((1 + C r N i) ^ 2 + 4 * X r N i / pj r (i + 1))) / 2
  else 1

def referenceXi (r : ℝ) (i : ℕ) : ℝ :=
  (1 + (i : ℝ) * (1 + r) - 1 / r ^ i) / ((1 + r) * (1 + 1 / r ^ (i + 1)))

def rootPoly (r v : ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  pj r (i + 1) * x * (1 + x + v * (i + 1) / ((1 + r) * pj r (i + 1)) - (1 - r) / (1 + r))
    - (v * (i : ℝ) * (i + 1) / 2 - (1 - r) * PiS r i) / (1 + r)

def rootE (r : ℝ) (i : ℕ) : ℝ :=
  (1 + r) / r ^ i - (1 - r) * (1 + (i : ℝ) * (1 + r)) - 2 * r

def rootNu (r : ℝ) (i : ℕ) : ℝ := (i + 1) / pj r (i + 1) - (i : ℝ) / pj r i

def rootJ (r v x : ℝ) (i : ℕ) : ℝ :=
  1 + pj r i / pj r (i + 1) - (1 - pj r i / pj r (i + 1)) * x + v / (1 + r) * rootNu r i

def smallK (N : ℕ) (h : ℝ) (f q : ℕ → ℝ) : ℝ :=
  2 * (∑ i ∈ range N, (f i - f N)) - (h - 1) * (∑ i ∈ range N, q i)
    - (N : ℝ) * (1 + (N : ℝ) * h) * q N

def scaledK (N : ℕ) (a s : ℝ) (f q : ℕ → ℝ) : ℝ :=
  2 * (∑ i ∈ range N, (f i - f N)) - s * (a - 1) * (∑ i ∈ range N, q i)
    - s * (N : ℝ) * (1 + (N : ℝ) * a) * q N

end GDGen3


