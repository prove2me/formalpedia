-- Prove2me | Definitions.Def_TeschlODE_IntervalMaps_IsFractal
-- name    : TeschlODE_IntervalMaps_IsFractal
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T18:36:28.905329+00:00
-- url     : https://prove2.me/theorems/2e1c8394-b590-4203-b170-c092a5f5c2d9
-- title:
--   Fractal set: Hausdorff dimension not an integer
-- statement:
--   A set $s$ is **fractal** if its Hausdorff dimension $\dim_H(s)$ (11.44) is not an integer.
--
--   **Formalization Note.** Mathlib's `dimH` takes values in $[0, \infty]$ and agrees with (11.44) (it is defined from the diameter-normalized Hausdorff measures, the book's $h^\alpha$). "Not an integer" is read as: $\dim_H(s) \ne \infty$ and $\dim_H(s) \ne k$ for every $k \in \mathbb{N}_0$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 307, §11.6 (definition of fractal), and p. 309, Eq. (11.44)

import Mathlib

namespace TeschlODE.IntervalMaps

/-- Teschl, §11.6, p. 307: a set is fractal if its Hausdorff dimension (11.44) is not an integer.
Mathlib's `dimH` takes values in `[0, ∞]`; "not an integer" is read as: finite and different
from every natural number (a Hausdorff dimension is never negative). -/
noncomputable def IsFractal {X : Type*} [EMetricSpace X] (s : Set X) : Prop :=
  dimH s ≠ ⊤ ∧ ∀ k : ℕ, dimH s ≠ (k : ENNReal)

end TeschlODE.IntervalMaps


