-- Prove2me | Definitions.Def_GradSuffice_thm8D
-- name    : GradSuffice_thm8D
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:21.947705+00:00
-- url     : https://prove2.me/theorems/575aa8b4-3def-4dc4-a5e2-2261c9dfed71
-- title:
--   The session length $D$ of Theorem 8
-- statement:
--   For a margin $\theta$ and a tree depth $m$, Theorem 8 sets
--   $$D:=\Big\lfloor\Big(\frac{\theta^2m}{65536\,\log(16m^2)}\Big)^{1/3}\Big\rfloor ,$$
--   with the natural logarithm. The theorem assumes $D\ge1$.
--
--   **Formalization Note** At $m=0$ the value is $0$, which the assumption $D\ge1$ excludes.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Theorem 8, p.18

import Mathlib

namespace GradSuffice

/-- **The session length `D := ⌊(θ²m / (65536 log(16m²)))^{1/3}⌋`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Theorem 8, p.18.

**Formalization Note.** `log` is the natural logarithm; the cube root is `Real.rpow` with exponent
`1/3` of a nonnegative base (for `m ≥ 1`, `log(16m²) > 0`). At `m = 0` the value is `0`. -/
noncomputable def thm8D (θ : ℝ) (m : ℕ) : ℕ :=
  ⌊(θ ^ 2 * (m : ℝ) / (65536 * Real.log (16 * (m : ℝ) ^ 2))) ^ (1 / 3 : ℝ)⌋₊

end GradSuffice


