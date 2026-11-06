-- Prove2me | Definitions.Def_GradSuffice_thm8L
-- name    : GradSuffice_thm8L
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:24.259793+00:00
-- url     : https://prove2.me/theorems/edf76222-c7e5-4f0e-8565-bd9532a3413a
-- title:
--   The block length $L$ of the Theorem 8 construction
-- statement:
--   The hard instance of Theorem 8 groups the levels of the shattered tree into blocks of length
--   $$L:=\Big\lceil\frac{32768\,D^2}{\theta^2}\log(32D^2)\Big\rceil ,$$
--   with the natural logarithm; it uses a tree of depth exactly $DL$.
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), §7, p.19

import Mathlib

namespace GradSuffice

/-- **The block length `L := ⌈(32768 D²/θ²) log(32D²)⌉`.** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, §7, p.19.

**Formalization Note.** `log` is the natural logarithm. -/
noncomputable def thm8L (θ : ℝ) (D : ℕ) : ℕ :=
  ⌈32768 * (D : ℝ) ^ 2 / θ ^ 2 * Real.log (32 * (D : ℝ) ^ 2)⌉₊

end GradSuffice


