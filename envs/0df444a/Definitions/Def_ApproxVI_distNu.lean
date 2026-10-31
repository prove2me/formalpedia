-- Prove2me | Definitions.Def_ApproxVI_distNu
-- name    : ApproxVI_distNu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:14:10.232797+00:00
-- url     : https://prove2.me/theorems/cdee48f1-9bd1-4126-9b05-346b1a6a7545
-- title:
--   Point-to-set distance $d_\nu(x,B)$ in the weighted max-norm
-- statement:
--   For $x\in\mathbb R^d$ and $B\subseteq\mathbb R^d$,
--
--   $$
--   d_\nu(x,B)=\inf\{\|x-y\|_\nu:\ y\in B\}.
--   $$
--
--   It is the building block of the weighted Hausdorff metric $H_\nu$.
--
--   **Formalization Note** The infimum is taken in the extended nonnegative reals $[0,\infty]$, so $d_\nu(x,\emptyset)=\infty$.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §5, Definition (Hausdorff metric), pp.14–15

import Mathlib
import Definitions.Def_ApproxVI_wNorm

namespace ApproxVI

open scoped ENNReal

/-- The point-to-set distance `d_ν(x, B) := inf{‖x − y‖_ν | y ∈ B}` of Ramaswamy & Bhatnagar,
*Analyzing Approximate Value Iteration Algorithms*, arXiv:1709.04673v5, §5, Definition of the
weighted Hausdorff metric, pp.14–15.

**Formalization Note** The infimum is taken in `ℝ≥0∞` (the distances are nonnegative), so it
is `∞` for `B = ∅` instead of the junk value `0` of a real `sInf`. -/
noncomputable def distNu {d : ℕ} (ν : Fin d → ℝ) (x : Fin d → ℝ) (B : Set (Fin d → ℝ)) : ℝ≥0∞ :=
  ⨅ y ∈ B, ENNReal.ofReal (wNorm ν (x - y))

end ApproxVI


