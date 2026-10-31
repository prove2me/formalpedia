-- Prove2me | Definitions.Def_ApproxVI_euclNorm
-- name    : ApproxVI_euclNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:24.365999+00:00
-- url     : https://prove2.me/theorems/02adcc99-a6c5-4072-b7ac-d32cf767f448
-- title:
--   The Euclidean norm $\|z\|$ on $\mathbb R^d$
-- statement:
--   For $z=(z_1,\dots,z_d)\in\mathbb R^d$, the **Euclidean norm** is
--
--   $$
--   \|z\|=\sqrt{z_1^2+\cdots+z_d^2}.
--   $$
--
--   It is the unsubscripted norm of the paper: it appears in the noise assumption (AV5), in the point-wise boundedness condition of a Marchaud map, in the norm comparison (11), in Lemma 7 and in the stability clause of Theorem 2.
--
--   **Formalization Note** $\mathbb R^d$ is represented as `Fin d → ℝ`. Mathlib's built-in norm on that type is the max-norm $\|z\|_\infty$, so the Euclidean norm is defined explicitly.
-- source:
--   Ramaswamy & Bhatnagar, Analyzing Approximate Value Iteration Algorithms, arXiv:1709.04673v5, §5, proof of Lemma 2, p.14 ("the standard Euclidean norm")

import Mathlib

namespace ApproxVI

/-- The standard Euclidean norm `‖z‖ = √(z₁² + … + z_d²)` on `ℝ^d`, as written in
Ramaswamy & Bhatnagar, *Analyzing Approximate Value Iteration Algorithms*, arXiv:1709.04673v5,
§5, proof of Lemma 2, p.14 ("‖z‖ = √(z₁² + . . . + z_d²) is the standard Euclidean norm").
It is the unsubscripted norm `‖·‖` of (AV5) (p.7), of the Marchaud condition (p.5), of (11)
(p.15) and of Lemma 7 (p.27).

**Formalization Note** `ℝ^d` is `Fin d → ℝ` (states indexed from `0`). Mathlib's `‖z‖` on
`Fin d → ℝ` is the sup norm `‖z‖_∞`, not the Euclidean norm, so the Euclidean norm is written
out explicitly here. -/
noncomputable def euclNorm {d : ℕ} (z : Fin d → ℝ) : ℝ :=
  Real.sqrt (∑ i, z i ^ 2)

end ApproxVI


