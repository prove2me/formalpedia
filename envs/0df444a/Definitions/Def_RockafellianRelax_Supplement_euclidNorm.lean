-- Prove2me | Definitions.Def_RockafellianRelax_Supplement_euclidNorm
-- name    : RockafellianRelax_Supplement_euclidNorm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T03:10:39.521797+00:00
-- url     : https://prove2.me/theorems/c014b56e-4be5-4a8a-8318-d5d36501c819
-- title:
--   Euclidean norm $\|x\|_2$ of a coordinate vector
-- statement:
--   For a finite index set $\iota$ and $x \in \mathbb R^\iota$, the **Euclidean norm** is
--
--   $$
--   \|x\|_2 = \Bigl(\sum_{i\in\iota} x_i^2\Bigr)^{1/2},
--   $$
--
--   and the closed ball $\mathbb B(0,\rho)$ of the paper is $\{x \mid \|x\|_2 \le \rho\}$.
--
--   It measures the perturbations, the tilts and the radii in Theorems 4.3–4.6.
--
--   **Formalization Note** Mathlib's norm on `ι → ℝ` is the sup norm, so $\|x\|_2$ is the norm of the corresponding point of `EuclideanSpace ℝ ι`.
-- source:
--   Royset, Chen & Eckstrand, Rockafellian Relaxation and Stochastic Optimization under Perturbations, arXiv:2204.04762v4, §4.1, p.12 (notation for balls)

import Mathlib

namespace RockafellianRelax.Supplement

/-- **Euclidean norm** `‖x‖₂` of a coordinate vector.
Royset, Chen & Eckstrand, arXiv:2204.04762v4, §4.1, p.12: "B(x̄, ρ) = {x ∈ ℝⁿ | ‖x − x̄‖₂ ≤ ρ}".

**Formalization Note.** The norm that Mathlib puts on `ι → ℝ` is the sup norm, so `‖x‖₂` is taken
in `EuclideanSpace ℝ ι`. Thus `x ∈ B(0, ρ)` is `euclidNorm x ≤ ρ`. -/
noncomputable def euclidNorm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 x : EuclideanSpace ℝ ι)‖

end RockafellianRelax.Supplement


