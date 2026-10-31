-- Prove2me | Definitions.Def_SweepingDesing_curveLength
-- name    : SweepingDesing_curveLength
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:59.043088+00:00
-- url     : https://prove2.me/theorems/727372ba-e0b6-4558-8bc0-4cbf0ffd92bb
-- title:
--   §2.1 — length $\ell(\gamma)$ of a (piecewise) absolutely continuous curve
-- statement:
--   The length of a (piecewise) absolutely continuous curve $\gamma:I\to\mathbb R^n$ is
--
--   $$
--   \ell(\gamma)=\int_I\|\dot\gamma(t)\|\,dt\in[0,+\infty].
--   $$
--
--   For a piecewise absolutely continuous curve the jumps do not contribute: this is the integral of the speed, not the variation.
--
--   **Formalization Note** A lower Lebesgue integral in `ℝ≥0∞` of `‖deriv γ t‖`.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, p.4

import Mathlib
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, §2.1, p.4: the length of a (piecewise) absolutely continuous curve `γ : I → ℝⁿ`,
`ℓ(γ) := ∫_I ‖γ̇(t)‖ dt`.

**Formalization Note** A lower Lebesgue integral in `[0, +∞]` of `‖γ'(t)‖`. It is not the
variation of `γ`: jumps of a piecewise absolutely continuous curve do not count. -/
noncomputable def curveLength {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin n)) (I : Set ℝ) : ℝ≥0∞ :=
  ∫⁻ t in I, ‖deriv γ t‖ₑ

end SweepingDesing


