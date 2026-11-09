-- Prove2me | Definitions.Def_GevreyGibbsSep_grad
-- name    : GevreyGibbsSep_grad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:34:47.977348+00:00
-- url     : https://prove2.me/theorems/5b3a0e92-164e-46d2-81bd-1eea82991795
-- title:
--   Gradient $\nabla E(x)$
-- statement:
--   The gradient $\nabla E(x)=(\partial_1E(x),\dots,\partial_dE(x))\in\mathbb R^d$ of a potential $E$, the quantity returned by the coherent oracle (7).
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Eq. (7), p.6

import Mathlib

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

/-- The gradient `∇E(x) = (∂_1 E(x), …, ∂_d E(x))` (arXiv:2608.24527 (sha256 d4fd40eb…),
Eq. (7), p.6). -/
noncomputable def grad {d : ℕ} (E : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ E x (Pi.single i 1)

end GevreyGibbsSep


