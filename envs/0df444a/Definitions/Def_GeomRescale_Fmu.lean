-- Prove2me | Definitions.Def_GeomRescale_Fmu
-- name    : GeomRescale_Fmu
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:44.935334+00:00
-- url     : https://prove2.me/theorems/0d5d46c4-57e8-4868-837f-145bc0dc9e0b
-- title:
--   The set $F_\mu$, display (11)
-- statement:
--   $$F_\mu = \Sigma_\mu \cap \mathbb{B}^n,$$
--
--   where $\mathbb{B}^n$ is the closed Euclidean unit ball.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (11), p.10

import Mathlib
import Definitions.Def_GeomRescale_norm2
import Definitions.Def_GeomRescale_Sigma

namespace GeomRescale

/-- The set `F_μ = Σ_μ ∩ 𝔹ⁿ` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (11), p.10), with `𝔹ⁿ` the closed Euclidean unit ball. -/
def Fmu {n : ℕ} (f : Finset (Fin n) → ℝ) (μ : ℝ) : Set (Fin n → ℝ) :=
  Sigma f μ ∩ {w | norm2 w ≤ 1}

end GeomRescale


