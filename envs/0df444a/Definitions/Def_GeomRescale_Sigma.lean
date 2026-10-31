-- Prove2me | Definitions.Def_GeomRescale_Sigma
-- name    : GeomRescale_Sigma
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:14:35.091966+00:00
-- url     : https://prove2.me/theorems/95603bf9-1be7-46eb-8ef0-9e60e97c1f1e
-- title:
--   The cone $\Sigma_\mu$, display (11)
-- statement:
--   $$\Sigma_\mu = \{w \in \mathbb{R}^n : w^{\mathsf T} x \ge 0 \ \ \forall x \in B(f_\mu)\}.$$
--
--   This is the set of normal vectors of hyperplanes that weakly separate $0$ from $B(f_\mu)$.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (11), p.10

import Mathlib
import Definitions.Def_SchrijverSFM_Alg_Setting
import Definitions.Def_GeomRescale_enlarge

namespace GeomRescale

/-- The cone `Σ_μ = {w ∈ ℝⁿ : wᵀx ≥ 0 ∀ x ∈ B(f_μ)}` (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, display (11), p.10). -/
def Sigma {n : ℕ} (f : Finset (Fin n) → ℝ) (μ : ℝ) : Set (Fin n → ℝ) :=
  {w | ∀ x ∈ SchrijverSFM.Alg.baseB (enlarge f μ), 0 ≤ w ⬝ᵥ x}

end GeomRescale


