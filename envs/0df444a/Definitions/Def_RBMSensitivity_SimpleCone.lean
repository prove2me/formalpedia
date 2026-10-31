-- Prove2me | Definitions.Def_RBMSensitivity_SimpleCone
-- name    : RBMSensitivity_SimpleCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:18.16514+00:00
-- url     : https://prove2.me/theorems/c33798b7-9b11-4a46-93d4-0457927b69eb
-- title:
--   A simple polyhedral cone: the unit normals $n_1,\dots,n_J$
-- statement:
--   A **simple polyhedral cone** in $\mathbb R^J$ is specified by $J$ linearly independent unit vectors $n_1,\dots,n_J\in\mathbb S^{J-1}$. "Simple" means that the number of faces equals the dimension and that the normals are linearly independent.
--
--   This is the fixed domain of the reflected process.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, pp.4–5

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The data of a simple polyhedral cone in `ℝ^J`: arXiv:1907.00472v2, §2.1, pp.4–5, "for linearly
independent unit vectors n_i ∈ S^{J-1}, i = 1, . . . , J". The cone itself is `SimpleCone.G`. -/
structure SimpleCone (J : ℕ) where
  /-- The inward unit normals `n_1, …, n_J`. -/
  n : Fin J → E J
  n_unit : ∀ i, ‖n i‖ = 1
  n_indep : LinearIndependent ℝ n

end RBMSensitivity


