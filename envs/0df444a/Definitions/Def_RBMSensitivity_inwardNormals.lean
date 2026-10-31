-- Prove2me | Definitions.Def_RBMSensitivity_inwardNormals
-- name    : RBMSensitivity_inwardNormals
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:22.731748+00:00
-- url     : https://prove2.me/theorems/410772c6-02b5-4468-b8a5-35f749dd6fc4
-- title:
--   The inward normal vectors $\nu_B(z)$
-- statement:
--   Given a convex set $B$,
--   $$\nu_B(z):=\{\nu\in\mathbb S^{J-1}:\langle\nu,y-z\rangle\ge 0\text{ for all }y\in B\}$$
--   is the set of inward normal vectors to $B$ at $z\in\partial B$.
--
--   It enters the geometric condition of Assumption 2.4.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.6

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `ν_B(z) := {ν ∈ S^{J-1} : ⟨ν, y - z⟩ ≥ 0 for all y ∈ B}`: arXiv:1907.00472v2, §2.1, p.6. -/
def inwardNormals {J : ℕ} (B : Set (E J)) (z : E J) : Set (E J) :=
  {ν | ‖ν‖ = 1 ∧ ∀ y ∈ B, 0 ≤ ⟪ν, y - z⟫}

end RBMSensitivity


