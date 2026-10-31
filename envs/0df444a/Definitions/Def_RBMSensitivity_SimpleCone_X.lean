-- Prove2me | Definitions.Def_RBMSensitivity_SimpleCone_X
-- name    : RBMSensitivity_SimpleCone_X
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:31:05.668003+00:00
-- url     : https://prove2.me/theorems/e713c9c8-c537-427e-829f-6a1bc99285d7
-- title:
--   The joint state space $\mathbb X$
-- statement:
--   The state space of the joint RBM-derivative process:
--   $$\mathbb X:=\bigcup_{x\in G}(\{x\}\times\mathbb H_x)\subseteq G\times\mathbb R^J.$$
--
--   It is a separable metric space but it is not closed in $G\times\mathbb R^J$ (Remark 3.1), so it is not Polish. This is the reason the usual tools for stationary distributions need care here.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §3.1, (3.1), p.9

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone_G
import Definitions.Def_RBMSensitivity_SimpleCone_H
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The state space of the joint process, (3.1): arXiv:1907.00472v2, §3.1, p.9,
`X := ⋃_{x ∈ G} ({x} × H_x) ⊆ G × ℝ^J`. -/
def SimpleCone.X {J : ℕ} (C : SimpleCone J) : Set (E J × E J) :=
  {ξ | ξ.1 ∈ C.G ∧ ξ.2 ∈ C.H ξ.1}

end RBMSensitivity


