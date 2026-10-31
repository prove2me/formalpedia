-- Prove2me | Definitions.Def_RBMSensitivity_SimpleCone_GK
-- name    : RBMSensitivity_SimpleCone_GK
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:30:22.983168+00:00
-- url     : https://prove2.me/theorems/d368fcb2-c7cb-47e3-8fb9-1c0f9a8cb0c6
-- title:
--   The truncated cone $G_K$
-- statement:
--   For $K\in(0,\infty)$, $G_K:=\{x\in G:|x|\le K\}$, and $G_\infty:=G$.
--
--   The stopping times of §6 ask the RBM to end a face-visiting cycle in $G_K$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §6.1, p.21

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone_G
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `G_K := {x ∈ G : |x| ≤ K}` for `K ∈ (0, ∞)` and `G_∞ := G`: arXiv:1907.00472v2, §6.1, p.21. -/
def SimpleCone.GK {J : ℕ} (C : SimpleCone J) (K : ℝ≥0∞) : Set (E J) :=
  {x | x ∈ C.G ∧ ‖x‖ₑ ≤ K}

end RBMSensitivity


