-- Prove2me | Definitions.Def_RBMSensitivity_SimpleCone_G
-- name    : RBMSensitivity_SimpleCone_G
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:29:02.282267+00:00
-- url     : https://prove2.me/theorems/5f0cce87-4fce-47da-942b-88090162499c
-- title:
--   The cone $G=\bigcap_i\{x:\langle x,n_i\rangle\ge 0\}$
-- statement:
--   The cone
--   $$G:=\bigcap_{i=1,\dots,J}\{x\in\mathbb R^J:\langle x,n_i\rangle\ge 0\}.$$
--
--   Every RBM of the mission takes its values in $G$.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §2.1, p.4

import Mathlib
import Definitions.Def_RBMSensitivity_SimpleCone
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- The cone `G := ⋂_{i=1,…,J} {x ∈ ℝ^J : ⟨x, n_i⟩ ≥ 0}`: arXiv:1907.00472v2, §2.1, p.4. -/
def SimpleCone.G {J : ℕ} (C : SimpleCone J) : Set (E J) :=
  {x | ∀ i, 0 ≤ ⟪x, C.n i⟫}

end RBMSensitivity


