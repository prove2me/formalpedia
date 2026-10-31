-- Prove2me | Definitions.Def_RBMSensitivity_E
-- name    : RBMSensitivity_E
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:27:38.099041+00:00
-- url     : https://prove2.me/theorems/8276e137-7079-46e7-99ef-b5a2af1daff1
-- title:
--   The Euclidean space $\mathbb R^J$
-- statement:
--   The state space $\mathbb R^J$, with Euclidean inner product $\langle\cdot,\cdot\rangle$ and norm $|\cdot|$.
--
--   All processes and directions of reflection in this mission take values in this space.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, §1.4, p.4

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `ℝ^J` with the Euclidean inner product and norm: arXiv:1907.00472v2, §1.4, p.4.

**Formalization Note.** All vectors of the paper live in this type. Vectors are columns. -/
abbrev E (J : ℕ) : Type := EuclideanSpace ℝ (Fin J)

end RBMSensitivity


