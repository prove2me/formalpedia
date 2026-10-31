-- Prove2me | Definitions.Def_RBMSensitivity_pathSup
-- name    : RBMSensitivity_pathSup
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:28:35.975906+00:00
-- url     : https://prove2.me/theorems/15225285-a78c-4bd6-8e8d-ef5770774dd1
-- title:
--   The path supremum $\|W\|_T$
-- statement:
--   For a path $W$ and $T<\infty$, $\|W\|_T:=\sup_{0\le s\le T}|W(s)|$.
--
--   It controls the noise in the pathwise bound on the derivative process.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Lemma 7.5, (7.7), p.29

import Mathlib
import Definitions.Def_RBMSensitivity_E
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace

namespace RBMSensitivity

/-- `‖W‖_T := sup_{0 ≤ s ≤ T} |W(s)|`: arXiv:1907.00472v2, (7.7), p.29.

**Formalization Note.** The paper does not define the symbol. This is what the proof of Lemma 7.7
computes. `Set.Iic T` in `ℝ≥0` is `[0, T]`, nonempty and compact, so the supremum is of a bounded set
for a continuous path, that is, almost surely. -/
noncomputable def pathSup {J : ℕ} {Ω : Type*} (W : ℝ≥0 → Ω → E J) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ⨆ s : Set.Iic T, ‖W s ω‖

end RBMSensitivity


