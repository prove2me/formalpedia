-- Prove2me | Definitions.Def_RBMSensitivity_Data_Assumption_2_12
-- name    : RBMSensitivity_Data_Assumption_2_12
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:32:57.608672+00:00
-- url     : https://prove2.me/theorems/0e7378fe-0032-4a87-85bb-c6c2d1f9fdc3
-- title:
--   Assumption 2.12: Hölder continuity of the Jacobians
-- statement:
--   **Assumption 2.12.** There exists $\kappa'<\infty$ and $\gamma\in(0,1]$ such that for all $\alpha,\tilde\alpha\in U$,
--   $$|b'(\alpha)-b'(\tilde\alpha)|+\|\sigma'(\alpha)-\sigma'(\tilde\alpha)\|+\|R'(\alpha)-R'(\tilde\alpha)\|\le\kappa'|\alpha-\tilde\alpha|^\gamma.$$
--   Here $\|\cdot\|$ is the Frobenius norm.
--
--   Under this assumption there is a pathwise unique derivative process along an RBM.
-- source:
--   Lipshutz, Ramanan, Sensitivity analysis for the stationary distribution of RBM, arXiv:1907.00472v2, https://arxiv.org/abs/1907.00472v2, Assumption 2.12, p.7

import Mathlib
import Definitions.Def_RBMSensitivity_Data_sigmaDeriv
import Definitions.Def_RBMSensitivity_Data_RDeriv
import Definitions.Def_RBMSensitivity_Data_bDeriv
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal RealInnerProductSpace
open scoped Matrix.Norms.Frobenius

namespace RBMSensitivity

/-- Assumption 2.12: arXiv:1907.00472v2, p.7. There are `κ' < ∞` and `γ ∈ (0, 1]` with
`|b'(α) - b'(α̃)| + ‖σ'(α) - σ'(α̃)‖ + ‖R'(α) - R'(α̃)‖ ≤ κ'|α - α̃|^γ` for all `α, α̃ ∈ U`.

**Formalization Note.** `‖·‖` on matrices is the Frobenius norm (p.4), through the scoped instance
`Matrix.Norms.Frobenius`. -/
def Data.Assumption_2_12 {J : ℕ} (D : Data J) : Prop :=
  ∃ κ' γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧ ∀ α ∈ D.U, ∀ α' ∈ D.U,
    ‖D.bDeriv α - D.bDeriv α'‖ + ‖D.sigmaDeriv α - D.sigmaDeriv α'‖ +
      ‖D.RDeriv α - D.RDeriv α'‖ ≤ κ' * |α - α'| ^ γ

end RBMSensitivity


