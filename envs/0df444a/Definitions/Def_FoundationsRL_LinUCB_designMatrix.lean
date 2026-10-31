-- Prove2me | Definitions.Def_FoundationsRL_LinUCB_designMatrix
-- name    : FoundationsRL_LinUCB_designMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:21:10.656884+00:00
-- url     : https://prove2.me/theorems/ec1d4052-8159-4632-b429-bc79ef914287
-- title:
--   Regularized design matrix $\widetilde\Sigma^t$
-- statement:
--   The **regularized design matrix** of round $t$ is
--
--   $$
--   \widetilde\Sigma^t=\sum_{i=1}^{t-1}\phi(x^i,\pi^i)\phi(x^i,\pi^i)^{\top}+I.
--   $$
--
--   It is the matrix whose norm shapes the confidence ellipsoid of LinUCB, and it is always positive definite.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, LinUCB algorithm box, p. 43; Eq. (3.25), p. 44

import Mathlib
import Definitions.Def_FoundationsRL_LinUCB_ContextualBanditRun

open MeasureTheory ProbabilityTheory Matrix

namespace FoundationsRL.LinUCB

/-- The regularized design matrix `Σ̃^t = ∑_{i<t} ϕ(x^i, π^i) ϕ(x^i, π^i)ᵀ + I` of round `t`
(Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*, arXiv:2312.16730v1, algorithm box, p. 43, and Eq. (3.25), p. 44). -/
noncomputable def designMatrix {Ω X Act : Type*} {mΩ : MeasurableSpace Ω} [MeasurableSpace X]
    [MeasurableSpace Act] {P : Measure Ω} {Mstar : Kernel (X × Act) ℝ} {d : ℕ}
    (ϕ : X → Act → Fin d → ℝ) (R : ContextualBanditRun P Mstar) (t : ℕ) (ω : Ω) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ i ∈ Finset.range t, vecMulVec (ϕ (R.x i ω) (R.act i ω)) (ϕ (R.x i ω) (R.act i ω)) + 1

end FoundationsRL.LinUCB


