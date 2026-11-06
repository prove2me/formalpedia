-- Prove2me | Definitions.Def_MSetBandit_cov
-- name    : MSetBandit_cov
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:40:39.99431+00:00
-- url     : https://prove2.me/theorems/a5f31e6c-87bb-4579-b2d1-5c7fd80e8787
-- title:
--   Covariance matrix $\Sigma(p)$
-- statement:
--   The **covariance matrix** of $p\in\Delta(\mathcal X)$ is
--   $$
--   \Sigma(p)=\operatorname{Cov}_{X\sim p}(X)=M(p)-\mu(p)\mu(p)^\top .
--   $$
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4

import Mathlib
import Definitions.Def_MSetBandit_marg
import Definitions.Def_MSetBandit_secondMoment

namespace MSetBandit

/-- **Covariance matrix `Σ(p) = M(p) − µ(p)µ(p)^⊤`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4:
`Σ(p) := Cov_{X∼p}(X) = M(p) − µ(p)µ(p)^⊤`. -/
def cov {d m : ℕ} (p : Action d m → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  secondMoment p - Matrix.vecMulVec (marg p) (marg p)

end MSetBandit


