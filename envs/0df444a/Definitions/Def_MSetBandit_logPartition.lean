-- Prove2me | Definitions.Def_MSetBandit_logPartition
-- name    : MSetBandit_logPartition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:43.917802+00:00
-- url     : https://prove2.me/theorems/94b6fbf2-f7de-4b5f-af7f-d0a4914fe74f
-- title:
--   Log-partition function $F(\theta)$
-- statement:
--   The **log-partition function** of the weighted $m$-set family is
--   $$
--   F(\theta)=\log\sum_{A\subseteq[d]:\,|A|=m}\exp\Big(\sum_{i\in A}\theta_i\Big)=\log\sum_{x\in\mathcal X}e^{\theta^\top x},\qquad\theta\in\mathbb R^d,
--   $$
--   so that $\log p_\theta(x)=\theta^\top x-F(\theta)$ (natural logarithm).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix D, p.33

import Mathlib
import Definitions.Def_MSetBandit_ind
open Matrix

namespace MSetBandit

/-- **The log-partition function `F(θ)`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix D, p.33:
`F(θ) := log Σ_{A⊆[d], |A|=m} exp(Σ_{i∈A} θ_i) = log e_m(e^{θ_1}, …, e^{θ_d})`; equivalently
`F(θ) = log Σ_{x∈X} exp(θ^⊤ x)` (p.14, after (24)). -/
noncomputable def logPartition {d : ℕ} (m : ℕ) (θ : Fin d → ℝ) : ℝ :=
  Real.log (∑ x : Action d m, Real.exp (θ ⬝ᵥ ind x))

end MSetBandit


