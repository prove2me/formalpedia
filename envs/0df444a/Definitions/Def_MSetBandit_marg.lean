-- Prove2me | Definitions.Def_MSetBandit_marg
-- name    : MSetBandit_marg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:34.346946+00:00
-- url     : https://prove2.me/theorems/1ba26a9e-8d0a-45b0-9847-f17c5b46f01c
-- title:
--   Marginal vector $\mu(p)$
-- statement:
--   The **marginal vector** of $p\in\Delta(\mathcal X)$ is $\mu(p)=\mathbb E_{X\sim p}[X]\in\mathbb R^d$, that is,
--   $$
--   \mu_i(p)=\sum_{x\in\mathcal X}p(x)\,x_i=\mathbb P_{X\sim p}[X_i=1],
--   $$
--   the probability that the random action selects item $i$.
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4

import Mathlib
import Definitions.Def_MSetBandit_ind

namespace MSetBandit

/-- **Marginal vector `µ(p) = E_{X∼p}[X]`.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4: "The i-th marginal
probability `µ_i(p)` satisfies `µ_i(p) = P_{X∼p}[X_i = 1]`". -/
def marg {d m : ℕ} (p : Action d m → ℝ) : Fin d → ℝ :=
  fun i => ∑ x, p x * ind x i

end MSetBandit


