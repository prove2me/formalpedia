-- Prove2me | Definitions.Def_MSetBandit_uniform
-- name    : MSetBandit_uniform
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:38:45.395201+00:00
-- url     : https://prove2.me/theorems/b59d8768-ee14-48f4-9e05-38593f0e96ff
-- title:
--   Uniform distribution $U$ over the actions
-- statement:
--   The **uniform distribution** $U$ over $\mathcal X$ gives every action probability $U(x)=1/K$, $K=|\mathcal X|=\binom dm$. It is the initial sampling distribution of Algorithm 1 ($p_1=p_{\mathbf 0}=U$).
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 2, p.4; Algorithm 1, line 3, p.12

import Mathlib
import Definitions.Def_MSetBandit_Action

namespace MSetBandit

/-- **The uniform distribution `U` over the actions.** Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 2, p.4 ("the uniform
distribution `U` over `X`") and Algorithm 1, line 3, p.12. `U(x) = 1/K` with `K = |X|`. -/
noncomputable def uniform {d m : ℕ} : Action d m → ℝ :=
  fun _ => 1 / (Fintype.card (Action d m) : ℝ)

end MSetBandit


