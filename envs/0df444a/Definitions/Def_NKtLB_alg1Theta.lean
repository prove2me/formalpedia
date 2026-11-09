-- Prove2me | Definitions.Def_NKtLB_alg1Theta
-- name    : NKtLB_alg1Theta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:01:11.446621+00:00
-- url     : https://prove2.me/theorems/b8ce6986-28a5-47f2-9c6b-ea633dc14c80
-- title:
--   The thresholds $\theta_i$ of Algorithm 1
-- statement:
--   $\theta_i=\gamma N_i$, the lower bound on $\mathrm{nKt}(s_i)$ that membership $s_i\in L\subseteq R_{\mathrm{nKt}}[\gamma n]$ guarantees. Algorithm 1 stops at the first $i$ with $\theta_i>n/(2-2\gamma')$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75, lines 2, 11, 19

import Mathlib
import Definitions.Def_NKtLB_alg1N

namespace NKtLB

/-- **The thresholds `θ_i = γ N_i` of Algorithm 1** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Algorithm 1, p.75, lines 2 and 11). -/
noncomputable def alg1Theta (γ : ℝ) (n i : ℕ) : ℝ := γ * alg1N γ n i

end NKtLB


