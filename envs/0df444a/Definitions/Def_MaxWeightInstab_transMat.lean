-- Prove2me | Definitions.Def_MaxWeightInstab_transMat
-- name    : MaxWeightInstab_transMat
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:22.794014+00:00
-- url     : https://prove2.me/theorems/6e9879a6-52f0-4294-bc7a-6bfd92faf26a
-- title:
--   Transition matrix of the MaxWeight queueing process
-- statement:
--   The transition matrix $P(x,y)=\mathbb P[Q(t+1)=y\mid Q(t)=x]$ of the queueing network process of Figure 1 under the MaxWeight tie rule $\pi$, as a real matrix on the countable state space $\mathbb Z_+^{2J+2}$. Recurrence and transience are those of the published countable-chain definitions (`MatrixAnalytic_Stability_Chain`).
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, p.1 and p.5

import Mathlib
import Definitions.Def_MaxWeightInstab_kernel

namespace MaxWeightInstab

/-- The transition matrix `P(x, y) = P[Q(t+1) = y | Q(t) = x]` of the queueing network process of
Figure 1 under the MaxWeight tie rule `π` (Bramson, D'Auria & Walton, *Stability and Instability of the MaxWeight Policy*, arXiv:1909.10825v2, p.1: "The queueing network process is a discrete
time countable state space Markov chain"), as a real matrix on the countable state space
`ℤ₊^{2J+2}`, the form used by `MatrixAnalytic.Stability`. -/
noncomputable def transMat {J : ℕ} (a : ℝ) (π : State J → PMF (State J)) (x y : State J) : ℝ :=
  (kernel a π x y).toReal

end MaxWeightInstab


