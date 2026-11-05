-- Prove2me | Definitions.Def_DegenNRM_algorithm2
-- name    : DegenNRM_algorithm2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:42.799026+00:00
-- url     : https://prove2.me/theorems/5f2a07af-d9c2-48ad-9204-97b416a21ac9
-- title:
--   The estimator $\hat M_{c,a_{j_t}}$ of Algorithm 2
-- statement:
--   Let $s=T-t+1$ be the number of periods left, $j$ the type of the arriving query and $\hat q^*_{j,t}$ the type-$j$ entry of the optimal solution of (13) the algorithm obtained. With $\tau=2\kappa\sqrt{\log s/s}$:
--
--   1. if $\hat q^*_{j,t}\ge1-\tau$, then $\hat M=l_j$ (every reward is accepted);
--   2. else if $\hat q^*_{j,t}\le\tau$, then $\hat M=u_j+1$ (every reward is rejected);
--   3. else ($\tau\le\hat q^*_{j,t}\le1-\tau$), $\hat M=F_j^{-1}(1-\hat q^*_{j,t})$.
--
--   The two boundary branches are the "boundary-attracted" part of the policy: near $0$ and $1$ the fluid solution is rounded.
--
--   **Formalization Note** The branches are tested in the printed order, so when the first two conditions overlap the first wins. If neither of the first two holds, the third condition holds, so it is written as the final else. $\log$ is the natural logarithm, with $\log1=0$.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, Algorithm 2, p.15

import Mathlib
import Definitions.Def_DegenNRM_quantile

namespace DegenNRM

/-- **The estimator `M̂_{c, a_{j_t}}` of Algorithm 2** (Jiang, Ma & Zhang, arXiv:2210.07996v5,
Algorithm 2, p.15).

Let `s = T - t + 1` be the number of periods left, `κ` the constant of (15), `j` the type of the
arriving query and `qh = q̂*_{j,t}` the type-`j` entry of the optimal solution of (13) the
algorithm obtained. With `τ = 2κ √(log s / s)`:

1. if `q̂* ≥ 1 - τ`, then `M̂ = l_j` (accept every reward);
2. else if `q̂* ≤ τ`, then `M̂ = u_j + 1` (reject every reward);
3. else (`τ ≤ q̂* ≤ 1 - τ`), `M̂ = F_j⁻¹(1 - q̂*)`.

**Formalization Note.** The branches are tested in the printed order (if / else if / else if);
when the first two conditions overlap the first wins. If neither of the first two holds then
`τ < q̂* < 1 - τ`, so the third condition holds and is written as `else`. `log` is the natural
logarithm `Real.log`; at `s = 1` it is `0`, so `τ = 0`. -/
noncomputable def estimator {m n : ℕ} (inst : Instance m n) (κ s : ℝ) (j : Fin n) (qh : ℝ) : ℝ :=
  if 1 - 2 * κ * Real.sqrt (Real.log s / s) ≤ qh then inst.l j
  else if qh ≤ 2 * κ * Real.sqrt (Real.log s / s) then inst.u j + 1
  else quantile inst j (1 - qh)

end DegenNRM


