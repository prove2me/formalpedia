-- Prove2me | Definitions.Def_L0BnB_Relax_VB
-- name    : L0BnB_Relax_VB
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:43:24.08275+00:00
-- url     : https://prove2.me/theorems/db0cd946-1bea-469c-b02f-fda7d6c79579
-- title:
--   $V_{B(M)}$: value of the interval relaxation of B(M)
-- statement:
--   $V_{B(M)}$ is the optimal objective of the interval relaxation of the Big-M formulation (2):
--
--   $$V_{B(M)}=\inf\Bigl\{\tfrac12\|y-X\beta\|_2^2+\lambda_0\sum_i z_i+\lambda_2\|\beta\|_2^2\ :\ z\in[0,1]^p,\ -Mz_i\le\beta_i\le Mz_i\ \forall i\Bigr\}.$$
--
--   It is the lower bound that a branch-and-bound method working on B$(M)$ obtains at its root node.
--
--   **Formalization Note** The optimal value is encoded as the infimum (`sInf`) of the objective values over the feasible set. The set contains $(\beta,z)=(0,0)$ and, for $\lambda_0,\lambda_2\ge0$, all values are nonnegative, so this infimum is not a junk value; for $M\ge0$ the feasible set is compact and the infimum is attained. $V_{B(M)}$ is deliberately not defined through the $\beta$-space form (37), which is a theorem of the mission.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, Proposition 1, p. 7 (definition of V_B(M)); eq. (2), p. 5; §2.2, p. 6

import Mathlib
import Definitions.Def_L0BnB_Relax_bigMFeasible
import Definitions.Def_L0BnB_Relax_bigMObj

namespace L0BnB.Relax

/-- **`V_B(M)`, the optimal value of the interval relaxation of B(M).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, Proposition 1, p. 7: "Let `V_B(M)` denote the optimal objective of the interval relaxation
of B(M)"; B(M) is (2), p. 5, and its interval relaxation replaces `zᵢ ∈ {0, 1}` by
`zᵢ ∈ [0, 1]` (§2.2, p. 6).

`VB X y lam0 lam2 M = inf { bigMObj X y lam0 lam2 β z | bigMFeasible M β z }`, the infimum over
`(β, z) ∈ ℝᵖ × ℝᵖ`.

**Formalization Note.** The optimal value is encoded as the infimum (`sInf`) of the objective
values over the feasible set (paper.md Reading 3, an `encoding`). The feasible set always contains
`(β, z) = (0, 0)` and, for `λ₀, λ₂ ≥ 0`, every objective value is `≥ 0`, so the set of values is
nonempty and bounded below and `sInf` is the true infimum, not a junk value (both checked in the
verification file). For `M ≥ 0` the feasible set is compact and the infimum is attained, so it is
the paper's minimum. `V_B(M)` is **not** defined through the β-space form (37); (37) is a
theorem of the mission. -/
noncomputable def VB {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 M : ℝ) : ℝ :=
  sInf {v | ∃ β z : Fin p → ℝ, bigMFeasible M β z ∧ bigMObj X y lam0 lam2 β z = v}

end L0BnB.Relax


