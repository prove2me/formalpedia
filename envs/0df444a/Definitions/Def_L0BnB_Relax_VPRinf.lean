-- Prove2me | Definitions.Def_L0BnB_Relax_VPRinf
-- name    : L0BnB_Relax_VPRinf
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:44:46.372189+00:00
-- url     : https://prove2.me/theorems/a2c8273f-0e6b-4c29-add6-5aa46419c9d9
-- title:
--   $V_{PR(\infty)}$: value of the interval relaxation of PR(∞)
-- statement:
--   $V_{PR(\infty)}$ is the optimal value of the interval relaxation of the perspective formulation without Big-M constraints:
--
--   $$V_{PR(\infty)}=\inf\Bigl\{\tfrac12\|y-X\beta\|_2^2+\lambda_0\sum_i z_i+\lambda_2\sum_i s_i\ :\ z\in[0,1]^p,\ s\ge0,\ \beta_i^2\le s_iz_i\ \forall i\Bigr\}.$$
--
--   It is always a valid lower bound for problem (1), independent of any Big-M parameter.
--
--   **Formalization Note** Encoded as the infimum (`sInf`) of the objective values over the feasible set, which contains $(0,0,0)$; for $\lambda_0,\lambda_2\ge0$ all values are nonnegative. $V_{PR(\infty)}$ is deliberately not defined as $\min_\beta G(\beta)$; that identity, (6), is a theorem of the mission.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, eq. (3) and the M = ∞ remark, p. 5; §2.2 and eq. (6), pp. 6–7

import Mathlib
import Definitions.Def_L0BnB_Relax_prFeasible
import Definitions.Def_L0BnB_Relax_prObj

namespace L0BnB.Relax

/-- **`V_PR(∞)`, the optimal value of the interval relaxation of PR(∞).**
Hazimeh, Mazumder, Saab, *Sparse Regression at Scale: Branch-and-Bound rooted in First-Order
Optimization*, arXiv:2004.06152v2, pp. 5–7: PR(M) is (3), p. 5; PR(∞) drops the Big-M constraints (p. 5); the interval
relaxation relaxes `zᵢ` to `[0, 1]` (§2.2, p. 6); `V_PR(∞)` is the optimal value of that
relaxation (p. 6, "[21] has shown that the interval relaxation of PR(∞) can be written as:
V_PR(∞) = …").

`VPRinf X y lam0 lam2 = inf { prObj X y lam0 lam2 β z s | prFeasible β z s }`, the infimum
over `(β, z, s) ∈ ℝᵖ × ℝᵖ × ℝᵖ`.

**Formalization Note.** The optimal value is the infimum (`sInf`) of the objective values
(paper.md Reading 3). The feasible set contains `(0, 0, 0)` and, for `λ₀, λ₂ ≥ 0`, all values are
`≥ 0`, so the set is nonempty and bounded below (checked in the verification file); the infimum
is attained (milestone (6)). `V_PR(∞)` is **not** defined as `min_β G(β)`; that identity, (6), is
a theorem of the mission. -/
noncomputable def VPRinf {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ)
    (lam0 lam2 : ℝ) : ℝ :=
  sInf {v | ∃ β z s : Fin p → ℝ, prFeasible β z s ∧ prObj X y lam0 lam2 β z s = v}

end L0BnB.Relax


