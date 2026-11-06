-- Prove2me | Definitions.Def_RandomLPIPM_pgdIter
-- name    : RandomLPIPM_pgdIter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:07:52.108133+00:00
-- url     : https://prove2.me/theorems/ff658606-716c-45b5-8ff9-01ea4b0f7c23
-- title:
--   Projected gradient descent iterates $u_k$ on $\Phi_{x,\mu}$ (Lemma 9.5)
-- statement:
--   The projected gradient descent on $\Phi=\Phi_{x,\mu}$ over $\ker(AX)$ with step $1/2$ is
--   $$u_0=0,\qquad u_{k+1}=u_k-\tfrac12\,P_x\nabla\Phi_{x,\mu}(u_k),\qquad k\ge0 .$$
--   These are the iterates of Lemma 9.5 and of the inner loop of Algorithm 1.
-- source:
--   Dadush–Jiang–Kyng–Ma, Interior Point Methods Solve Random LPs in polylog(n) iterations, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 9.5, p.79; §9.2, p.78

import Mathlib
import Definitions.Def_RandomLPIPM_Px
import Definitions.Def_RandomLPIPM_gradPhi

open Matrix

namespace RandomLPIPM

/-- **Projected gradient descent on `Φ_{x,μ}` (Lemma 9.5).** Dadush–Jiang–Kyng–Ma, *Interior Point Methods Solve Random LPs in polylog(n) iterations*, STOC 2027 submission (manuscript sha256 a8a320f9…), Lemma 9.5, p.79: "`Δuₖ = −P∇Φ(uₖ)`
be the projected gradient descent direction at `uₖ` and `uₖ₊₁ = uₖ + Δuₖ/2` for `k ≥ 0` ... starting
from `u₀ := 0`". `pgdIter A c x μ k` is `uₖ`, with `P = P_x` (§9.2, p.78: `P := P_x`, `Φ := Φ_{x,μ}`). -/
noncomputable def pgdIter {d n : ℕ} (A : Matrix (Fin d) (Fin n) ℝ) (c x : Fin n → ℝ) (μ : ℝ) :
    ℕ → Fin n → ℝ
  | 0 => 0
  | k + 1 => pgdIter A c x μ k - (1 / 2 : ℝ) • (Px A x *ᵥ gradPhi c x μ (pgdIter A c x μ k))

end RandomLPIPM


