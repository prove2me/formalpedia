-- Prove2me | Definitions.Def_FirstPriceLearning_NonIID_HardInstance
-- name    : FirstPriceLearning_NonIID_HardInstance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:16.639436+00:00
-- url     : https://prove2.me/theorems/d3526cf0-7d7e-45f9-a0dd-f659453a7979
-- title:
--   Proof of Theorem 8, p. 34 — thresholds $f(u)=\tfrac12+\tfrac14\sum_t u_t/2^t$ and values $v_1=\tfrac12$, $v_{t+1}=v_t+u_t/2^{t+2}$
-- statement:
--   The hard instance in the proof of Theorem 8 of Han, Zhou and Weissman (p. 34) is indexed by a sign vector $u=(u_1,\dots,u_T)\in\{\pm1\}^T$.
--
--   The threshold is
--   $$
--   f(u_1,\dots,u_T)=\frac12+\frac14\sum_{t=1}^T\frac{u_t}{2^t},
--   $$
--   and the private values are defined recursively by
--   $$
--   v_1=\frac12,\qquad v_{t+1}=v_t+\frac{u_t}{2^{t+2}}\quad(t\ge1).
--   $$
--   The value $v_t$ depends only on $u_1,\dots,u_{t-1}$, while its position relative to $v^\star=f(u)$ is decided by $u_t$; this is what hides the threshold from any bidder.
--
--   **Formalization Note** Rounds are `Fin T` (Lean $t$ = paper $t+1$). $f$ and $v$ are defined for any real vector $u$; the theorems that use them assume $u_t\in\{\pm1\}$. A Boolean $\sigma_t$ encodes the sign $u_t=+1$ (true) or $-1$ (false) where a finite sum over all sign vectors is needed.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 34, proof of Theorem 8 (definitions of f and of (v_t))

import Mathlib

namespace FirstPriceLearning.NonIID

/-- A sign `±1` encoded by a Boolean: `true ↦ 1`, `false ↦ −1`. -/
def pm (b : Bool) : ℝ := if b then 1 else -1

/-- The threshold candidates of the proof of Theorem 8 (arXiv:2003.09795v7, p. 34):
`f(u_1, …, u_T) = 1/2 + (1/4) ∑_{t=1}^T u_t / 2^t`. Round `t : Fin T` is the paper's `t.val + 1`. -/
noncomputable def fval {T : ℕ} (u : Fin T → ℝ) : ℝ :=
  1 / 2 + 1 / 4 * ∑ t : Fin T, u t / 2 ^ (t.val + 1)

/-- Auxiliary recursion on `ℕ` for the value sequence: index `n` is the paper's round `n + 1`;
`v_1 = 1/2` and `v_{t+1} = v_t + u_t / 2^{t+2}` (p. 34). Signs `u_t` past the horizon are never used
by `valueSeq`; they read as `0`. -/
noncomputable def valueAux {T : ℕ} (u : Fin T → ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | n + 1 => valueAux u n + (if h : n < T then u ⟨n, h⟩ else 0) / 2 ^ (n + 3)

/-- The private values of the proof of Theorem 8 (p. 34): `v_1 = 1/2` and
`v_{t+1} = v_t + u_t / 2^{t+2}` for `t ≥ 1`; `valueSeq u t` is the paper's `v_{t.val + 1}`. -/
noncomputable def valueSeq {T : ℕ} (u : Fin T → ℝ) (t : Fin T) : ℝ :=
  valueAux u t.val

end FirstPriceLearning.NonIID


