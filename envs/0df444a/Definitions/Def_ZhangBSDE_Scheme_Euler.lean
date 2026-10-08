-- Prove2me | Definitions.Def_ZhangBSDE_Scheme_Euler
-- name    : ZhangBSDE_Scheme_Euler
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:01:45.580984+00:00
-- url     : https://prove2.me/theorems/38ca1b9a-50c4-4924-9886-729fe59cbb4c
-- title:
--   (4.1)–(4.2), (6.1)–(6.2), pp. 476, 483 — the Euler scheme X^π and its step process X̂^π
-- statement:
--   Fix a partition $\pi:0=t_0<\dots<t_n=T$, $x\in\mathbb R^d$, coefficients $b,\sigma$ and a one-dimensional path family $W$.
--
--   1. **Grid values** ((6.1)–(6.2)). $X^\pi_{t_0}=x$ and, for $k=0,\dots,n-1$,
--   $$X^\pi_{t_{k+1}} = X^\pi_{t_k}+b(t_k,X^\pi_{t_k})\,\Delta t_{k+1}+\sigma(t_k,X^\pi_{t_k})\,(W_{t_{k+1}}-W_{t_k}).$$
--   2. **The Euler process** (4.1). $X^\pi_t = x+\int_0^t b(\pi(r),X^\pi_{\pi(r)})\,dr+\int_0^t\sigma(\pi(r),X^\pi_{\pi(r)})\,dW_r$ with $\pi(r)=t_{i-1}$ on $[t_{i-1},t_i)$. Its integrands are constant on each grid interval, so for $t\in[t_k,t_{k+1})$
--   $$X^\pi_t = X^\pi_{t_k}+b(t_k,X^\pi_{t_k})(t-t_k)+\sigma(t_k,X^\pi_{t_k})(W_t-W_{t_k}),$$
--   which is the form used, and $X^\pi_T = X^\pi_{t_n}$.
--   3. **The step process** (4.2). $\hat X^\pi_t = X^\pi_{\pi(t)} = X^\pi_{t_{i-1}}$ for $t\in[t_{i-1},t_i)$, and $\hat X^\pi_T = X^\pi_{t_n}$.
--
--   These are the forward approximations whose errors Lemma 4.1, Theorem 4.2 and Corollary 4.4 estimate, and $\Phi(\hat X^\pi)$ is the terminal value of the scheme in Theorem 6.1.
--
--   **Formalization Note** The processes are constructed pathwise from $W$, not quantified as solutions. The paper defines $\hat X^\pi$ on $[t_{i-1},t_i)$ only; the value at $T$ is the one (6.3) gives it ($x_n\mathbb 1_{\{T\}}$). (6.2) writes "$x\in\mathbb R$"; the state is in $\mathbb R^d$.
-- source:
--   Zhang (2004), Ann. Appl. Probab. 14, §4, p. 476, (4.1)–(4.2); §6, p. 483, (6.1)–(6.2)

import Mathlib
import Definitions.Def_ZhangBSDE_Scheme_Setting

namespace ZhangBSDE.Scheme

open MeasureTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {d : ℕ} {T : ℝ≥0}

/-- The Euler scheme on the grid, (6.1)–(6.2) (p. 483): `X^π_{t_0} = x` and
`X^π_{t_{k+1}} = X^π_{t_k} + b(t_k, X^π_{t_k}) Δt_{k+1} + σ(t_k, X^π_{t_k}) (W_{t_{k+1}} − W_{t_k})`.
For `k ≥ n` the increments vanish, so the value stays `X^π_{t_n}`. -/
noncomputable def eulerGrid (π : Partition T) (x : EuclideanSpace ℝ (Fin d))
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (W : ℝ≥0 → Ω → ℝ) : ℕ → Ω → EuclideanSpace ℝ (Fin d)
  | 0 => fun _ => x
  | k + 1 => fun ω =>
      eulerGrid π x b σ W k ω + π.Δt (k + 1) • b (π.tt k) (eulerGrid π x b σ W k ω)
        + (W (π.tt (k + 1)) ω - W (π.tt k) ω) • σ (π.tt k) (eulerGrid π x b σ W k ω)

/-- The Euler process `X^π` of (4.1) (p. 476):
`X^π_t = x + ∫₀ᵗ b(π(r), X^π_{π(r)}) dr + ∫₀ᵗ σ(π(r), X^π_{π(r)}) dW_r`, `π(r) = t_{i−1}` on
`[t_{i−1}, t_i)`. Its integrands are constant on each grid interval, so for `t ∈ [t_k, t_{k+1})`
it is `X^π_{t_k} + b(t_k, X^π_{t_k})(t − t_k) + σ(t_k, X^π_{t_k})(W_t − W_{t_k})`; this is the
explicit form used here (`k = gridIndex t`; at `t = T` it is `X^π_{t_n}`). -/
noncomputable def euler (π : Partition T) (x : EuclideanSpace ℝ (Fin d))
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  eulerGrid π x b σ W (π.gridIndex t) ω
    + ((t : ℝ) - π.tt (π.gridIndex t)) • b (π.tt (π.gridIndex t)) (eulerGrid π x b σ W (π.gridIndex t) ω)
    + (W t ω - W (π.tt (π.gridIndex t)) ω) • σ (π.tt (π.gridIndex t)) (eulerGrid π x b σ W (π.gridIndex t) ω)

/-- The step process `X̂^π_t ≜ X^π_{π(t)}` of (4.2) (p. 476): `X̂^π_t = X^π_{t_{i−1}}` for
`t ∈ [t_{i−1}, t_i)`, and `X̂^π_T = X^π_{t_n}` (the value (6.3) gives it, `x_n 𝟙_{T}`). -/
noncomputable def stepX (π : Partition T) (x : EuclideanSpace ℝ (Fin d))
    (b σ : ℝ≥0 → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : EuclideanSpace ℝ (Fin d) :=
  eulerGrid π x b σ W (π.gridIndex t) ω

end ZhangBSDE.Scheme


