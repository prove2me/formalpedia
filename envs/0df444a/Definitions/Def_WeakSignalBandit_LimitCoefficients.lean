-- Prove2me | Definitions.Def_WeakSignalBandit_LimitCoefficients
-- name    : WeakSignalBandit_LimitCoefficients
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:23.886149+00:00
-- url     : https://prove2.me/theorems/3b3f030e-e1a2-4d30-9f97-cba6bb592315
-- title:
--   Coefficients of the limit diffusion (3.1): drift $b=(\psi_k,\ \psi_k\mu_k)$ and diffusion matrix $a_{kk}=\psi_k\sigma_k^2$ on $I_S$
-- statement:
--   Let $z=(q,s)\in\mathbb R^K\times\mathbb R^K$, with $I_Q$ the coordinates of $q$ and $I_S$ those of $s$, let $\mu\in\mathbb R^K$, $\sigma\in\mathbb R^K$, and let $\psi$ be a limit sampling function on $D=[0,1]^K\times\mathbb R^K$. The limit diffusion (3.1),
--   $$dQ_{k,t}=\psi_k(Q_t,S_t)\,dt,\qquad dS_{k,t}=\mu_k\psi_k(Q_t,S_t)\,dt+\sigma_k\sqrt{\psi_k(Q_t,S_t)}\,dB_{k,t},$$
--   has drift and diffusion matrix
--   $$b_k(z)=\begin{cases}\psi_k(z),&k\in I_Q,\\ \psi_k(z)\mu_k,&k\in I_S,\end{cases}\qquad a_{k,l}(z)=\begin{cases}\psi_k(z)\sigma_k^2,&k=l\in I_S,\\ 0,&\text{otherwise},\end{cases}$$
--   where $a=\eta\eta^\top$ with $\eta_{k,k}=\sqrt{\psi_k}\,\sigma_k$ on $I_S$ (A.2).
--
--   Together with the generator and martingale problem of the path-space module, these coefficients define the solution law of (3.1) in Theorem 1.
--
--   **Formalization Note** $\psi$ is only given on $D$ (Definition 4), so the coefficients read $\psi$ at the projection of $z$ onto $D$ (each $q_k$ clamped into $[0,1]$); on $D$ they are the printed ones. A solution of (3.1) from $0$ has $Q_{k,t}=\int_0^t\psi_k\in[0,t]$, so it stays in $D$ for $t\le1$ and the values off $D$ never matter.
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (3.1) p.12; (A.1)–(A.2) p.31; (A.15)–(A.17) p.33

import Mathlib
import Definitions.Def_WeakSignalBandit_Experiment

namespace WeakSignalBandit

variable {K : ℕ}

/-- The projection of `ℝ^{2K}` onto `D = [0,1]^K × ℝ^K` that clamps each `q_k` into `[0,1]` and
leaves `s` unchanged. It is the identity on `D`. -/
noncomputable def clampD (z : State K) : State K :=
  mkState (fun k => max 0 (min 1 (z (Sum.inl k)))) (fun k => z (Sum.inr k))

/-- The drift `b` of the limit diffusion (3.1):
`b_k(z) = ψ_k(z)` for `k ∈ I_Q` and `b_k(z) = ψ_k(z) μ_k` for `k ∈ I_S`.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (3.1) p.12, (A.1) p.31, (A.15) p.33.

**Formalization Note** The limit sampling function `ψ` is only given on `D = [0,1]^K × ℝ^K`
(Definition 4), so the coefficients read `ψ` through `clampD`; on `D` they are the printed ones. A
solution of (3.1) from `0` has `Q_{k,t} = ∫_0^t ψ_k ∈ [0, t]`, so it never leaves `D` for `t ≤ 1`. -/
noncomputable def limitDrift (μ : Fin K → ℝ) (ψ : State K → Fin K → ℝ) (z : State K) :
    Fin K ⊕ Fin K → ℝ
  | Sum.inl k => ψ (clampD z) k
  | Sum.inr k => ψ (clampD z) k * μ k

/-- The diffusion matrix `a = ηηᵀ` of the limit diffusion (3.1):
`a_{k,l}(z) = ψ_k(z) σ_k²` if `k = l ∈ I_S`, and `0` otherwise
(with `η_{k,k}(z) = √ψ_k(z) σ_k` for `k ∈ I_S`, (A.2)).
Kuang, Wager, arXiv:2101.09855v7, (3.1) p.12, (A.2) p.31, (A.16)–(A.17) p.33.

**Formalization Note** `ψ` is read through `clampD`, as in `limitDrift`. -/
noncomputable def limitDiff (σ : Fin K → ℝ) (ψ : State K → Fin K → ℝ) (z : State K) :
    Fin K ⊕ Fin K → Fin K ⊕ Fin K → ℝ
  | Sum.inr k, Sum.inr l => if k = l then ψ (clampD z) k * σ k ^ 2 else 0
  | _, _ => 0

end WeakSignalBandit


