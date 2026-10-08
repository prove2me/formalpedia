-- Prove2me | Definitions.Def_BSUMM_Rand_RBSUMM
-- name    : BSUMM_Rand_RBSUMM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:32:15.968685+00:00
-- url     : https://prove2.me/theorems/505e6748-2abb-497f-a437-2a937f1a2200
-- title:
--   The randomized BSUM-M (1.13): paths, the block steps (2.5), the dual step (2.6), the one-step conditional average and i.i.d. update indices
-- statement:
--   The randomized block successive upper-bound minimization method of multipliers (RBSUM-M) selects a probability vector $(p_0,\dots,p_K)$ with $p_k>0$ and $\sum_{k=0}^K p_k=1$. At each iteration $t\ge1$ it picks an index $k\in\{0,\dots,K\}$ with probability $p_k$ and
--
--   $$\begin{cases} y^{t+1}=y^t+\alpha^t(q-Ex^t),\quad x^{t+1}=x^t, & k=0,\\[2pt] x^{t+1}_k=\arg\min_{x_k\in X_k} u_k(x_k;x^t)-\langle y^t,E_kx_k\rangle+h_k(x_k),\quad x^{t+1}_j=x^t_j\ (j\ne k),\quad y^{t+1}=y^t, & k\ge1,\end{cases}\tag{1.13}$$
--
--   with dual stepsizes $\alpha^t>0$. This file defines:
--
--   1. **RBSUM-M paths**: sequences $(x^t,y^t)$ obeying (1.13) for a given sequence of indices, for every $t\ge1$.
--   2. **The block steps** (2.5) from a state $(x,y)$: $\hat x_k=\arg\min_{x_k\in X_k}u_k(x_k;x)+\langle y,q-E_kx_k\rangle+h_k(x_k)$ for every $k$, and **the dual step** (2.6) $\hat y=y+a(q-Ex)$.
--   3. **The one-step conditional average** of a function $F$ of the state:
--
--   $$\mathbb E[F(z^{t+1})\mid z^t]=p_0\,F(x,\hat y)+\sum_{k=1}^K p_k\,F\big((\hat x_k,x_{-k}),y\big),\qquad z^t=(x,y),$$
--
--   with $a=\alpha^t$ and $\hat x=\hat x^{t+1}$.
--   4. **The bound (2.13)** with constants $\hat\sigma_1,\hat\sigma_2$: at every state $x\in X$, $y$ and $a>0$, $\|\tilde\nabla L(x;\hat y)\|\le\hat\sigma_1\|\hat x-x\|+\hat\sigma_2\|\hat y-y\|$.
--   5. **The random index process**: measurable, mutually independent indices $\iota_t$ with $\mathbb P(\iota_t=k)=p_k$.
--
--   These are the objects in which Lemmas 2.3–2.6 and Theorem 2.1(2) are stated.
--
--   **Formalization Note** Index $0$ of `Fin (K+1)` is the dual update and `Fin.succ k` is primal block $k$. The argmin steps are stated as minimality predicates (the minimizers are unique by strong convexity). The one-step average equals $\mathbb E[F(z^{t+1})\mid z^t]$ because the index drawn at iteration $t$ is independent of $z^t$ (a function of the earlier indices) and has law $p$; the lemmas are stated for this average at every state, which covers every iterate.
-- source:
--   Hong, Chang, Wang, Razaviyayn, Ma, Luo, arXiv:1401.7079v1, pp. 6, 10–11, (1.13), (2.5), (2.6), (2.13)

import Mathlib
import Definitions.Def_BSUMM_Rand_Setting

open scoped RealInnerProductSpace
open MeasureTheory

namespace BSUMM.Rand

namespace Setting

variable (S : Setting)

/-- `{p_k}_{k=0}^K` is a probability vector with `p_k > 0` (1.13). Index `0` is the dual
update, index `Fin.succ k` the primal block `k`. -/
def IsProbVec (p : Fin (S.K + 1) → ℝ) : Prop := (∀ k, 0 < p k) ∧ ∑ k, p k = 1

/-- The dual step `ŷ = y + a (q - Ex)` of (2.6) (and of the `k = 0` branch of (1.13)). -/
noncomputable def dualStep (x : S.Xsp) (y : S.Ysp) (a : ℝ) : S.Ysp := y + a • (S.q - S.Emap x)

/-- One RBSUM-M path (1.13) for the index sequence `κ` (`κ t = 0`: dual update;
`κ t = Fin.succ k`: update of primal block `k`), stepsizes `α`, primal iterates `x` and dual
iterates `y`, for every iteration `t ≥ 1`. The block step is the minimality of
`u_k(·; x^t) - ⟨y^t, E_k ·⟩ + h_k` over `X_k`. -/
def IsRBSUMMPath (u : S.UFun) (α : ℕ → ℝ) (κ : ℕ → Fin (S.K + 1)) (x : ℕ → S.Xsp)
    (y : ℕ → S.Ysp) : Prop :=
  ∀ t : ℕ, 1 ≤ t →
    (κ t = 0 → y (t + 1) = S.dualStep (x t) (y t) (α t) ∧ x (t + 1) = x t) ∧
    (∀ k : Fin S.K, κ t = k.succ →
      x (t + 1) k ∈ S.Xk k ∧
      (∀ v ∈ S.Xk k,
        u k (x (t + 1) k) (x t) - ⟪y t, S.E k (x (t + 1) k)⟫ + S.h k (x (t + 1) k) ≤
          u k v (x t) - ⟪y t, S.E k v⟫ + S.h k v) ∧
      (∀ j : Fin S.K, j ≠ k → x (t + 1) j = x t j) ∧
      y (t + 1) = y t)

/-- `x̂` is the vector of all block steps (2.5) from the state `(x, y)`:
`x̂_k = argmin_{v ∈ X_k} u_k(v; x) + ⟨y, q - E_k v⟩ + h_k(v)` for every `k`. -/
def IsHatStep (u : S.UFun) (x : S.Xsp) (y : S.Ysp) (xhat : S.Xsp) : Prop :=
  ∀ k : Fin S.K, xhat k ∈ S.Xk k ∧
    ∀ v ∈ S.Xk k,
      u k (xhat k) x + ⟪y, S.q - S.E k (xhat k)⟫ + S.h k (xhat k) ≤
        u k v x + ⟪y, S.q - S.E k v⟫ + S.h k v

/-- The one-step average of `F` over the random index of (1.13) from the state `z = (x, y)` with
stepsize `a` and block steps `x̂`:
`p_0 F(x, ŷ) + ∑_k p_k F(x[k ↦ x̂_k], y)`, `ŷ = y + a(q - Ex)`.
Since the index drawn at iteration `t` is independent of `z^t` and has law `p`, this is
`E[F(z^{t+1}) | z^t]` when `(x, y) = z^t`, `a = α^t` and `x̂ = x̂^{t+1}`. -/
noncomputable def condAvg (p : Fin (S.K + 1) → ℝ) (F : S.Xsp → S.Ysp → ℝ) (x : S.Xsp)
    (y : S.Ysp) (a : ℝ) (xhat : S.Xsp) : ℝ :=
  p 0 * F x (S.dualStep x y a) + ∑ k : Fin S.K, p k.succ * F (S.upd x k (xhat k)) y

/-- The bound (2.13) of Lemma 2.4(2) with constants `σ̂₁, σ̂₂`: at every state `x ∈ X`, `y`,
stepsize `a > 0`, with `x̂` the block steps (2.5) and `ŷ = y + a(q - Ex)`,
`‖∇̃L(x; ŷ)‖ ≤ σ̂₁ ‖x̂ - x‖ + σ̂₂ ‖ŷ - y‖`. -/
def ProxGradBound (u : S.UFun) (σ1 σ2 : ℝ) : Prop :=
  ∀ x ∈ S.Xset, ∀ (y : S.Ysp) (a : ℝ) (xhat : S.Xsp), 0 < a → S.IsHatStep u x y xhat →
    ∀ pp : S.Xsp, S.IsProxPt (x - S.gL x (S.dualStep x y a)) pp →
      ‖x - pp‖ ≤ σ1 * ‖xhat - x‖ + σ2 * ‖S.dualStep x y a - y‖

/-- The random indices of RBSUM-M: `ι t` is the index picked at iteration `t`; the `ι t` are
measurable, mutually independent, and each has law `p` (`P(ι_t = k) = p_k`). -/
def IsIIDIndexProcess {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (p : Fin (S.K + 1) → ℝ)
    (ι : ℕ → Ω → Fin (S.K + 1)) : Prop :=
  (∀ t, Measurable (ι t)) ∧ ProbabilityTheory.iIndepFun ι P ∧
    ∀ t k, P (ι t ⁻¹' {k}) = ENNReal.ofReal (p k)

end Setting

end BSUMM.Rand


