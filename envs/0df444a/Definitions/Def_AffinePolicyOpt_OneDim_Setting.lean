-- Prove2me | Definitions.Def_AffinePolicyOpt_OneDim_Setting
-- name    : AffinePolicyOpt_OneDim_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:48:30.55691+00:00
-- url     : https://prove2.me/theorems/f3421127-0f0b-49ea-8d0d-8a6b22a2280c
-- title:
--   Problem 1.1 and §2, pp. 1–5 — the one-dimensional min-max control model (DP), its Bellman functions g_k, J*_k, and affine policies/costs (10)–(11)
-- statement:
--   This file fixes the objects of the one-dimensional constrained min-max control problem of Bertsimas, Iancu and Parrilo, in the reduced form (DP) of §2 (the dynamics coefficients normalised to $\alpha_k=\beta_k=\gamma_k=1$, which the paper notes is without loss of generality).
--
--   1. **Model.** A horizon $T$, an initial state $x_1\in\mathbb R$, and for every stage $k=1,\dots,T$: a per-unit control cost $c_k$, control bounds $L_k, U_k$, disturbance bounds $\underline w_k,\overline w_k$, and a state cost $h_k:\mathbb R\to\mathbb R$. The state evolves as $x_{k+1}=x_k+u_k+w_k$ with $u_k\in[L_k,U_k]$ and $w_k\in\mathcal W_k=[\underline w_k,\overline w_k]$.
--   2. **Standing hypotheses.** $c_k\ge 0$; each $h_k$ is convex and coercive ($h_k(x)\to+\infty$ as $|x|\to\infty$); and $L_k\le U_k$, $\underline w_k\le\overline w_k$.
--   3. **Bellman functions.** With $J^*_{T+1}\equiv 0$, for $k=T,\dots,1$,
--   $$g_k(y)=\max_{w\in\mathcal W_k}\big[h_k(y+w)+J^*_{k+1}(y+w)\big],\qquad J^*_k(x)=\min_{L_k\le u\le U_k}\big[c_k u+g_k(x+u)\big].$$
--   4. **Min-max value.** $J_{mM}=J^*_1(x_1)$.
--   5. **Affine policies and costs.** For coefficient arrays $q_{k,0},q_{k,t}$ and $z_{k,0},z_{k,t}$, a disturbance sequence $w=(w_1,\dots,w_T)$ and a stage $k$,
--   $$q_k(w)=q_{k,0}+\sum_{t=1}^{k-1}q_{k,t}w_t,\qquad z_k(w)=z_{k,0}+\sum_{t=1}^{k}z_{k,t}w_t,$$
--   and the state reached after stage $k$ under these policies is $x_1+\sum_{t=1}^{k}\big(q_t(w)+w_t\big)$. The policy $q_k$ reads only $w_1,\dots,w_{k-1}$ and the cost $z_k$ only $w_1,\dots,w_k$ (non-anticipativity). A sequence $w$ is admissible when $w_t\in\mathcal W_t$ for all $t$.
--
--   These are the objects of Theorem 3.1 and of the dynamic-programming facts (Lemma 7.1) on which the paper's induction rests.
--
--   **Formalization Note** Stages are 0-based: Lean's `k : Fin T` is the paper's stage $k+1$, and `Jstar M j` is the paper's $J^*_{j+1}$ (so `Jstar M T` is $J^*_{T+1}=0$; its value for $j>T$ is the unused $0$). `gFun` and `bellman` are written with `sSup`/`sInf` over the image of a nonempty compact interval; under the standing hypotheses the integrands are continuous (convex functions on $\mathbb R$ are continuous, and $J^*_{k+1}$ is convex by Lemma 7.1), so these are attained maxima and minima, not junk values. The nested expression (4) of Problem 1.1, unrolled, is exactly this Bellman recursion evaluated at $x_1$, because each inner bracket depends on the history only through the current state; (4) is not formalized separately. The hypotheses $L_k\le U_k$ and $\underline w_k\le\overline w_k$ are added: the page writes both as intervals but never says they are nonempty.
-- source:
--   Bertsimas, Iancu & Parrilo, Optimality of Affine Policies in Multi-stage Robust Optimization, arXiv:0904.3986v1, pp. 1–5, Problem 1.1, (DP), Bellman recursion p. 4 and (7), (10)–(11)

import Mathlib

namespace AffinePolicyOpt.OneDim

/-- The data of the one-dimensional min-max control problem (DP) of §2 (Problem 1.1 with
`α_k = β_k = γ_k = 1`), over the horizon `T`. Time is 0-based: Lean stage `k : Fin T` is the
paper's stage `k + 1`.
* `x1` : the initial state `x_1`;
* `c k` : the per-unit control cost `c_k`;
* `L k`, `U k` : the control bounds, `u_k ∈ [L_k, U_k]`;
* `wlo k`, `whi k` : the disturbance bounds, `w_k ∈ 𝒲_k = [w̲_k, w̄_k]`;
* `h k` : the state cost `h_k`, charged on `x_{k+1}`. -/
structure Model (T : ℕ) where
  x1 : ℝ
  c : Fin T → ℝ
  L : Fin T → ℝ
  U : Fin T → ℝ
  wlo : Fin T → ℝ
  whi : Fin T → ℝ
  h : Fin T → ℝ → ℝ

variable {T : ℕ}

/-- The standing hypotheses of Problem 1.1: `c_k ≥ 0`, `h_k` convex and coercive; plus the
nonemptiness of the control interval `[L_k, U_k]` and of the disturbance interval `[w̲_k, w̄_k]`
(disclosed additions: the page writes both as intervals). -/
structure Model.Standing (M : Model T) : Prop where
  c_nonneg : ∀ k, 0 ≤ M.c k
  L_le_U : ∀ k, M.L k ≤ M.U k
  wlo_le_whi : ∀ k, M.wlo k ≤ M.whi k
  h_convex : ∀ k, ConvexOn ℝ Set.univ (M.h k)
  h_coercive : ∀ k, Filter.Tendsto (M.h k) (Filter.cocompact ℝ) Filter.atTop

/-- `g_k` of (7): `g_k(y) = max_{w ∈ 𝒲_k} [h_k(y + w) + J'(y + w)]`, where `J'` is the next
stage's value function `J*_{k+1}`. -/
noncomputable def gFun (M : Model T) (k : Fin T) (J' : ℝ → ℝ) (y : ℝ) : ℝ :=
  sSup ((fun w => M.h k (y + w) + J' (y + w)) '' Set.Icc (M.wlo k) (M.whi k))

/-- One step of the Bellman recursion (p. 4):
`x ↦ min_{L_k ≤ u ≤ U_k} [c_k u + g_k(x + u)]`, with `g_k` built from `J'`. -/
noncomputable def bellman (M : Model T) (k : Fin T) (J' : ℝ → ℝ) (x : ℝ) : ℝ :=
  sInf ((fun u => M.c k * u + gFun M k J' (x + u)) '' Set.Icc (M.L k) (M.U k))

/-- The optimal value functions of the Bellman recursion: `Jstar M j` is the paper's
`J*_{j+1}`. For `j < T` it is one Bellman step applied to `Jstar M (j + 1)`;
`Jstar M T = 0` is `J*_{T+1} ≡ 0` (and the value `0` for `j > T` is never used). -/
noncomputable def Jstar (M : Model T) (j : ℕ) : ℝ → ℝ :=
  if h : j < T then bellman M ⟨j, h⟩ (Jstar M (j + 1)) else fun _ => 0
termination_by T - j

/-- The min-max value `J_mM = J*_1(x_1)` of (4), computed by dynamic programming. -/
noncomputable def JmM (M : Model T) : ℝ :=
  Jstar M 0 M.x1

/-- A full disturbance sequence `w` lies in the box `𝒲_1 × ⋯ × 𝒲_T`. -/
def Model.inBox (M : Model T) (w : Fin T → ℝ) : Prop :=
  ∀ t, w t ∈ Set.Icc (M.wlo t) (M.whi t)

/-- The affine control policy (10): `q_k(w) = q_{k,0} + Σ_{t < k} q_{k,t} w_t`. It reads only
the disturbances strictly before stage `k`. -/
def qEval (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (k : Fin T) (w : Fin T → ℝ) : ℝ :=
  q0 k + ∑ t ∈ Finset.univ.filter (· < k), q k t * w t

/-- The affine running cost (11): `z_k(w) = z_{k,0} + Σ_{t ≤ k} z_{k,t} w_t`. It reads the
disturbances up to and including stage `k`. -/
def zEval (z0 : Fin T → ℝ) (z : Fin T → Fin T → ℝ) (k : Fin T) (w : Fin T → ℝ) : ℝ :=
  z0 k + ∑ t ∈ Finset.univ.filter (· ≤ k), z k t * w t

/-- The state reached after stage `k` under the affine policies:
`x_1 + Σ_{t ≤ k} (q_t(w) + w_t)`, the paper's `x_{k+1}` in (13)–(14). -/
def Model.xAff (M : Model T) (q0 : Fin T → ℝ) (q : Fin T → Fin T → ℝ) (k : Fin T)
    (w : Fin T → ℝ) : ℝ :=
  M.x1 + ∑ t ∈ Finset.univ.filter (· ≤ k), (qEval q0 q t w + w t)

end AffinePolicyOpt.OneDim


