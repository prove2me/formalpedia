-- Prove2me | Definitions.Def_QuantileMDP_Model
-- name    : QuantileMDP_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:41:23.247998+00:00
-- url     : https://prove2.me/theorems/7f30e319-2147-452c-9821-456d8cc09e3b
-- title:
--   Finite-horizon non-stationary MDP, history-dependent policies and the law of the cumulative reward
-- statement:
--   A **model** on a state set $\mathcal S$ and an action set $\mathcal A$ consists of
--
--   1. transition laws $P_t(\cdot\mid s,a)$ on $\mathcal S$, for every time $t\in\mathbb N$, state $s$ and action $a$;
--   2. rewards $r_t(s,a,s')\in\mathbb R$, depending on the current state, the action and the next state;
--   3. admissible action sets $\mathcal A_t(s)\subseteq\mathcal A$, each nonempty.
--
--   A **policy** $\pi=(\mu_0,\mu_1,\dots)$ is deterministic and history dependent: $\mu_t$ maps the state history $(S_0,\dots,S_t)$ to an action. It is **admissible** if $\mu_t(S_0,\dots,S_t)\in\mathcal A_t(S_t)$ for every $t$ and every history. The **shifted model** $M^{(t)}$ is the model whose time $k$ is time $t+k$ of $M$; the **tail** of $\pi$ after the first state $s$ is the policy $k\mapsto\mu_{k+1}(s,\cdot)$.
--
--   For a horizon $T$, a start state $s$ and a policy $\pi$, a state path $h=(h_0,\dots,h_T)$ with $h_0=s$ has probability $\prod_{t=0}^{T-1}P_t\bigl(h_{t+1}\mid h_t,\mu_t(h_0,\dots,h_t)\bigr)$ and reward $\sum_{t=0}^{T-1}r_t\bigl(h_t,\mu_t(h_0,\dots,h_t),h_{t+1}\bigr)$. The **law of the cumulative reward** is
--
--   $$
--   \mathcal L^\pi_{T}(s)=\sum_{h:\,h_0=s}\ \mathbb P^\pi(h)\,\delta_{\mathrm{reward}(h)},
--   $$
--
--   the distribution of $\sum_{k=0}^{T-1}r_k(S_k,a_k,w_k)$ given $S_0=s$, the random variable whose quantile the QMDP (3) maximizes.
--
--   **Formalization Note** The paper's system $S_{t+1}=f_t(S_t,a_t,w_t)$ with finitely supported noise $w_t$ and the weak inverse $l_t$ of Assumption 1(c) induces exactly the kernels $P_t$ and the rewards $r_t(s,a,l_t(s,a,s'))$; conversely every kernel model is one, with $W=\mathcal S$, $f_t(s,a,w)=w$ and $l_t(s,a,s')=s'$. Finiteness of $\mathcal S$ and $\mathcal A$ (Assumption 1(a)) is imposed by the theorems. The admissible set may depend on the state; the paper's $\mathcal A_t$ is the case $\mathcal A_t(s)=\mathcal A_t$. For deterministic policies the past actions are functions of the past states, so state histories carry the information of the paper's $H_t=(S_0,a_0,\dots,S_t)$. The terminal reward is $0$, as the paper assumes without loss of generality (p.8). The law is a finite sum of Dirac masses over the paths $(s,g_1,\dots,g_T)$.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §2 (1), pp.7–8; Assumption 1, p.8; p.9; (3), p.9

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace QuantileMDP

/-- A finite-horizon, non-stationary Markov decision process in kernel form: transition laws
`P t s a = P_t(· | s, a)`, rewards `r t s a s' = r_t(s, a, l_t(s, a, s'))` and admissible action
sets `adm t s`, each nonempty.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §2 (1), pp.7–8;
Assumption 1, p.8; p.9.

**Formalization Note** The paper's system `S_{t+1} = f_t(S_t, a_t, w_t)` with finitely supported
`w_t` and an inverse `l_t` (Assumption 1(b),(c)) induces exactly the kernel `P_t(· | s, a)` and the
reward `r_t(s, a, s')` as a function of the next state; conversely every kernel model is one
(`W = S`, `f_t(s,a,w) = w`, `l_t(s,a,s') = s'`). Finiteness of `S` and `A` (Assumption 1(a)) is
imposed by the theorems as `Fintype` instances. The admissible set may depend on the state (the
paper's `A_t` is the case `adm t s = A_t`). The terminal reward is `0` ("without loss of
generality", p.8). -/
structure Model (S A : Type*) where
  /-- transition law `P_t(· | s, a)` -/
  P : ℕ → S → A → PMF S
  /-- reward `r_t(s, a, s')` -/
  r : ℕ → S → A → S → ℝ
  /-- admissible actions at time `t` in state `s` -/
  adm : ℕ → S → Set A
  adm_nonempty : ∀ t s, (adm t s).Nonempty

variable {S A : Type*}

/-- The model started at time `t`: time `k` of `M.shift t` is time `t + k` of `M`. -/
def Model.shift (M : Model S A) (t : ℕ) : Model S A where
  P k := M.P (t + k)
  r k := M.r (t + k)
  adm k := M.adm (t + k)
  adm_nonempty k := M.adm_nonempty (t + k)

/-- A deterministic history-dependent policy: at time `t` it maps the state history
`(S_0, …, S_t)` to an action.

**Formalization Note** The paper's `μ_t` sees `H_t = (S_0, a_0, …, S_{t-1}, a_{t-1}, S_t)`; for a
deterministic policy the past actions are functions of the past states, so state histories carry
the same information. -/
def Policy (S A : Type*) : Type _ := (t : ℕ) → (Fin (t + 1) → S) → A

/-- `π` chooses an admissible action at every time and every history. -/
def Model.Admissible (M : Model S A) (π : Policy S A) : Prop :=
  ∀ (t : ℕ) (h : Fin (t + 1) → S), π t h ∈ M.adm t (h (Fin.last t))

/-- The continuation of `π` after the first state `s`: `(π.tail s) k h = π (k+1) (s, h)`. -/
def Policy.tail (π : Policy S A) (s : S) : Policy S A :=
  fun k h => π (k + 1) (Fin.cons s h)

/-- The first `t + 1` states `(h_0, …, h_t)` of a path `h = (h_0, …, h_T)`. -/
def pathPrefix {T : ℕ} (h : Fin (T + 1) → S) (t : Fin T) : Fin (t.val + 1) → S :=
  fun j => h (Fin.castLE (by have := t.isLt; omega) j)

/-- The probability `∏_{t<T} P_t(h_{t+1} | h_t, μ_t(h_0, …, h_t))` of a state path under `π`. -/
noncomputable def pathWeight (M : Model S A) {T : ℕ} (π : Policy S A) (h : Fin (T + 1) → S) :
    ℝ≥0∞ :=
  ∏ t : Fin T, M.P t.val (h t.castSucc) (π t.val (pathPrefix h t)) (h t.succ)

/-- The cumulative reward `∑_{t<T} r_t(h_t, μ_t(h_0, …, h_t), h_{t+1})` of a state path. -/
def pathReward (M : Model S A) {T : ℕ} (π : Policy S A) (h : Fin (T + 1) → S) : ℝ :=
  ∑ t : Fin T, M.r t.val (h t.castSucc) (π t.val (pathPrefix h t)) (h t.succ)

/-- The law of the cumulative reward `∑_{k=0}^{T-1} r_k(S_k, a_k, w_k)` over horizon `T`, given
`S_0 = s`, under policy `π`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, (3), p.9.

**Formalization Note** A finite sum of Dirac masses over the state paths `(s, g_1, …, g_T)`
(`Fin.cons s g`), each weighted by its probability. -/
noncomputable def rewardLaw [Fintype S] (M : Model S A) (T : ℕ) (π : Policy S A) (s : S) :
    Measure ℝ :=
  ∑ g : Fin T → S, pathWeight M π (Fin.cons s g : Fin (T + 1) → S) •
    Measure.dirac (pathReward M π (Fin.cons s g : Fin (T + 1) → S))

end QuantileMDP


