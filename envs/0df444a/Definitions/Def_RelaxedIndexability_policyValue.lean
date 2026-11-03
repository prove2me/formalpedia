-- Prove2me | Definitions.Def_RelaxedIndexability_policyValue
-- name    : RelaxedIndexability_policyValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:19:25.234598+00:00
-- url     : https://prove2.me/theorems/84d161a1-b1a3-4c90-9afd-106636cd3392
-- title:
--   Value of a stationary policy on the belief process of one arm
-- statement:
--   Fix one arm with transition matrix $\mathbf P$ (rows $p_0, \dots, p_{K-1}$), a discount factor $\beta$, an **active reward** $r_1(x)$ and a **passive reward** $r_0(x)$ depending on the current belief $x$, and a stationary policy $\pi$ that maps each belief to an action ($1$ = active, $0$ = passive).
--
--   By the belief update (4), at belief $x$:
--
--   1. if the arm is activated, the reward is $r_1(x)$ and the arm is observed in state $k$ with probability $x_k$, after which the belief is $p_k$;
--   2. if the arm is passive, the reward is $r_0(x)$ and the next belief is $\mathcal T^1(x) = x\mathbf P$.
--
--   The $n$-horizon value $V^{(n)}_\pi(x) = \mathbb E_\pi\big[\sum_{t=1}^{n} \beta^{t-1} r_{u(t)}(\omega(t)) \,\big|\, \omega(1) = x\big]$ satisfies $V^{(0)}_\pi = 0$ and
--   $$
--   V^{(n+1)}_\pi(x) = \begin{cases} r_1(x) + \beta \sum_{k} x_k\, V^{(n)}_\pi(p_k), & \pi(x) = 1,\\ r_0(x) + \beta\, V^{(n)}_\pi(x\mathbf P), & \pi(x) = 0. \end{cases}
--   $$
--   The **value** of $\pi$ is the infinite-horizon expected total discounted reward $V_\pi(x) = \lim_{n\to\infty} V^{(n)}_\pi(x)$, and the **value of action $u$ at $x$**, $V_\pi(x; u)$, is the same limit when the first action is forced to be $u$ and $\pi$ is followed afterwards.
--
--   These are the objects behind the paper's $\hat V_{\beta,m}(\omega_1)$ (the expected total discounted reward of the threshold policy) and $\hat V_{\beta,m}(x; u)$, and, with rewards $0$ when active and $1$ when passive, behind the passive time $\hat D_\beta$.
--
--   **Formalization Note** Beliefs are row vectors `Fin K → ℝ` and $x\mathbf P$ is `x ᵥ* P`. The limit is `limUnder atTop`, which returns a junk value for a non-convergent sequence; for $0<\beta<1$, a row-stochastic $\mathbf P$, $x$ in the simplex and bounded rewards the sequence converges (geometric tail), which is the case in every use in this mission.
-- source:
--   Liu, Relaxed Indexability and Index Policy for Partially Observable Restless Bandits, arXiv:2107.11939v4, belief update (4), p.7; (13)–(14), p.11; value of the threshold policy, p.20

import Mathlib

open Filter Matrix

namespace RelaxedIndexability

variable {K : ℕ}

/-- **One step of the single-arm belief process** (Liu, arXiv:2107.11939v4, (4), p.7, and
(13)–(14), p.11). At belief `x` (a row vector over the `K` states), with continuation value `V`:

* active (`u = true`): the arm is observed, the expected reward is `rAct x`, and the next belief is
  the row `p_k = P k` with probability `x k` (the probability of observing state `k`), so the value
  is `rAct x + β ∑ₖ x k · V(p_k)`;
* passive (`u = false`): the reward is `rPas x` and the next belief is `T¹(x) = x P`, so the value
  is `rPas x + β V(x P)`.

**Formalization Note.** Beliefs are row vectors `Fin K → ℝ`; `x ᵥ* P` is `x P`. -/
noncomputable def beliefStep (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (rAct rPas : (Fin K → ℝ) → ℝ) (u : Bool) (V : (Fin K → ℝ) → ℝ) (x : Fin K → ℝ) : ℝ :=
  if u then rAct x + β * ∑ k, x k * V (P k) else rPas x + β * V (x ᵥ* P)

/-- The `n`-horizon expected total discounted reward `𝔼[∑_{t=1}^{n} β^{t−1} r_t]` of the
stationary policy `π` (belief ↦ action, `true` = active) on the single-arm belief process (4),
started at belief `x`; computed by conditioning on the observation at each active step. -/
noncomputable def horizonValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool) : ℕ → (Fin K → ℝ) → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun x => beliefStep β P rAct rPas (π x) (horizonValue β P rAct rPas π n) x

/-- **The value of a stationary policy on the belief process**: the expected total discounted
reward `𝔼_π[∑_{t=1}^{∞} β^{t−1} r_t | ω(1) = x]` (Liu, arXiv:2107.11939v4, p.20), as the limit of
the `n`-horizon values.

**Formalization Note.** `limUnder` returns a junk value for a non-convergent sequence; for
`0 < β < 1`, a row-stochastic `P`, `x` in the simplex and bounded rewards the sequence converges
(geometric tail). -/
noncomputable def policyValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool) (x : Fin K → ℝ) : ℝ :=
  limUnder atTop fun n => horizonValue β P rAct rPas π n x

/-- **The value of taking action `u` first and following `π` afterwards**, `V(x; u)` in the
notation of (13)–(14) (Liu, arXiv:2107.11939v4, p.11), as the limit of the `n`-horizon values
with the first action forced to `u`. -/
noncomputable def actionValue (β : ℝ) (P : Matrix (Fin K) (Fin K) ℝ)
    (rAct rPas : (Fin K → ℝ) → ℝ) (π : (Fin K → ℝ) → Bool) (u : Bool) (x : Fin K → ℝ) : ℝ :=
  limUnder atTop fun n => beliefStep β P rAct rPas u (horizonValue β P rAct rPas π n) x

end RelaxedIndexability


