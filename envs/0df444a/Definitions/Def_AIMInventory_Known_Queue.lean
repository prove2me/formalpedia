-- Prove2me | Definitions.Def_AIMInventory_Known_Queue
-- name    : AIMInventory_Known_Queue
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:03.987174+00:00
-- url     : https://prove2.me/theorems/cb3533f8-8b09-4027-9429-75c3812f149a
-- title:
--   §2.3.2 and App. C: the waiting times W_t(θ), the queue Z_t(θ), renewal epochs τ_i(θ), busy periods J_i(θ), and i(θ,t)
-- statement:
--   These are the queueing processes of §2.3.2 (pp. 8–9) and Appendix C (p. 18), as functions of a demand path $D_1, D_2, \dots$.
--
--   For $\theta > 0$ the **waiting time** process of a single-server queue with inter-arrival times $D_t$ and deterministic service time $\theta$ is given by Lindley's equation
--   $$W_1(\theta) = 0, \qquad W_{t+1}(\theta) = [W_t(\theta) + \theta - D_t]^+ \quad (t \ge 1),$$
--   and the **auxiliary queue** with decreasing service times by
--   $$Z_1(\theta) = 0, \qquad Z_{t+1}(\theta) = \Big[Z_t(\theta) + \frac{\theta}{\sqrt t} - D_t\Big]^+ \quad (t \ge 1).$$
--
--   The **renewal epochs** are $\tau_0(\theta) = 1$ and $\tau_i(\theta) = \inf\{t > \tau_{i-1}(\theta) \mid W_t(\theta) = 0\}$ for $i \ge 1$, with value $+\infty$ when the queue never empties again. The $i$-th **busy period** is $J_i(\theta) = \{s \mid \tau_{i-1}(\theta) < s \le \tau_i(\theta)\}$, and $|J_i(\theta)| \in \{1,2,\dots\} \cup \{+\infty\}$ is its length. For $t \ge 2$, $i(\theta,t)$ is the index $k \ge 1$ with $t \in J_k(\theta)$; the busy periods are disjoint and cover $\{2,3,\dots\}$, so this index exists and is unique.
--
--   The process $Z_t(\rho)$ dominates the excess inventory of the AIM algorithm (Theorem 6), and $W_t(\theta) \ge Z_t(\theta)$ is the stationary process whose busy periods control it (Lemma 5).
--
--   **Formalization Note** The paper writes $W_0(\theta)=0$, $\tau_0(\theta)=0$ and $Z_0(\theta)=0$, which leaves $D_0$ and $\theta/\sqrt 0$ undefined; the proof of Theorem 6 uses $Z_1(\rho)=0$. This file shifts the start to $t = 1$ for both $W$ and $Z$, with $\tau_0 = 1$, so $Z_t \le W_t$ pathwise and $|J_1(\theta)| = \tau_1(\theta) - 1 \ge 1$; period $t=1$ belongs to no busy period. The demand path is zero-based ($D_t$ is `d (t - 1)`); index $0$ of $W$ and $Z$ is unused. Epochs live in `ℕ∞` and lengths are `Set.encard`, so an infinite busy period has length $\top$. `busyIndex` is the least $k \ge 1$ with $t \in J_k$, and takes the default value $0$ (with $J_0 = \emptyset$) only for $t \le 1$.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, pp. 8–9, §2.3.2, Eqs. (6)–(7); p. 18, Appendix C (definition of i(θ, t))

import Mathlib
import Definitions.Def_CappedBaseStock_Model
open scoped ENNReal NNReal
noncomputable section

namespace AIMInventory.Known

/-- Lindley's waiting-time process (6), p. 8, with service time `θ` and inter-arrival times the
demands: `W_1(θ) = 0` and `W_{t+1}(θ) = [W_t(θ) + θ − D_t]⁺` for `t ≥ 1`. The demand path is
zero-based (`D_t = d (t - 1)`); index `0` is unused and set to `0`. -/
def waiting (θ : ℝ) (d : CappedBaseStock.DemandPath) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | (t + 2) => max (waiting θ d (t + 1) + θ - (d t : ℝ)) 0

/-- The auxiliary queue (7), p. 9: `Z_1(θ) = 0` and `Z_{t+1}(θ) = [Z_t(θ) + θ/√t − D_t]⁺`
for `t ≥ 1`. Index `0` is unused and set to `0`. -/
def auxQueue (θ : ℝ) (d : CappedBaseStock.DemandPath) : ℕ → ℝ
  | 0 => 0
  | 1 => 0
  | (t + 2) => max (auxQueue θ d (t + 1) + θ / Real.sqrt ((t : ℝ) + 1) - (d t : ℝ)) 0

/-- Renewal epochs of `W(θ)`, p. 8: `τ_0(θ) = 1` and
`τ_i(θ) = inf {t > τ_{i−1}(θ) | W_t(θ) = 0}` in `ℕ∞` (`⊤` when the queue never empties again,
and `⊤` forever after). -/
def renewalEpoch (θ : ℝ) (d : CappedBaseStock.DemandPath) : ℕ → ℕ∞
  | 0 => 1
  | (i + 1) =>
      sInf ((fun t : ℕ => (t : ℕ∞)) ''
        {t : ℕ | renewalEpoch θ d i < (t : ℕ∞) ∧ waiting θ d t = 0})

/-- The `i`-th busy period `J_i(θ) = {s | τ_{i−1}(θ) < s ≤ τ_i(θ)}`, p. 8, for `i ≥ 1`. -/
def busyPeriod (θ : ℝ) (d : CappedBaseStock.DemandPath) (i : ℕ) : Set ℕ :=
  {s : ℕ | renewalEpoch θ d (i - 1) < (s : ℕ∞) ∧ (s : ℕ∞) ≤ renewalEpoch θ d i}

/-- The length `|J_i(θ)|` of the `i`-th busy period, in `ℕ∞` (`⊤` if it never ends). -/
def busyLength (θ : ℝ) (d : CappedBaseStock.DemandPath) (i : ℕ) : ℕ∞ :=
  (busyPeriod θ d i).encard

/-- The index `i(θ, t)` of the busy period containing period `t`, App. C, p. 18: the least
`k ≥ 1` with `t ∈ J_k(θ)` (the busy periods are disjoint, so it is the unique such `k`). Every
`t ≥ 2` lies in some busy period; for `t ≤ 1` no `k` exists and the value is the default `0`. -/
def busyIndex (θ : ℝ) (d : CappedBaseStock.DemandPath) (t : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ t ∈ busyPeriod θ d k}

end AIMInventory.Known


