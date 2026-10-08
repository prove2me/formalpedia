-- Prove2me | Definitions.Def_WeightedMajority_InfinitePool_IsWMI2Run
-- name    : WeightedMajority_InfinitePool_IsWMI2Run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T14:42:52.413006+00:00
-- url     : https://prove2.me/theorems/71ee5d8e-6317-4e03-a007-792d174998ce
-- title:
--   Runs of WMI₂, the Weighted Majority Algorithm on a countably infinite pool (Section 4)
-- statement:
--   This definition fixes the algorithm $\mathrm{WMI}_2$ of Littlestone and Warmuth, which runs the Weighted Majority Algorithm on a countably infinite pool $A_1, A_2, \dots$ of prediction algorithms by working only with an active initial segment $A_1, \dots, A_l$ of the pool.
--
--   The data are a parameter $\beta$ with $0 \le \beta < 1$, two real functions $W$ and $\hat W$ on the positive integers ($W(i)$ is the initial weight of $A_i$), a number $T$ of trials, the predictions $x_t(i) \in \{0,1\}$ of every pool member in trial $t \in \{0, \dots, T-1\}$, and the labels $\rho_t \in \{0,1\}$. Write $u = (1+\beta)/2$ and, for a number $m$ of mistakes,
--   $$
--   \theta(m) = \frac{u^{m+1}\,\hat W(1)}{(1-\beta)(m+1)(m+2)}.
--   $$
--   Let $m_t$ be the number of trials $s < t$ in which the master prediction differed from the label. A run consists of master predictions $\gamma_t$, weights $w_t(i)$ and active-pool sizes $l_t$ (at the beginning of trial $t$; index $T$ is the state after the last trial) such that:
--
--   1. $l_0$ is the least $l \ge 0$ with $\hat W(l+1) \le \theta(0)$, and $w_0(i) = W(i)$ for $i \le l_0$.
--   2. With $q_b = \sum_{i \le l_t,\ x_t(i) = b} w_t(i)$ the active weight predicting $b$: if $q_0 > q_1 + \theta(m_t)$ then $\gamma_t = 0$; if $q_1 > q_0 + \theta(m_t)$ then $\gamma_t = 1$; otherwise either prediction is allowed.
--   3. For every active $i \le l_t$: $w_{t+1}(i) = \beta\, w_t(i)$ if $\gamma_t \ne \rho_t$ and $x_t(i) \ne \rho_t$, and $w_{t+1}(i) = w_t(i)$ otherwise.
--   4. If $\gamma_t = \rho_t$ then $l_{t+1} = l_t$. If $\gamma_t \ne \rho_t$ then $l_{t+1}$ is the least $l \ge l_t$ with $\hat W(l+1) \le \theta(m_{t+1})$, and every newly active member $l_t < i \le l_{t+1}$ gets $w_{t+1}(i) = W(i)$.
--
--   The definition also introduces the weights $\omega_t(i)$ of Theorem 4.1: $\omega_t(i) = w_t(i)$ for an active member $i \le l_t$ and $\omega_t(i) = W(i)$ for an inactive one.
--
--   This is the algorithm whose mistake bound is the subject of Theorem 4.1; the slack band in rule 2 lets an implementation use finite-precision approximations of $q_0$ and $q_1$.
--
--   **Formalization Note.** The pool is indexed by `ℕ+`, trials by `Fin T`; `false` stands for $0$ and `true` for $1$. Because the prediction inside the slack band is free, a run is a relation (`IsWMI2Run`), not a function. Only the weights of active members are constrained; inactive weights enter the theorems through `omega`. The paper's requirement that $W$ and $\hat W$ be computable only makes the algorithm implementable and is not part of the definition. `slack` is $\theta$, `mistakesBefore` is $m_t$, `activeVote` is $q_b$.
-- source:
--   Littlestone, Warmuth, The Weighted Majority Algorithm, Inform. and Comput. 108 (1994), pp. 225–226, Weighted Majority Algorithm (WMI2); p. 226, Theorem 4.1 (definition of ω_i)

import Mathlib

namespace WeightedMajority.InfinitePool

/-- The constant `u = (1 + β) / 2` of Section 4. -/
noncomputable def u (β : ℝ) : ℝ := (1 + β) / 2

/-- The slack `u^(m+1) Ŵ(1) / ((1 - β)(m + 1)(m + 2))` used by WMI₂ after `m` mistakes, both
for the size of the active pool and for the band in which the master prediction is free. -/
noncomputable def slack (β : ℝ) (What : ℕ+ → ℝ) (m : ℕ) : ℝ :=
  u β ^ (m + 1) * What 1 / ((1 - β) * ((m : ℝ) + 1) * ((m : ℝ) + 2))

/-- The number of mistakes made by the master in the trials preceding trial `t`
(trials are numbered `0, …, T - 1`; `t = T` counts all of them). -/
def mistakesBefore {T : ℕ} (prediction label : Fin T → Bool) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun s : Fin T => s.val < t ∧ prediction s ≠ label s)).card

/-- The total weight of the active pool members `A_1, …, A_l` that predict `b` in trial `t`,
where `l` is the size of the active pool at the beginning of that trial. -/
def activeVote {T : ℕ} (x : Fin T → ℕ+ → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ)
    (t : Fin T) (b : Bool) : ℝ :=
  ∑ k ∈ Finset.range (l t.val),
    if x t (Nat.succPNat k) = b then w t.val (Nat.succPNat k) else 0

/-- The weights `ω_i` of Theorem 4.1 at the boundary before trial `t`: the current weight
`w t i` of an active member (`i ≤ l t`), and the initial weight `W i` of an inactive one. -/
def omega (W : ℕ+ → ℝ) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ) (t : ℕ) (i : ℕ+) : ℝ :=
  if (i : ℕ) ≤ l t then w t i else W i

/-- A run of WMI₂ (Littlestone–Warmuth 1994, pp. 225–226) on a countably infinite pool
`A_1, A_2, …` (indexed by `ℕ+`) over the trials `0, …, T - 1`. `x t i` is the prediction of
`A_i` in trial `t`, `label t` the label, `prediction t` the master prediction (`false` = 0,
`true` = 1); `w t i` is the weight of `A_i` and `l t` the size of the active pool at the
beginning of trial `t` (for `t = T`: after the last trial). Only the weights of active members
`i ≤ l t` are constrained. Inside the slack band either master prediction is allowed. -/
structure IsWMI2Run {T : ℕ} (β : ℝ) (W What : ℕ+ → ℝ) (x : Fin T → ℕ+ → Bool)
    (label : Fin T → Bool) (prediction : Fin T → Bool) (w : ℕ → ℕ+ → ℝ) (l : ℕ → ℕ) :
    Prop where
  /-- `l` starts at `0` and is raised initially (with `m = 0`) until
  `Ŵ(l + 1) ≤ slack 0`, i.e. to the least such `l`. -/
  init_size : What (Nat.succPNat (l 0)) ≤ slack β What 0
  init_size_min : ∀ l' < l 0, slack β What 0 < What (Nat.succPNat l')
  /-- The initial weight of every initially active member `A_i` is `W(i)`. -/
  init_weight : ∀ i : ℕ+, (i : ℕ) ≤ l 0 → w 0 i = W i
  /-- Prediction 0 when `q₀ > q₁ + slack m`. -/
  predict_zero : ∀ t : Fin T,
    activeVote x w l t true + slack β What (mistakesBefore prediction label t.val) <
      activeVote x w l t false → prediction t = false
  /-- Prediction 1 when `q₁ > q₀ + slack m`. -/
  predict_one : ∀ t : Fin T,
    activeVote x w l t false + slack β What (mistakesBefore prediction label t.val) <
      activeVote x w l t true → prediction t = true
  /-- On a mistake, every active member that disagreed with the label has its weight
  multiplied by `β`; other active weights, and all weights in trials without a mistake,
  are unchanged. -/
  update_weight : ∀ (t : Fin T) (i : ℕ+), (i : ℕ) ≤ l t.val →
    w (t.val + 1) i =
      if prediction t ≠ label t ∧ x t i ≠ label t then β * w t.val i else w t.val i
  /-- Without a mistake the active pool does not change. -/
  size_keep : ∀ t : Fin T, prediction t = label t → l (t.val + 1) = l t.val
  /-- At the end of a trial with a mistake, `l` is increased as necessary until
  `Ŵ(l + 1) ≤ slack m`, where `m` now counts this mistake: `l (t+1)` is the least
  `l' ≥ l t` satisfying the inequality. -/
  size_grow_le : ∀ t : Fin T, prediction t ≠ label t → l t.val ≤ l (t.val + 1)
  size_grow : ∀ t : Fin T, prediction t ≠ label t →
    What (Nat.succPNat (l (t.val + 1))) ≤
      slack β What (mistakesBefore prediction label (t.val + 1))
  size_grow_min : ∀ t : Fin T, prediction t ≠ label t → ∀ l', l t.val ≤ l' →
    l' < l (t.val + 1) →
      slack β What (mistakesBefore prediction label (t.val + 1)) < What (Nat.succPNat l')
  /-- The newly activated members start with their initial weights `W(i)`. -/
  activate_weight : ∀ (t : Fin T) (i : ℕ+), l t.val < (i : ℕ) → (i : ℕ) ≤ l (t.val + 1) →
    w (t.val + 1) i = W i

end WeightedMajority.InfinitePool


