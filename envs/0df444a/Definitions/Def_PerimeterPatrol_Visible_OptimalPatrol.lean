-- Prove2me | Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol
-- name    : PerimeterPatrol_Visible_OptimalPatrol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:53.374057+00:00
-- url     : https://prove2.me/theorems/5befaa88-2c22-4f76-9c50-7d5b32b4e56c
-- title:
--   Theorem 2, pp. 6–7 — the blue–red patrol schedule μ* as a probability measure on dispatch sequences
-- statement:
--   This file constructs the defender's strategy $\mu^*$ of Theorem 2 of Lin, *Optimal Patrol of a Perimeter*.
--
--   Let $\lambda > 0$, $t > 0$ and write $\Delta = t / \lceil \lambda t \rceil$ and $q = \lambda t - \lfloor \lambda t \rfloor \in [0, 1)$.
--
--   1. **Blue patrollers** pass deterministically at the times $jt + k\Delta$ for $j = 0, 1, 2, \dots$ and $k = 1, 2, \dots, \lfloor \lambda t \rfloor$.
--   2. **Red patrollers**: at each slot $jt$, $j = 0, 1, 2, \dots$, a patroller passes independently with probability $q$. This is realised with i.i.d. uniform draws $\omega_0, \omega_1, \dots$ on $[0, 1]$: the red patroller at $jt$ is present iff $\omega_j < q$.
--
--   With $C_\omega(u)$ the total number of blue and red patrollers that have passed by time $u$, the arrival time of patroller $n + 1$ is
--
--   $$s_n(\omega) = \inf\{u \in \mathbb R : C_\omega(u) > n\},$$
--
--   the sorted enumeration of all arrival times, and $\mu^*$ is the law of $s(\omega)$ when $\omega$ has the product uniform law.
--
--   When $\lambda t$ is an integer, $q = 0$, no red patroller ever passes, $\Delta = 1/\lambda$, and the blue times $jt + k/\lambda$ are exactly $m/\lambda$, $m = 1, 2, \dots$: patrollers at fixed intervals of $1/\lambda$, which is the integer case of Theorem 2. One construction covers both cases. Figure 1 of the paper shows the case $\lambda t = 3.2$, where $\Delta = t/4$, three blue patrollers per period and a red one with probability $0.2$.
--
--   **Formalization Note.** The construction is stated without a measurability proof: $\mu^*$ is a pushforward (`Measure.map`), which Lean sets to $0$ for a non-measurable map. That the map is measurable and that $\mu^*$ is a feasible mixed strategy is a theorem of the mission (the first conjunct of Theorem 2), not an assumption. On the null event that only finitely many patrollers ever pass, the infimum of an empty set is $0$ in Lean and the path is infeasible; this does not affect $\mu^*$-almost-sure statements.
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, pp. 6–7, Theorem 2 and Figure 1

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model

open MeasureTheory

namespace PerimeterPatrol.Visible

/-- The blue time point `j t + k Δ` with `Δ = t / ⌈λt⌉`, indexed by `jk = (j, k)`. -/
noncomputable def bluePoint (lam t : ℝ) (jk : ℕ × ℕ) : ℝ :=
  (jk.1 : ℝ) * t + (jk.2 : ℝ) * (t / (⌈lam * t⌉₊ : ℝ))

/-- The admissible blue indices: `j = 0, 1, 2, …` and `k = 1, …, ⌊λt⌋`. -/
def IsBlue (lam t : ℝ) (jk : ℕ × ℕ) : Prop :=
  1 ≤ jk.2 ∧ jk.2 ≤ ⌊lam * t⌋₊

/-- The number of blue patrollers that have passed by time `u`. -/
noncomputable def blueCount (lam t u : ℝ) : ℕ :=
  Nat.card {jk : ℕ × ℕ | IsBlue lam t jk ∧ bluePoint lam t jk ≤ u}

/-- The red patroller at the slot `j t` is present iff the `j`-th uniform draw `ω j` is below
`λt − ⌊λt⌋`; the draws are independent, so the red patrollers are independent
Bernoulli(`λt − ⌊λt⌋`). -/
def redPresent (lam t : ℝ) (ω : ℕ → unitInterval) (j : ℕ) : Prop :=
  ((ω j : ℝ) < lam * t - ⌊lam * t⌋₊)

/-- The number of patrollers (blue and red) that have passed by time `u`, for the draws `ω`. -/
noncomputable def count (lam t : ℝ) (ω : ℕ → unitInterval) (u : ℝ) : ℕ :=
  blueCount lam t u + Nat.card {j : ℕ | (j : ℝ) * t ≤ u ∧ redPresent lam t ω j}

/-- The arrival time of patroller `n + 1` (the sorted enumeration of all arrival times). -/
noncomputable def sched (lam t : ℝ) (ω : ℕ → unitInterval) (n : ℕ) : ℝ :=
  sInf {u : ℝ | n < count lam t ω u}

/-- The defender's strategy of Theorem 2: the law of the schedule `sched` when the draws `ω j` are
i.i.d. uniform on `[0, 1]`. -/
noncomputable def optimalPatrol (lam t : ℝ) : Measure (ℕ → ℝ) :=
  Measure.map (fun ω : ℕ → unitInterval => fun n => sched lam t ω n)
    (Measure.infinitePi fun _ : ℕ => (volume : Measure unitInterval))

end PerimeterPatrol.Visible


