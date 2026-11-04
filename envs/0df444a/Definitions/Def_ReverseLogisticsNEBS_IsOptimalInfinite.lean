-- Prove2me | Definitions.Def_ReverseLogisticsNEBS_IsOptimalInfinite
-- name    : ReverseLogisticsNEBS_IsOptimalInfinite
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:04.778801+00:00
-- url     : https://prove2.me/theorems/aff84b57-6cb9-4de6-9ec3-ee6b3fa8ea42
-- title:
--   Optimality of a stationary NEBS policy for the infinite-horizon problem (18)
-- statement:
--   A **policy** $\pi$ assigns to each period $\tau$, Markov state $\omega$ and echelon state $y$ a schedule $\pi_\tau(\omega, y)$; it is **feasible** if $\pi_\tau(\omega, y) \in \mathbb Y(y)$ (6) at every nested $y$. Its cost from $(t, \omega, y)$ is the limit as the horizon grows of the expected discounted sum
--   $$
--   \mathcal V_t(\omega, y, \pi) = \lim_{T\to\infty} \mathbb E\Big[\sum_{\tau=t}^{T} \alpha^{\tau-t}\Big(\gamma_\tau(\omega_\tau, Y^R_{1\tau}) + \sum_j \big(c^E_j Y^E_{j\tau} + c_j Y_{j\tau} - c^R_j Y^R_{j\tau} - k^E_j y_{j\tau}\big)\Big)\Big],
--   $$
--   with $y_{\tau+1} = Y_\tau - D_\tau$, computed by backward recursion of conditional expectations.
--
--   The **stationary NEBS policy** with levels $S^E(\omega), S^R(\omega), S(\omega)$ takes the schedule (15)–(17) at the current state. It is **optimal for (18)** (`IsOptimalInfinite`) if it is feasible and, for every period $t \ge 1$, Markov state $\omega$ and nested state $y$, all its expectations are finite, its cost from $(t, \omega, y)$ exists, and that cost is at most the cost of every feasible policy whose expectations are finite and whose cost converges.
--
--   **Formalization Note** (18) is read through (5)/(8): the one-period cost uses $\gamma_\tau$ and the actual state $y_\tau = Y_{\tau-1} - D_{\tau-1}$ (the display (18) writes $D_\tau$ in the $-k^E_j$ term and $(p+H_1)(D - Y^R_1)^+$, which differs from $\gamma$ by the constant $H_1\mathbb E[D]$). Policies are Markov, functions of the current $(\omega, y)$. Policies with infinite or non-convergent expected cost are not compared.
-- source:
--   Angelus–Özer, When Variability Trumps Volatility: Optimal Control and Value of Reverse Logistics in Supply Chains with Multiple Flows of Product, SSRN 3508009 (Dec. 21, 2019), §4, pp.16–17: policies π and 𝒱_t(π), (18); Theorem 7 and Theorem 8, p.17

import Mathlib
import Definitions.Def_ReverseLogisticsNEBS_Sched
import Definitions.Def_ReverseLogisticsNEBS_nebsE

open MeasureTheory ProbabilityTheory Filter Topology

namespace ReverseLogisticsNEBS

namespace Model

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] (M : Model N Ω)

/-- The one-period cost (5)/(8) (p.11–12) of the schedule `s` at the echelon state `y`, Markov
state `ω`, period `τ`: `−Σ_j k^E_j y_j + γ_τ(ω, Y^R_1) + Σ_j (c^E_j Y^E_j + c_j Y_j − c^R_j Y^R_j)`. -/
noncomputable def periodCost (τ : ℕ) (ω : Ω) (y : Fin N → ℝ) (s : Sched N) : ℝ :=
  -∑ j, M.kE j * y j + M.gamma τ ω (firstLoc s.YR) +
    ∑ j, (M.cE j * s.YE j + M.c j * s.Y j - M.cR j * s.YR j)

/-- The expected discounted cost of following the policy `π` for `n` periods starting in period
`τ` from `(ω, y)`: `0` for `n = 0`, and the period cost plus `α` times the expected cost of the
remaining `n − 1` periods from `(ω_{τ+1}, Y_τ − D_τ)` otherwise. -/
noncomputable def policyCostAux (π : ℕ → Ω → (Fin N → ℝ) → Sched N) :
    ℕ → ℕ → Ω → (Fin N → ℝ) → ℝ
  | 0, _ => fun _ _ => 0
  | n + 1, τ => fun ω y =>
      M.periodCost τ ω y (π τ ω y) +
        M.α * ∫ z, policyCostAux π n (τ + 1) z.2 (nextState (π τ ω y) z.1) ∂(M.κ τ ω)

/-- **Optimality of a stationary NEBS policy for the infinite-horizon problem (18)** (p.17).

A policy `π` assigns to every period `τ`, Markov state `ω` and echelon state `y` a schedule
`π τ ω y` (the paper's `π = ((Y^E_1, Y^R_1, Y_1), (Y^E_2, Y^R_2, Y_2), …)`, p.16); it is feasible
when `π τ ω y ∈ 𝕐(y)` (6) at every nested `y`. Its cost from `(t, ω, y)` is the limit, as the
horizon grows, of the expected discounted cost of periods `t, t + 1, …` (the
`lim_{T→∞} Σ_{τ=t}^T α^{τ−t} E[…]` of (18)), computed by `policyCostAux`. The stationary NEBS
policy with levels `S^E(ω), S^R(ω), S(ω)` takes the schedule (15)–(17) at the current state.

`IsOptimalInfinite M SE SR S` holds when, for every period `t ≥ 1`, every Markov state `ω` and
every nested echelon state `y`: the stationary NEBS policy is feasible, all its expectations are
finite, its cost from `(t, ω, y)` exists, and it is at most the cost of every feasible policy
whose expectations are finite and whose cost from `(t, ω, y)` exists.

**Formalization Note.** (18) is read through (5)/(8): the one-period cost is
`γ_τ(ω_τ, Y^R_1τ) + Σ_j (c^E_j Y^E_jτ + c_j Y_jτ − c^R_j Y^R_jτ) − Σ_j k^E_j y_jτ` with the actual
state `y_τ = Y_{τ−1} − D_{τ−1}` (the display (18) writes `D_τ` there and uses
`(p + H_1)(D − Y^R_1)^+`, which differs from `γ` by the constant `H_1 E[D]`). Policies are Markov
(functions of the current `(ω, y)`). A policy is compared only if every expectation in its cost
recursion is finite (at every period `τ ≥ t` and every nested state) and its cost converges;
policies with infinite or undefined cost are not better than any policy with finite cost. -/
def IsOptimalInfinite (SE SR S : Ω → Fin N → ℝ) : Prop :=
  let πs : ℕ → Ω → (Fin N → ℝ) → Sched N := fun _ ω y => nebsSched (SE ω) (SR ω) (S ω) y
  let Feasible : (ℕ → Ω → (Fin N → ℝ) → Sched N) → Prop :=
    fun π => ∀ τ ω (y : Fin N → ℝ), Monotone y → Sched.FeasOrig y (π τ ω y)
  let Admissible : (ℕ → Ω → (Fin N → ℝ) → Sched N) → ℕ → Prop := fun π t =>
    ∀ n τ ω (y : Fin N → ℝ), t ≤ τ → Monotone y →
      Integrable (fun z : ℝ × Ω => M.policyCostAux π n (τ + 1) z.2 (nextState (π τ ω y) z.1))
        (M.κ τ ω)
  Feasible πs ∧
    ∀ t, 1 ≤ t → ∀ ω (y : Fin N → ℝ), Monotone y →
      Admissible πs t ∧
        ∃ V, Tendsto (fun n => M.policyCostAux πs n t ω y) atTop (𝓝 V) ∧
          ∀ π, Feasible π → Admissible π t → ∀ V',
            Tendsto (fun n => M.policyCostAux π n t ω y) atTop (𝓝 V') → V ≤ V'

end Model

end ReverseLogisticsNEBS


