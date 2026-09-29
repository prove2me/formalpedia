-- Prove2me | Definitions.Def_RobustMDP_Discounted_discountedCost
-- name    : RobustMDP_Discounted_discountedCost
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T23:56:15.473456+00:00
-- url     : https://prove2.me/theorems/68dba696-0b37-4841-ae9b-0cb89715c56b
-- title:
--   Discounted cost $C_\infty(\pi, \tau)$ of a stationary policy under stationary transition matrices
-- statement:
--   Fix an initial state $i_0$, a stationary control policy $\pi = (\mathbf a, \mathbf a, \dots)$ and a stationary policy of nature $(P^a)_{a \in \mathcal A}$. The state distribution at time $t$ is
--   $$\mu_0 = e_{i_0}, \qquad \mu_{t+1}(j) = \sum_i \mu_t(i)\, P^{\mathbf a(i)}(i, j).$$
--   The **discounted cost** is the expected total discounted cost
--   $$C_\infty(\pi, \tau) = \sum_{t \ge 0} \nu^t \sum_i \mu_t(i)\, c(i, \mathbf a(i)) = \mathbf E\Big(\sum_{t\ge 0} \nu^t c(i_t, \mathbf a(i_t))\Big).$$
--
--   The paper defines $C_\infty(\pi, \tau)$ as the limit, as $N \to \infty$, of the $N$-stage expected cost (2) with stage costs $\nu^t c(i, a)$ and zero terminal cost. That $N$-stage cost is the partial sum of the series above.
--
--   **Formalization Note** The series is written as a `tsum`. Its terms are nonnegative and bounded by $\nu^t \max c$, because each $\mu_t$ is a probability vector, so the series is summable and the `tsum` equals the limit of the partial sums, the paper's definition. The cost is defined by the forward state distribution, not by a fixed-point equation: the fixed-point characterization is milestone (26).
-- source:
--   Nilim and El Ghaoui, Robust Control of Markov Decision Processes with Uncertain Transition Matrices, Oper. Res. 53 (2005), p. 781, Eq. (2) and the definition of the discounted cost function

import Mathlib
import Definitions.Def_RobustMDP_Discounted_Model

namespace RobustMDP.Discounted

/-- The distribution of the state `i_t` at time `t` under a stationary controller policy `π`
and stationary transition matrices `P` (`P a i j` = probability of moving from `i` to `j` under
action `a`), starting from the initial state `i₀`: `μ_0 = e_{i₀}` and
`μ_{t+1}(j) = ∑_i μ_t(i) P^{𝐚(i)}(i, j)`. -/
noncomputable def stateDist {n : ℕ} {A : Type} (π : StationaryPolicy n A)
    (P : A → Fin n → Fin n → ℝ) (i₀ : Fin n) : ℕ → Fin n → ℝ
  | 0 => fun j => if j = i₀ then 1 else 0
  | t + 1 => fun j => ∑ i, stateDist π P i₀ t i * P (π i) i j

/-- The discounted cost `C_∞(π, τ)` (p. 781): the expected total cost (2) with stage costs
`c_t(i, a) = ν^t c(i, a)` and zero terminal cost, in the limit `N → ∞`, from the initial state
`i₀`, for a stationary policy `π` and a stationary nature policy `P ∈ 𝒯_s`:
`C_∞(π, P) = ∑_{t ≥ 0} ν^t ∑_i μ_t(i) c(i, 𝐚(i))`, with `μ_t = stateDist π P i₀ t`.
It is written as a `tsum`; its terms are nonnegative and bounded by `ν^t max c` (each `μ_t` is a
probability vector), so the series is summable and the `tsum` is the limit of the `N`-stage
costs, which is the paper's definition. -/
noncomputable def Model.discountedCost {n : ℕ} {A : Type} (M : Model n A) (i₀ : Fin n)
    (π : StationaryPolicy n A) (P : M.StationaryNature) : ℝ :=
  ∑' t : ℕ, M.discount ^ t * ∑ i, stateDist π P.1 i₀ t i * M.cost i (π i)

end RobustMDP.Discounted


