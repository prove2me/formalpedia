-- Prove2me | Definitions.Def_KellyReversibility_Allocation_CapacityAllocation
-- name    : KellyReversibility_Allocation_CapacityAllocation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T02:49:45.92699+00:00
-- url     : https://prove2.me/theorems/d4425d70-0062-430d-aead-323e47196ab2
-- title:
--   §4.1 — mean number in the network, the feasible capacities (4.2), the Lagrangian and the allocation of Theorem 4.1
-- statement:
--   Consider a communication network with $J$ channels. Channel $j$ receives messages at average arrival rate $a_j$ and has capacity $\phi_j$; spending on channel $j$ costs $f_j$ per unit of capacity, and the total budget is $F$.
--
--   1. The **mean number of customers in the network** is
--   $$N(\phi) = \sum_{j=1}^{J} \frac{a_j}{\phi_j - a_j},$$
--   the sum over the channels of the mean $a_j/(\phi_j - a_j)$ of the geometric law (4.1).
--   2. The **feasible capacity vectors** are those $\phi \in \mathbb{R}^J$ with $\phi_j > a_j$ for every $j$ (every channel is stable) and with the cost constraint (4.2)
--   $$\sum_{j} f_j \phi_j = F.$$
--   3. For a multiplier $y$, the **Lagrangian** is
--   $$L(\phi) = \sum_j \frac{a_j}{\phi_j - a_j} + y\Big(\sum_j f_j\phi_j - F\Big).$$
--   4. The **allocation of Theorem 4.1** is
--   $$\phi^*_j = a_j + \frac{\sqrt{a_j f_j}}{\sum_k \sqrt{a_k f_k}}\cdot\frac{F - \sum_k a_k f_k}{f_j}.$$
--
--   These are the objects of the capacity-allocation problem of §4.1: choose capacities, subject to the cost constraint, to minimize the mean number of customers in the network.
--
--   **Formalization Note** Channels are indexed by `Fin J`. The functions are total: $N(\phi)$ and $\phi^*$ are only meaningful when $\phi_j > a_j$, $f_j > 0$ and $\sum_k \sqrt{a_k f_k} > 0$, and every theorem that uses them carries these conditions as hypotheses. Stability $\phi_j > a_j$ is part of the feasible set, so division by $\phi_j - a_j = 0$ never enters the optimization.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 96–97, Eq. (4.1), (4.2), Theorem 4.1 and its proof

import Mathlib

namespace KellyReversibility.Allocation

/-- **Mean number of customers in the network** (Kelly 1979, §4.1, p. 97): with arrival rate
`a j` and capacity `φ j` at channel `j`, the mean number at channel `j` is `a j / (φ j - a j)`,
and the network total is the sum over the `J` channels. -/
noncomputable def meanNumberInNetwork {J : ℕ} (a φ : Fin J → ℝ) : ℝ :=
  ∑ j, a j / (φ j - a j)

/-- **Feasible capacity vectors** for the allocation problem of Kelly 1979, §4.1, p. 97:
every channel is stable (`a j < φ j`, which makes `a j / (φ j - a j)` the mean of the
geometric law (4.1)) and the cost constraint (4.2), `∑ j, f j * φ j = F`, holds. -/
def FeasibleCapacities {J : ℕ} (a f : Fin J → ℝ) (F : ℝ) : Set (Fin J → ℝ) :=
  {φ | (∀ j, a j < φ j) ∧ ∑ j, f j * φ j = F}

/-- **The Lagrangian** of the proof of Theorem 4.1 (Kelly 1979, p. 97):
`L = ∑ j, a j / (φ j - a j) + y * (∑ j, f j * φ j - F)`. -/
noncomputable def lagrangian {J : ℕ} (a f : Fin J → ℝ) (F y : ℝ) (φ : Fin J → ℝ) : ℝ :=
  meanNumberInNetwork a φ + y * ((∑ j, f j * φ j) - F)

/-- **The optimal allocation** of Theorem 4.1 (Kelly 1979, p. 97):
`φ j = a j + (√(a j f j) / ∑ k, √(a k f k)) * (F - ∑ k, a k f k) / f j`. -/
noncomputable def optimalAllocation {J : ℕ} (a f : Fin J → ℝ) (F : ℝ) : Fin J → ℝ :=
  fun j => a j + (Real.sqrt (a j * f j) / ∑ k, Real.sqrt (a k * f k))
    * ((F - ∑ k, a k * f k) / f j)

end KellyReversibility.Allocation


