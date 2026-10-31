-- Prove2me | Definitions.Def_AvgCostLP_Policy
-- name    : AvgCostLP_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:28:21.815507+00:00
-- url     : https://prove2.me/theorems/055b5041-2b71-4cf6-847c-810ef5c4031d
-- title:
--   §2.1 — policies $\pi=(\mu_0,\mu_1,\dots)$ and stationary policies
-- statement:
--   A **policy** is a sequence $\pi=(\mu_0,\mu_1,\dots)$ in which, for each $n\ge0$, $\mu_n(da_n\mid x_0,a_0,\dots,a_{n-1},x_n)$ is a Borel measurable stochastic kernel on $\mathbb A$ given $(\mathbb X\times\mathbb A)^n\times\mathbb X$ obeying the control constraint
--   $$\mu_n\big(A(x_n)\mid x_0,a_0,\dots,a_{n-1},x_n\big)=1\qquad\text{for all }(x_0,a_0,\dots,a_{n-1},x_n)\in(\mathbb X\times\mathbb A)^n\times\mathbb X .$$
--   Policies may be randomized and history-dependent; $\Pi$ denotes the set of all of them.
--
--   A **stationary policy** is given by one Borel measurable stochastic kernel $\mu(da\mid x)$ on $\mathbb A$ given $\mathbb X$ with $\mu(A(x)\mid x)=1$ for every $x$; it is the policy $(\mu,\mu,\dots)$ that uses $\mu(\cdot\mid x_n)$ at every stage. $\Pi_s\subset\Pi$ is the set of stationary policies.
--
--   **Formalization Note** The constraint is imposed at every history and every state, not almost everywhere. A stationary policy is embedded into $\Pi$ by `StationaryPolicy.toPolicy`.
-- source:
--   Yu, On Linear Programming for Constrained and Unconstrained Average-Cost Markov Decision Processes with Countable Action Spaces and Strictly Unbounded Costs, arXiv:1905.12095v3, §2.1, p.5

import Mathlib
import Definitions.Def_AvgCostLP_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace AvgCostLP

/-- Yu, arXiv:1905.12095v3, §2.1, p.5: a (Borel measurable) policy `π = (μ₀, μ₁, …)`.

For each `n ≥ 0`, `μ_n(da_n | x₀, a₀, …, a_{n−1}, x_n)` is a Borel measurable stochastic kernel
on `A` given `(X × A)ⁿ × X` that obeys the control constraint of the MDP,
`μ_n(A(x_n) | x₀, a₀, …, a_{n−1}, x_n) = 1` for every history
`(x₀, a₀, …, a_{n−1}, x_n) ∈ (X × A)ⁿ × X`. Policies are randomized and history-dependent; `Π` is
the type of all of them.

**Formalization Note** The history `(x₀, a₀, …, a_{n−1}, x_n)` is the pair
`(fun k : Fin n => (x_k, a_k), x_n)`. The constraint is imposed at every history, admissible or
not, exactly as on p.5. -/
structure Policy {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (M : Model X A) where
  /-- the decision rule `μ_n` at stage `n` -/
  rule : (n : ℕ) → Kernel ((Fin n → X × A) × X) A
  [isMarkovKernel_rule : ∀ n, IsMarkovKernel (rule n)]
  /-- the control constraint `μ_n(A(x_n) | h_n) = 1` for every history -/
  rule_adm : ∀ n (h : (Fin n → X × A) × X), rule n h (M.adm h.2) = 1

attribute [instance] Policy.isMarkovKernel_rule

/-- Yu, arXiv:1905.12095v3, §2.1, p.5: a stationary policy, given by one Borel measurable
stochastic kernel `μ(da | x)` on `A` given `X` that obeys the control constraint,
`μ(A(x) | x) = 1` for every `x`. `Π_s` is the type of all of them. -/
structure StationaryPolicy {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    (M : Model X A) where
  /-- the kernel `μ(da | x)` -/
  kernel : Kernel X A
  [isMarkovKernel_kernel : IsMarkovKernel kernel]
  /-- the control constraint `μ(A(x) | x) = 1` -/
  kernel_adm : ∀ x, kernel x (M.adm x) = 1

attribute [instance] StationaryPolicy.isMarkovKernel_kernel

/-- A stationary policy `μ` as the policy `π = (μ, μ, …)` (p.5): at every stage the action is drawn
from `μ(· | x_n)`, ignoring the earlier history. This is the inclusion `Π_s ⊂ Π`. -/
noncomputable def StationaryPolicy.toPolicy {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
    {M : Model X A} (μ : StationaryPolicy M) : Policy M where
  rule _ := μ.kernel.comap Prod.snd measurable_snd
  rule_adm _ h := by simpa using μ.kernel_adm h.2

end AvgCostLP


