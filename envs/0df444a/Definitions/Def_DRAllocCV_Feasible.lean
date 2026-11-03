-- Prove2me | Definitions.Def_DRAllocCV_Feasible
-- name    : DRAllocCV_Feasible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:08.936266+00:00
-- url     : https://prove2.me/theorems/3a7909da-1451-4c02-9a91-226c9c94a7cc
-- title:
--   Feasible direct mechanisms $\mathcal X$: (FC) and (IC)
-- statement:
--   A **direct mechanism** $(p,q)$ consists of allocation functions $p_i,q_i\in\mathcal L(\mathcal T,[0,1])$, $i\in\mathcal I$, i.e. bounded Borel-measurable functions from $\mathcal T$ to $[0,1]$. After the agents report types $t'$, agent $i$ receives the good with probability $p_i(t')$, and receives it **and is inspected** with probability $q_i(t')$; an agent found to have lied loses the good. The set $\mathcal X$ of mechanisms feasible in (MDP) consists of those that satisfy
--
--   1. the feasibility conditions (FC): $q_i(t')\le p_i(t')$ for all $i$ and $\sum_{i}p_i(t')\le 1$, for all $t'\in\mathcal T$;
--   2. the incentive compatibility constraints (IC):
--
--   $$
--   p_i(t)\ \ge\ p_i(t'_i,t_{-i})-q_i(t'_i,t_{-i})\qquad\forall i\in\mathcal I,\ \forall t'_i\in\mathcal T_i,\ \forall t\in\mathcal T .
--   $$
--
--   (IC) says that, when the others report truthfully, agent $i$ cannot raise the probability of keeping the good by misreporting. The set $\mathcal X$ does not depend on the ambiguity set.
--
--   **Formalization Note** $p,q$ are functions $\iota\to(\iota\to\mathbb R)\to\mathbb R$ on all of $\mathbb R^I$; only their values on $\mathcal T$ are constrained, and they are required to be Borel measurable on $\mathbb R^I$ (every Borel function on the closed box extends to one). The profile $(t'_i,t_{-i})$ is `Function.update t i t'ᵢ`.
-- source:
--   Bayrak, Koçyiğit, Kuhn, Pınar, Distributionally Robust Optimal Allocation with Costly Verification, arXiv:2211.15122v3, §2, p.6, (FC), (IC); p.7, (MDP) and the definition of 𝒳

import Mathlib
import Definitions.Def_DRAllocCV_typeSpace

namespace DRAllocCV

/-- The **feasible set `𝒳` of (MDP)**: direct mechanisms `(p, q)` with allocation functions
`pᵢ, qᵢ ∈ ℒ(𝒯, [0,1])` (bounded Borel-measurable functions from `𝒯` to `[0,1]`) satisfying the
feasibility conditions (FC) and the incentive compatibility constraints (IC)
(Bayrak, Koçyiğit, Kuhn, Pınar, *Distributionally Robust Optimal Allocation with Costly Verification*, arXiv:2211.15122v3, §2, pp.5–7, (FC), (IC), (MDP)):

* (FC) `qᵢ(t′) ≤ pᵢ(t′)` for all `i` and `∑ᵢ pᵢ(t′) ≤ 1`, for all `t′ ∈ 𝒯`;
* (IC) `pᵢ(t) ≥ pᵢ(t′ᵢ, t₋ᵢ) − qᵢ(t′ᵢ, t₋ᵢ)` for all `i`, all `t′ᵢ ∈ 𝒯ᵢ` and all `t ∈ 𝒯`.

Here `pᵢ(t)` is the probability that agent `i` receives the good and `qᵢ(t)` the probability that
he receives it and is inspected.

**Formalization Note.** A mechanism is a pair `p q : ι → (ι → ℝ) → ℝ` defined on all of
`ι → ℝ`; only the values on `𝒯` are constrained. Borel measurability is required on all of
`ι → ℝ` (every Borel function on the closed set `𝒯` has such an extension with the same values
on `𝒯`); boundedness follows from the `[0,1]` bounds. The profile `(t′ᵢ, t₋ᵢ)` is
`Function.update t i t′ᵢ`. -/
def Feasible {ι : Type*} [Fintype ι] [DecidableEq ι] (tlo thi : ι → ℝ)
    (p q : ι → (ι → ℝ) → ℝ) : Prop :=
  (∀ i, Measurable (p i) ∧ Measurable (q i)) ∧
  (∀ t ∈ typeSpace tlo thi, ∀ i, 0 ≤ p i t ∧ p i t ≤ 1 ∧ 0 ≤ q i t ∧ q i t ≤ 1) ∧
  (∀ t ∈ typeSpace tlo thi, (∀ i, q i t ≤ p i t) ∧ ∑ i, p i t ≤ 1) ∧
  (∀ i, ∀ t ∈ typeSpace tlo thi, ∀ s ∈ Set.Icc (tlo i) (thi i),
    p i (Function.update t i s) - q i (Function.update t i s) ≤ p i t)

end DRAllocCV


