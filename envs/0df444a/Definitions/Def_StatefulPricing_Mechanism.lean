-- Prove2me | Definitions.Def_StatefulPricing_Mechanism
-- name    : StatefulPricing_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:25:18.721241+00:00
-- url     : https://prove2.me/theorems/979f3aed-453f-4ca7-94b5-ee5d3b5da57c
-- title:
--   Randomized posted price mechanisms: information, feasibility and regret
-- statement:
--   A **randomized posted price mechanism** for DRACC instances with horizon $T$ and bounds $C,W$ posts, at each round $t$, a price vector $p_t$ on the active resources, using its coins $\omega$ and what it has observed: the active sets $A_1,\dots,A_t$, the capacities of the resources that have arrived, and the valuations $v_1,\dots,v_{t-1}$ (each reported at the end of its round). It must post a price vector feasible for its own inventory $\lambda_t$ at every round $1\le t\le T$. Its regret with respect to a finite family $\Gamma$ of pricing policies is
--   $$
--   \max_{\gamma\in\Gamma}\sum_{t=1}^T\hat q^{\gamma}_t-\mathbb E\Big[\sum_{t=1}^T\hat q^{p_t}_t\Big],
--   $$
--   where the expectation is over the mechanism's coins.
--
--   The module defines the mechanism type, the relation "two instances agree up to round $t$", the non-anticipation and feasibility conditions, the mechanism's inventory and revenue, and the regret.
--
--   **Formalization Note** Non-anticipation is stated as: on any two instances that agree up to round $t$ (same $A_1,\dots,A_t$, same capacities of arrived resources, same $v_s$ on bundles of $A_s$ for $s<t$), the round-$t$ prices are equal. The parameters $T,C,W$ and the tie-breaking order are known upfront. The instance is a fixed argument (an oblivious adversary) and the benchmark is each policy's revenue along its own trajectory (policy regret).
-- source:
--   Emek, Lavi, Niazadeh, Shi, Stateful Posted Pricing with Vanishing Regret via Dynamic Deterministic Markov Decision Processes, arXiv:2005.01869v2, §2, pp.5–6

import Mathlib
import Definitions.Def_StatefulPricing_Instance

set_option autoImplicit false

namespace StatefulPricing

open MeasureTheory

/-- **A randomized posted price mechanism** for DRACC instances with horizon `T` and bounds `C`,
`W` (arXiv:2005.01869v2, §2, p.5): `M ω t I` is the price vector `p_t` posted at round `t` on the
instance `I` when the mechanism's internal coins are `ω`.

The protocol (p.5): "In each round t ∈ [T], the mechanism first realizes which resources i ∈ [N]
arrive at the beginning of round t, together with their initial capacity c(i), and which resources
departed at the end of round t − 1, thus updating its knowledge of At. It then posts a price vector
pt ∈ (0, 1]^At … the valuation function vt of user t is reported to the decision maker at the end
of each round t." What the mechanism may use is `Mechanism.NonAnticipating`; feasibility is
`Mechanism.AlwaysFeasible`. -/
abbrev Mechanism (Ω : Type*) (T C W : ℕ) := Ω → ℕ → Instance T C W → (ℕ → ℝ)

/-- Two instances look the same to the mechanism at the beginning of round `t` (before `p_t` is
posted): the same active sets `A_1, …, A_t`, the same capacities of the resources that have
arrived, and the same valuations `v_s` on bundles of `A_s` for the rounds `s < t`
(arXiv:2005.01869v2, p.5). -/
def Instance.AgreeUpTo {T C W : ℕ} (I I' : Instance T C W) (t : ℕ) : Prop :=
  (∀ s ≤ t, I.active s = I'.active s) ∧
  (∀ s ≤ t, ∀ i ∈ I.active s, I.cap i = I'.cap i) ∧
  (∀ s < t, ∀ A ⊆ I.active s, I.v s A = I'.v s A)

namespace Mechanism

variable {Ω : Type*} {T C W : ℕ}

/-- The mechanism is non-anticipating: the round-`t` prices depend on the instance only through
what has been revealed before they are posted (`Instance.AgreeUpTo`). The parameters `T`, `C`, `W`
and the tie-breaking order are known upfront (p.5: "the decision maker knows the parameters C and
W upfront"). -/
def NonAnticipating (M : Mechanism Ω T C W) : Prop :=
  ∀ ω t (I I' : Instance T C W), I.AgreeUpTo I' t → M ω t I = M ω t I'

/-- The mechanism's inventory trajectory `λ_t` on instance `I` for coins `ω`. -/
noncomputable def inv (rank : Finset ℕ → ℕ) (M : Mechanism Ω T C W) (ω : Ω)
    (I : Instance T C W) : ℕ → (ℕ → ℕ) :=
  I.traj rank (fun t _ => M ω t I)

/-- The mechanism always posts feasible prices: for every coin outcome, every instance and every
round `1 ≤ t ≤ T`, `p_t` is feasible for the mechanism's own inventory `λ_t` (p.5: "we require that
the posted price vector pt is feasible for λt for every 1 ≤ t ≤ T"). -/
def AlwaysFeasible (rank : Finset ℕ → ℕ) (M : Mechanism Ω T C W) : Prop :=
  ∀ ω (I : Instance T C W) t, 1 ≤ t → t ≤ T →
    Feasible (I.active t) (M.inv rank ω I t) (M ω t I)

/-- The mechanism's realized revenue `Σ_{t=1}^T q̂^{p_t}_t` for coins `ω`. -/
noncomputable def revenue (rank : Finset ℕ → ℕ) (M : Mechanism Ω T C W) (ω : Ω)
    (I : Instance T C W) : ℝ :=
  I.ruleRevenue rank (fun t _ => M ω t I)

/-- The regret with respect to a finite family `Γ` of pricing policies (arXiv:2005.01869v2,
pp.5–6): `max_{γ∈Γ} Σ_{t=1}^T q̂^γ_t − E[Σ_{t=1}^T q̂^{p_t}_t]`, "where the expectation is taken
over the decision maker's randomness".

**Formalization Note.** The instance is a fixed argument and the expectation is over `ω ∼ P`
only (an oblivious adversary). The benchmark is each policy's revenue along its own inventory
trajectory `λ^γ_t` (policy regret). The maximum is the real `⨆` over the finite, nonempty index
type of `Γ`. -/
noncomputable def regret [MeasurableSpace Ω] (rank : Finset ℕ → ℕ) (M : Mechanism Ω T C W)
    (P : Measure Ω) (I : Instance T C W) {ι : Type*} (Γ : ι → Policy) : ℝ :=
  (⨆ j, I.policyRevenue rank (Γ j)) - ∫ ω, M.revenue rank ω I ∂P

end Mechanism

end StatefulPricing


