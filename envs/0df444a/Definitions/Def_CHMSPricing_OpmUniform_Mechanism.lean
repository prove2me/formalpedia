-- Prove2me | Definitions.Def_CHMSPricing_OpmUniform_Mechanism
-- name    : CHMSPricing_OpmUniform_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:36:59.806667+00:00
-- url     : https://prove2.me/theorems/46709736-e090-4b23-84aa-3cefc53bb6b4
-- title:
--   Truthful single-parameter mechanisms, expected revenue and virtual surplus
-- statement:
--   A (deterministic, direct) **mechanism** $M$ for single-parameter agents $\iota$ maps each reported value profile $\mathbf v$ to an allocation $M(\mathbf v) \subseteq \iota$, the set of served agents, and to a payment $\pi_i(\mathbf v)$ for each agent $i$. An agent with true value $x$ facing reports $\mathbf b$ has quasilinear utility
--   $$u_i(x; \mathbf b) = x \cdot \mathbf 1[i \in M(\mathbf b)] - \pi_i(\mathbf b).$$
--
--   Given value distributions $(F_i)$ and a downward-closed set system $\mathcal J$, the mechanism is **truthful** if, on the type space $\prod_i[\underline v_i, \overline v_i]$:
--
--   1. it is feasible: $M(\mathbf v) \in \mathcal J$;
--   2. it is dominant-strategy incentive compatible: for every agent $i$ and every alternative report $x' \in [\underline v_i, \overline v_i]$, reporting $x'$ instead of $v_i$ (the others' reports fixed) does not raise $i$'s utility;
--   3. it is ex-post individually rational: $u_i(v_i; \mathbf v) \ge 0$;
--   4. the events $\{i \in M(\mathbf v)\}$ and the payments $\pi_i$ are measurable, and the payments are integrable under the prior.
--
--   The **expected revenue** of $M$ is $\mathcal R^M = \mathbb E_{\mathbf v \sim \mathbf F}\big[\sum_i \pi_i(\mathbf v)\big]$, and the **virtual surplus** of a set $S$ of agents at $\mathbf v$ is $\Phi(S, \mathbf v) = \sum_{i \in S} \phi_i(v_i)$ (Definition 1).
--
--   The revenue of Myerson's optimal mechanism, $\mathcal R^{\mathcal M}$, is at least the revenue of every truthful mechanism (Theorem 19), so bounding the revenue of every truthful mechanism bounds $\mathcal R^{\mathcal M}$.
--
--   **Formalization Note** Truthfulness means dominant-strategy incentive compatibility plus ex-post individual rationality; the measurability and integrability clauses make the expected revenue a genuine integral. Payments of unserved agents are not forced to be $0$.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1 (mechanisms); p. 5, §2.3; p. 12, Definition 1 (virtual surplus), Theorem 19

import Mathlib
import Definitions.Def_CHMSPricing_OpmUniform_ValueDist
import Definitions.Def_CHMSPricing_OpmUniform_SetSystem

namespace CHMSPricing.OpmUniform

open MeasureTheory

/-- A deterministic direct mechanism for single-parameter agents `ι` (§2.1, p. 4): it maps a
reported value profile `v` to an allocation `M(v)` (the set of served agents) and a payment
`πᵢ(v)` for each agent. -/
structure Mechanism (ι : Type*) where
  alloc : (ι → ℝ) → Finset ι
  pay : (ι → ℝ) → ι → ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quasilinear utility of agent `i` with true value `x` when the reported profile is `b`. -/
noncomputable def Mechanism.utility (M : Mechanism ι) (i : ι) (x : ℝ) (b : ι → ℝ) : ℝ :=
  (if i ∈ M.alloc b then x else 0) - M.pay b i

/-- A truthful (dominant-strategy incentive compatible), ex-post individually rational
mechanism respecting the feasibility constraint `J` on the type space, with measurable
allocation events and measurable, integrable payments (standing pin P3). -/
structure IsTruthful (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) : Prop where
  feasible : ∀ v ∈ typeSpace D, J.Feasible (M.alloc v)
  dsic : ∀ v ∈ typeSpace D, ∀ i, ∀ x' ∈ Set.Icc (D i).lo (D i).hi,
    M.utility i (v i) (Function.update v i x') ≤ M.utility i (v i) v
  ir : ∀ v ∈ typeSpace D, ∀ i, 0 ≤ M.utility i (v i) v
  alloc_measurable : ∀ i, MeasurableSet {v | i ∈ M.alloc v}
  pay_measurable : ∀ i, Measurable (fun v => M.pay v i)
  pay_integrable : ∀ i, Integrable (fun v => M.pay v i) (prior D)

/-- The expected revenue `𝔼_v[∑ᵢ πᵢ(v)]` of a mechanism under the prior. -/
noncomputable def revenue (D : ι → ValueDist) (M : Mechanism ι) : ℝ :=
  ∫ v, ∑ i, M.pay v i ∂(prior D)

/-- Definition 1 (p. 12): the virtual surplus `Φ(S, v) = ∑_{i ∈ S} φᵢ(vᵢ)` of a set `S`. -/
noncomputable def virtualSurplus (D : ι → ValueDist) (S : Finset ι) (v : ι → ℝ) : ℝ :=
  ∑ i ∈ S, (D i).virtualValue (v i)

end CHMSPricing.OpmUniform


