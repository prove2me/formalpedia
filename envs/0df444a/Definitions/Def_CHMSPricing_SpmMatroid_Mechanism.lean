-- Prove2me | Definitions.Def_CHMSPricing_SpmMatroid_Mechanism
-- name    : CHMSPricing_SpmMatroid_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:17:56.686632+00:00
-- url     : https://prove2.me/theorems/afb9ade9-a57a-49cc-90a7-e4db3990effa
-- title:
--   Deterministic single-parameter mechanisms: truthfulness, individual rationality, revenue, service probabilities, virtual surplus
-- statement:
--   A (deterministic, direct) **mechanism** $M$ for the BSMD maps each reported value profile $\mathbf v$ to an allocation $M(\mathbf v)$, the set of agents served, and a payment $\pi_i(\mathbf v)$ for each agent $i$ (§2.1). Agent $i$ with true value $x$ facing report profile $\mathbf b$ has quasilinear utility $u_i(x; \mathbf b) = x \cdot \mathbf 1[i \in M(\mathbf b)] - \pi_i(\mathbf b)$.
--
--   Given value distributions $F_i$ and a feasibility constraint $\mathcal J$, $M$ is **truthful** if, on the type space $\prod_i [\underline v_i, \overline v_i]$:
--
--   1. $M(\mathbf v) \in \mathcal J$ for every $\mathbf v$;
--   2. (dominant-strategy incentive compatibility) for every $\mathbf v$, every agent $i$ and every alternative report $x'$ in $i$'s support, $u_i(v_i; (x', \mathbf v_{-i})) \le u_i(v_i; \mathbf v)$;
--   3. (ex-post individual rationality) $u_i(v_i; \mathbf v) \ge 0$ for every $\mathbf v$ and $i$;
--   4. the events $\{i \in M(\mathbf v)\}$ and the payments $\pi_i$ are measurable, and the payments are integrable under the prior.
--
--   The **expected revenue** of $M$ is $\mathcal R^M = \mathbb E_{\mathbf v}\big[\sum_i \pi_i(\mathbf v)\big]$, and the **service probability** of agent $i$ is $q^M_i = \Pr_{\mathbf v}[i \in M(\mathbf v)]$. The **virtual surplus** of a set $S$ at $\mathbf v$ is $\Phi(S, \mathbf v) = \sum_{i \in S} \phi_i(v_i)$ (Definition 1).
--
--   **Formalization Note** "Truthful" is read as dominant-strategy incentive compatible and ex-post individually rational. Payments of unserved agents are not forced to be zero. The measurability and integrability clauses only make the expectations meaningful.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1; p. 5, Lemma 2 (q^M_i); p. 12, Definition 1 (virtual surplus)

import Mathlib
import Definitions.Def_CHMSPricing_SpmMatroid_ValueDist
import Definitions.Def_CHMSPricing_SpmMatroid_SetSystem

namespace CHMSPricing.SpmMatroid

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

/-- `q^M_i`: the probability over `v ∼ F` that `M` serves agent `i`. -/
noncomputable def servProb (D : ι → ValueDist) (M : Mechanism ι) (i : ι) : ℝ :=
  (prior D {v | i ∈ M.alloc v}).toReal

/-- Definition 1 (p. 12): the virtual surplus `Φ(S, v) = ∑_{i ∈ S} φᵢ(vᵢ)` of a set `S`. -/
noncomputable def virtualSurplus (D : ι → ValueDist) (S : Finset ι) (v : ι → ℝ) : ℝ :=
  ∑ i ∈ S, (D i).virtualValue (v i)

end CHMSPricing.SpmMatroid


