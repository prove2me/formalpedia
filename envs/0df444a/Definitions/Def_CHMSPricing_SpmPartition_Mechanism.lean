-- Prove2me | Definitions.Def_CHMSPricing_SpmPartition_Mechanism
-- name    : CHMSPricing_SpmPartition_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T11:23:26.470927+00:00
-- url     : https://prove2.me/theorems/4f909838-44c1-45e0-a3f5-6b601f210884
-- title:
--   Deterministic single-parameter mechanisms: truthfulness, individual rationality, revenue and service probabilities
-- statement:
--   A (deterministic, direct) **mechanism** $M$ for single-parameter agents maps a reported value vector $\mathbf v$ to an allocation $M(\mathbf v)$, the set of served agents, and a payment $\pi_i(\mathbf v)$ for each agent $i$. An agent with true value $x$ facing reports $\mathbf b$ has quasilinear utility $x\cdot\mathbf 1[i\in M(\mathbf b)]-\pi_i(\mathbf b)$.
--
--   Given value distributions $F_i$ and a feasibility constraint $\mathcal J$, $M$ is **truthful** (in the sense used here) if, on the type space $\prod_i[\underline v_i,\bar v_i]$:
--   1. it is feasible: $M(\mathbf v)\in\mathcal J$;
--   2. it is dominant-strategy incentive compatible: no agent gains by misreporting any value in its support, whatever the others report;
--   3. it is ex-post individually rational: every agent's utility is non-negative;
--   4. the events $\{i\in M(\mathbf v)\}$ are measurable and the payments are measurable and integrable under the prior.
--
--   The **expected revenue** is $\mathcal R^M=\mathbb E_{\mathbf v}\big[\sum_i\pi_i(\mathbf v)\big]$, and the **service probability** of agent $i$ is $q^M_i=\Pr_{\mathbf v}[i\in M(\mathbf v)]$. The virtual surplus of a set $S$ is $\Phi(S,\mathbf v)=\sum_{i\in S}\varphi_i(v_i)$ (Definition 1).
--
--   **Formalization Note** The paper's "truthful mechanism" is formalised as dominant-strategy IC plus ex-post IR; without individual rationality revenue would be unbounded. Payments of unserved agents are allowed to be negative, as the paper does not exclude it.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1 (mechanism, allocation, pricing); p. 5, Lemma 2 (q^M_i); p. 12, Definition 1 (virtual surplus)

import Mathlib
import Definitions.Def_CHMSPricing_SpmPartition_ValueDist
import Definitions.Def_CHMSPricing_SpmPartition_SetSystem

namespace CHMSPricing.SpmPartition

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

end CHMSPricing.SpmPartition


