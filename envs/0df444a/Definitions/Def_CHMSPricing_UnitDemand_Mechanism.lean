-- Prove2me | Definitions.Def_CHMSPricing_UnitDemand_Mechanism
-- name    : CHMSPricing_UnitDemand_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:15:59.730517+00:00
-- url     : https://prove2.me/theorems/abcfc294-1c4e-43d8-a365-f652e3c05493
-- title:
--   Single-parameter mechanisms: truthfulness, revenue, service probabilities and the order-oblivious revenue $\mathcal R^{\mathrm{obl}}_{\mathbf p}$
-- statement:
--   In the Bayesian single-parameter mechanism design problem (BSMD, §2.1, p. 4) there are finitely many agents $i$, each with a private value $v_i \sim F_i$ drawn independently, and a seller who may serve any feasible set of a set system $\mathcal J$. A deterministic **mechanism** $M$ maps a reported value vector $v$ to an allocation $M(v)$ (the set of served agents) and a payment $\pi_i(v)$ for each agent $i$. Agent $i$ with value $x$ facing reports $b$ has utility $x\cdot\mathbf 1[i \in M(b)] - \pi_i(b)$.
--
--   $M$ is **truthful** for $(F, \mathcal J)$ if, on the type space,
--   1. its allocation is feasible;
--   2. it is dominant-strategy incentive compatible: no agent gains by reporting any other value of its support, whatever the others report;
--   3. it is ex-post individually rational: every agent's utility is nonnegative;
--   4. its allocation events are measurable and its payments are measurable and integrable.
--
--   Its **expected revenue** is $\mathcal R^M = \mathbb E_v[\sum_i \pi_i(v)]$ and $q^M_i = \Pr_v[i \in M(v)]$ is the probability that it serves agent $i$.
--
--   For prices $p$, the **order-oblivious revenue** (§2.2, p. 4) is the pessimistic estimate of the revenue of an order-oblivious posted-price mechanism (OPM)
--   $$\mathcal R^{\mathrm{obl}}_{\mathbf p} = \mathbb E_{v \sim F}\Big[\min_{S \in \mathcal S_v} \sum_{i \in S} p_i\Big],$$
--   the minimum over the maximal feasible sets of agents desiring service.
--
--   These are the objects of the single-parameter instance with copies, $\mathcal I^{\mathrm{copies}}$, to which the multi-parameter problem is reduced.
--
--   **Formalization Note** Truthfulness bundles dominant-strategy incentive compatibility with deviations inside the support, ex-post individual rationality and the measurability and integrability needed for the expectations (pin P3). Myerson's mechanism is not constructed; statements that compare against it quantify over every truthful mechanism instead (pin P4).
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1 (BSMD) and §2.2 (order-oblivious posted prices, $\mathcal R^{\mathrm{obl}}_{\mathbf p}$); p. 5, Lemma 2 ($q^M_i$)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_ValueDist
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem

namespace CHMSPricing.UnitDemand

open MeasureTheory

/-- A deterministic direct mechanism for single-parameter agents `ι` (BSMD, §2.1, p. 4): it maps
a reported value profile `v` to an allocation `M(v)` (the set of served agents) and a payment
`πᵢ(v)` for each agent. -/
structure Mechanism (ι : Type*) where
  alloc : (ι → ℝ) → Finset ι
  pay : (ι → ℝ) → ι → ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Quasilinear utility of single-parameter agent `i` with true value `x` when the reported
profile is `b`. -/
noncomputable def Mechanism.utility (M : Mechanism ι) (i : ι) (x : ℝ) (b : ι → ℝ) : ℝ :=
  (if i ∈ M.alloc b then x else 0) - M.pay b i

/-- A truthful (dominant-strategy incentive compatible), ex-post individually rational
single-parameter mechanism respecting the feasibility constraint `J` on the type space, with
measurable allocation events and measurable, integrable payments (standing pin P3). -/
structure IsTruthful (D : ι → ValueDist) (J : SetSystem ι) (M : Mechanism ι) : Prop where
  feasible : ∀ v ∈ typeSpace D, J.Feasible (M.alloc v)
  dsic : ∀ v ∈ typeSpace D, ∀ i, ∀ x' ∈ Set.Icc (D i).lo (D i).hi,
    M.utility i (v i) (Function.update v i x') ≤ M.utility i (v i) v
  ir : ∀ v ∈ typeSpace D, ∀ i, 0 ≤ M.utility i (v i) v
  alloc_measurable : ∀ i, MeasurableSet {v | i ∈ M.alloc v}
  pay_measurable : ∀ i, Measurable (fun v => M.pay v i)
  pay_integrable : ∀ i, Integrable (fun v => M.pay v i) (prior D)

/-- The expected revenue `𝔼_v[∑ᵢ πᵢ(v)]` of a single-parameter mechanism under the prior. -/
noncomputable def revenue (D : ι → ValueDist) (M : Mechanism ι) : ℝ :=
  ∫ v, ∑ i, M.pay v i ∂(prior D)

/-- `q^M_i`: the probability over `v ∼ F` that `M` serves agent `i`. -/
noncomputable def servProb (D : ι → ValueDist) (M : Mechanism ι) (i : ι) : ℝ :=
  (prior D {v | i ∈ M.alloc v}).toReal

/-- `ℛ^obl_p` (§2.2, p. 4): the pessimistic expected revenue of the order-oblivious posted-price
mechanism with prices `p`, `𝔼_v [min_{S ∈ 𝒮_v} ∑_{i ∈ S} pᵢ]`, the minimum taken over the
(nonempty, finite) class of maximal feasible desiring sets. -/
noncomputable def oblRevenue (D : ι → ValueDist) (J : SetSystem ι) (p : ι → ℝ) : ℝ :=
  ∫ v, (maxFeasDesiringSets J p v).inf' (maxFeasDesiringSets_nonempty J p v)
    (fun S => ∑ i ∈ S, p i) ∂(prior D)

end CHMSPricing.UnitDemand


