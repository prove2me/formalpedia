-- Prove2me | Definitions.Def_CHMSPricing_UnitDemand_MultiMechanism
-- name    : CHMSPricing_UnitDemand_MultiMechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:16:14.18864+00:00
-- url     : https://prove2.me/theorems/fdf37868-46e5-4ad1-b498-d978c204c0b7
-- title:
--   The Bayesian multi-parameter unit-demand setting: mechanisms, truthfulness, individual rationality, revenue and weak monotonicity
-- statement:
--   In the Bayesian multi-parameter unit-demand setting (BMUMD, §2.1, p. 4) there are $m$ buyers and a finite set $J$ of services, partitioned into groups $J_i = \{j : \mathrm{owner}(j) = i\}$, the services targeted at buyer $i$. Buyer $i$ has value $v_j$ for each service $j \in J_i$; the values are independent with $v_j \sim F_j$. The seller faces a set system $\mathcal J \subseteq 2^J$ that is **unit-demand**: $|S \cap J_i| \le 1$ for every feasible $S$ and every buyer $i$.
--
--   A deterministic **mechanism** $\mathcal A$ maps the reported values $v$ to an allocation $\mathcal A(v) \subseteq J$ and a pricing $\pi(v)$, buyer $i$ paying $\pi_i(v)$. Write $v_{\mathcal A_i(b)}$ for the value, at values $v$, of the service of $J_i$ allocated at reports $b$ (zero if there is none). Buyer $i$'s utility is $v_{\mathcal A_i(b)} - \pi_i(b)$.
--
--   $\mathcal A$ is **truthful and individually rational** if, on the type space,
--   1. its allocation is feasible;
--   2. it is dominant-strategy incentive compatible: no buyer $i$ gains by misreporting its values for the services of $J_i$ (all of them at once), whatever the other buyers report;
--   3. it is individually rational in the paper's sense (p. 13): $\pi_i \le v_j$ for $j \in \mathcal A(v) \cap J_i$, and $\pi_i = 0$ if $\mathcal A(v) \cap J_i = \emptyset$;
--   4. its allocation events are measurable and its payments are measurable and integrable.
--
--   Its expected revenue is $\mathcal R^{\mathcal A} = \mathbb E_v[\sum_i \pi_i(v)]$.
--
--   **Definition 3** (weak monotonicity, p. 13). $\mathcal A$ is weakly monotone if for every buyer $i$ and all value vectors $v^1, v^2$ with $v^1_j = v^2_j$ for $j \in J \setminus J_i$,
--   $$v^1_{\mathcal A_i(v^1)} + v^2_{\mathcal A_i(v^2)} \ge v^1_{\mathcal A_i(v^2)} + v^2_{\mathcal A_i(v^1)}.$$
--
--   These are the benchmark mechanisms of Lemma 3, Theorem 4 and Theorem 14.
--
--   **Formalization Note** The unit-demand property is a separate predicate, assumed as a hypothesis by the theorems that need it. $v_{\mathcal A_i(b)}$ is the sum of $v_j$ over the allocated services of $J_i$; under unit demand there is at most one, so this is the paper's "unique index in $M(v) \cap J_i$", and $0$ when there is none. Weak monotonicity is required for value vectors in the type space.
-- source:
--   Chawla, Hartline, Malec and Sivan, Multi-parameter Mechanism Design and Sequential Posted Pricing, arXiv:0907.2435v2, p. 4, §2.1 (BMUMD); p. 13, App. B (individual rationality, Definition 3)

import Mathlib
import Definitions.Def_CHMSPricing_UnitDemand_ValueDist
import Definitions.Def_CHMSPricing_UnitDemand_SetSystem

namespace CHMSPricing.UnitDemand

open MeasureTheory

variable {J : Type*} [Fintype J] [DecidableEq J] {m : ℕ}

/-- BMUMD (§2.1, p. 4): the services `J` are partitioned into the groups
`Jᵢ = {j | owner j = i}` targeted at buyer `i`, and the set system is unit-demand: every
feasible set contains at most one service of each buyer (`|S ∩ Jᵢ| ≤ 1`). -/
def IsUnitDemand (𝒥 : SetSystem J) (owner : J → Fin m) : Prop :=
  ∀ S, 𝒥.Feasible S → ∀ i, (S.filter (fun j => owner j = i)).card ≤ 1

/-- A deterministic direct mechanism for the BMUMD with services `J` and buyers `Fin m`: it maps
the reported value vector `v = (v_j)_{j ∈ J}` to an allocation `M(v) ⊆ J` and a pricing
`π(v)`, with `πᵢ(v)` paid by buyer `i`. -/
structure MultiMechanism (J : Type*) (m : ℕ) where
  alloc : (J → ℝ) → Finset J
  pay : (J → ℝ) → Fin m → ℝ

/-- The value `v_{Mᵢ(b)}` buyer `i` obtains, at true values `v`, from the services of `Jᵢ` that
`A` allocates at reports `b` (`0` when none is allocated; under unit demand there is at most
one). -/
noncomputable def MultiMechanism.valueOf (A : MultiMechanism J m) (owner : J → Fin m)
    (i : Fin m) (v b : J → ℝ) : ℝ :=
  ∑ j ∈ (A.alloc b).filter (fun j => owner j = i), v j

/-- Quasilinear utility of buyer `i` with true values `v` when the reported profile is `b`. -/
noncomputable def MultiMechanism.utility (A : MultiMechanism J m) (owner : J → Fin m)
    (i : Fin m) (v b : J → ℝ) : ℝ :=
  A.valueOf owner i v b - A.pay b i

/-- A truthful (dominant-strategy incentive compatible), individually rational deterministic
mechanism for the BMUMD (standing pin P3):
* the allocation is feasible on the type space;
* DSIC: no buyer `i` gains by misreporting any values for its own services `Jᵢ` (all
  coordinates of `Jᵢ` at once), whatever the reports of the others;
* individual rationality as on p. 13: `πᵢ ≤ v_j` for `j ∈ M(v) ∩ Jᵢ`, and `πᵢ = 0` if
  `M(v) ∩ Jᵢ = ∅`;
* measurable allocation events and measurable, integrable payments. -/
structure IsTruthfulMulti (D : J → ValueDist) (𝒥 : SetSystem J) (owner : J → Fin m)
    (A : MultiMechanism J m) : Prop where
  feasible : ∀ v ∈ typeSpace D, 𝒥.Feasible (A.alloc v)
  dsic : ∀ v ∈ typeSpace D, ∀ i, ∀ b ∈ typeSpace D, (∀ j, owner j ≠ i → b j = v j) →
    A.utility owner i v b ≤ A.utility owner i v v
  ir_served : ∀ v ∈ typeSpace D, ∀ i, ∀ j ∈ A.alloc v, owner j = i → A.pay v i ≤ v j
  ir_unserved : ∀ v ∈ typeSpace D, ∀ i,
    (A.alloc v).filter (fun j => owner j = i) = ∅ → A.pay v i = 0
  alloc_measurable : ∀ j, MeasurableSet {v | j ∈ A.alloc v}
  pay_measurable : ∀ i, Measurable (fun v => A.pay v i)
  pay_integrable : ∀ i, Integrable (fun v => A.pay v i) (prior D)

/-- The expected revenue `ℛ^A = 𝔼_v[∑ᵢ πᵢ(v)]` of a BMUMD mechanism under the prior. -/
noncomputable def revenueMulti (D : J → ValueDist) (A : MultiMechanism J m) : ℝ :=
  ∫ v, ∑ i, A.pay v i ∂(prior D)

/-- Definition 3 (p. 13): weak monotonicity. For every buyer `i` and every two value vectors
`v¹, v²` of the type space that agree outside `Jᵢ`,
`v¹_{Mᵢ(v¹)} + v²_{Mᵢ(v²)} ≥ v¹_{Mᵢ(v²)} + v²_{Mᵢ(v¹)}`, where `v_{Mᵢ(b)}` is `valueOf`. -/
def WeaklyMonotone (D : J → ValueDist) (owner : J → Fin m) (A : MultiMechanism J m) : Prop :=
  ∀ i, ∀ v₁ ∈ typeSpace D, ∀ v₂ ∈ typeSpace D, (∀ j, owner j ≠ i → v₁ j = v₂ j) →
    A.valueOf owner i v₁ v₂ + A.valueOf owner i v₂ v₁ ≤
      A.valueOf owner i v₁ v₁ + A.valueOf owner i v₂ v₂

end CHMSPricing.UnitDemand


