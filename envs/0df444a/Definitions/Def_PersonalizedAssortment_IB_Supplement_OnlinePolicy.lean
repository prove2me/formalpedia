-- Prove2me | Definitions.Def_PersonalizedAssortment_IB_Supplement_OnlinePolicy
-- name    : PersonalizedAssortment_IB_Supplement_OnlinePolicy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T10:26:46.754272+00:00
-- url     : https://prove2.me/theorems/827a021a-512e-4d1b-bceb-ed8334e84e5d
-- title:
--   Definition 1, p. 1536 — deterministic and randomized online algorithms and their expected revenue $\mathrm{Rev}_A(\{z_t\})$
-- statement:
--   A firm sells products $0,1,\dots,n-1$ (the paper numbers them $1,\dots,n$) with per-unit revenues $r_i$ and initial inventories $c_i$, and faces customers of types $z_1,z_2,\dots,z_T$ from a type set $\mathcal Z$, arriving one per period. A customer of type $z$ offered the assortment $S$ picks product $i\in S$ with probability $\varphi_i^z(S)$ and nothing with probability $1-\sum_{i\in S}\varphi_i^z(S)$.
--
--   A **deterministic online algorithm** $\pi$ chooses, in period $t$, an assortment
--   $$S^t=\pi\big((z_1,\dots,z_t),\,(\xi^1,\dots,\xi^{t-1})\big)$$
--   from the types that have arrived so far, the current one included, and the outcomes $\xi^s$ of the earlier customers, where $\xi^s$ is either "no purchase" or the product the customer picked. It never sees future types. It is **feasible** for a family $\mathcal S$ of assortments if it always offers some $S\in\mathcal S$.
--
--   The **expected revenue** $\mathrm{Rev}_\pi(\{z_t\}_{t=1}^T)$ of Definition 1 is computed by conditioning on the history. A pick of product $i$ earns $r_i$ exactly when $i$ is still in stock, that is, when $c_i$ minus the earlier sales of $i$ is positive, and then lowers the inventory of $i$ by one. A pick of a stocked-out product earns nothing and leaves the inventory at zero, as in $I_i^t=\max\{I_i^{t-1}-Q_i^t,0\}$. The expectation is over the customers' choices.
--
--   A **randomized online algorithm** $A$ is a probability distribution, fixed before any customer arrives, over finitely many deterministic online algorithms $\pi_1,\dots,\pi_K$ with weights $w_k\ge 0$ and $\sum_k w_k=1$. Its expected revenue is
--   $$\mathrm{Rev}_A(\{z_t\})=\sum_{k=1}^K w_k\,\mathrm{Rev}_{\pi_k}(\{z_t\}),$$
--   the expectation now also covering the algorithm's own randomization.
--
--   These objects are the algorithms over which the paper's upper bounds (Lemma 3, Theorem 2) quantify. The inventory-balancing algorithm is one such deterministic online algorithm.
--
--   **Formalization Note** Histories are Lean lists in arrival order. The policy observes a pick of a stocked-out product, which only gives it more information. Feasibility is required on every history, reachable or not. Since $\emptyset\in\mathcal S$, a policy that is feasible on the reachable histories can be changed off them without changing its revenue. On an instance with finitely many types, finitely many products and a fixed horizon, the restriction of a deterministic policy to the histories of length at most $T$ takes finitely many values. So every distribution over deterministic online policies has the revenue of a finite mixture, and by Kuhn's theorem (perfect recall) so does every algorithm that randomizes period by period.
-- source:
--   Golrezaei, Nazerzadeh, Rusmevichientong, Real-Time Optimization of Personalized Assortments, Management Sci. 60(6), 2014, https://doi.org/10.1287/mnsc.2014.1939, p. 1536, Definition 1 (and §2, "the algorithm does not know the sequence of the customers in advance"); p. 1537, inventory dynamics I_i^t = max{I_i^{t-1} − Q_i^t, 0}; p. 1548, §A.2 (S^t depends on S^1, …, S^{t−1} and ξ^1, …, ξ^{t−1})

import Mathlib
import Definitions.Def_PersonalizedAssortment_IB_ChoiceModel

namespace PersonalizedAssortment.IB.Supplement

open PersonalizedAssortment.IB

/-- A deterministic online algorithm (Definition 1, p. 1536: "the algorithm does not know the
sequence of the customers in advance"; §A.2, p. 1548: `S^t` may depend on `S^1, …, S^{t-1}` and
`ξ^1, …, ξ^{t-1}`). In each period the policy sees the types `z_1, …, z_t` that have arrived so far
(in arrival order, the current customer last) and the outcomes `ξ^1, …, ξ^{t-1}` of the earlier
customers (`none` = no purchase, `some i` = the customer picked product `i`), and offers an
assortment. It never sees future types. -/
structure OnlinePolicy (n : ℕ) (Z : Type*) where
  /-- `offer [z_1, …, z_t] [ξ^1, …, ξ^{t-1}] = S^t`. -/
  offer : List Z → List (Option (Fin n)) → Finset (Fin n)

/-- The policy only offers feasible assortments `S ∈ 𝒮`. -/
def OnlinePolicy.IsFeasible {n : ℕ} {Z : Type*} (𝒮 : Finset (Finset (Fin n)))
    (π : OnlinePolicy n Z) : Prop :=
  ∀ zs ξs, π.offer zs ξs ∈ 𝒮

/-- Expected revenue collected from the customers `future` (in arrival order) by the policy `π`,
given the types `past` already seen, the outcomes `hist` already observed and the current
inventories `I`. The current customer `z` is offered `S = π.offer (past ++ [z]) hist`; she picks
`i ∈ S` with probability `φ_i^z(S)` and nothing with probability `1 - ∑_{i ∈ S} φ_i^z(S)`. A pick of
`i` earns `r_i` exactly when `I_i > 0`, and the inventory becomes `max{I_i - 1, 0}`; the policy
observes the pick in both cases. -/
noncomputable def revAux {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (φ : Z → ChoiceModel n)
    (π : OnlinePolicy n Z) :
    List Z → List Z → List (Option (Fin n)) → (Fin n → ℕ) → ℝ
  | _, [], _, _ => 0
  | past, z :: future, hist, I =>
      (1 - ∑ i ∈ π.offer (past ++ [z]) hist, (φ z).prob (π.offer (past ++ [z]) hist) i) *
          revAux r φ π (past ++ [z]) future (hist ++ [none]) I +
        ∑ i ∈ π.offer (past ++ [z]) hist, (φ z).prob (π.offer (past ++ [z]) hist) i *
          ((if 0 < I i then r i else 0) +
            revAux r φ π (past ++ [z]) future (hist ++ [some i]) (Function.update I i (I i - 1)))

/-- `Rev_π({z_t}_{t=1}^T)` (Definition 1, p. 1536): the expected revenue of the deterministic online
policy `π` on the arrival sequence `z` (period `t` of the paper is index `t - 1`), starting from the
initial inventories `c`, the expectation being over the customers' choices. -/
noncomputable def policyRevenue {n : ℕ} {Z : Type*} (r : Fin n → ℝ) (c : Fin n → ℕ)
    (φ : Z → ChoiceModel n) (π : OnlinePolicy n Z) {T : ℕ} (z : Fin T → Z) : ℝ :=
  revAux r φ π [] (List.ofFn z) [] c

/-- A randomized online algorithm: a probability distribution, chosen before any customer
arrives, over finitely many deterministic online policies `pol k` with weights `w k`. -/
structure RandomizedPolicy (n : ℕ) (Z : Type*) where
  /-- Index set of the deterministic policies in the support. -/
  ι : Type
  [fin : Fintype ι]
  /-- Probability of running `pol k`. -/
  w : ι → ℝ
  /-- The deterministic online policies. -/
  pol : ι → OnlinePolicy n Z
  w_nonneg : ∀ k, 0 ≤ w k
  w_sum : ∑ k, w k = 1

attribute [instance] RandomizedPolicy.fin

/-- Every policy in the support offers only feasible assortments. -/
def RandomizedPolicy.IsFeasible {n : ℕ} {Z : Type*} (𝒮 : Finset (Finset (Fin n)))
    (A : RandomizedPolicy n Z) : Prop :=
  ∀ k, (A.pol k).IsFeasible 𝒮

/-- Expected revenue of a randomized online algorithm, over its own randomization and the
customers' choices: `∑_k w_k Rev_{π_k}({z_t})`. -/
noncomputable def RandomizedPolicy.revenue {n : ℕ} {Z : Type*} (A : RandomizedPolicy n Z)
    (r : Fin n → ℝ) (c : Fin n → ℕ) (φ : Z → ChoiceModel n) {T : ℕ} (z : Fin T → Z) : ℝ :=
  ∑ k, A.w k * policyRevenue r c φ (A.pol k) z

end PersonalizedAssortment.IB.Supplement


