-- Prove2me | Definitions.Def_TalluriMNLFull_Policy_Control
-- name    : TalluriMNLFull_Policy_Control
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T13:59:31.740443+00:00
-- url     : https://prove2.me/theorems/caf9bfff-6a47-43c9-9d14-955cce270c4f
-- title:
--   Markov offer policies, achieved revenue, and fare-order nesting
-- statement:
--   Let $N$ be a finite product set, $a$ an arrival probability, $P_j(S)$ the probability of choosing product $j$ conditional on an arrival and offer $S$, and $r_j$ its fare. Write $Q(S)=\sum_{j\in S}P_j(S)$ and $R(S)=\sum_{j\in S}r_jP_j(S)$, using the published definitions. A deterministic Markov rule $\pi_t(x)$ chooses an offer set from the periods $t$ and capacity $x$ remaining. Admissibility requires $\pi_t(0)=\emptyset$.
--
--   Its achieved revenue has boundaries $J^\pi_0(x)=J^\pi_t(0)=0$ and, for $t,x\ge1$,
--   $$
--   J^\pi_t(x)=aR(\pi_t(x))+aQ(\pi_t(x))J^\pi_{t-1}(x-1)+(1-aQ(\pi_t(x)))J^\pi_{t-1}(x).
--   $$
--   This recurrence contains no optimization and does not call the Bellman value. For indices $k_t(x)\in\{0,\ldots,n\}$ the prefix policy offers the already published complete set $A_{k_t(x)}$. Fare-order nesting on a rectangle $0\le t\le H$, $0\le x\le C$ requires this representation and an index nondecreasing in capacity for each time.
--
--   A randomized Markov rule $\mu_{t,x}(S)$ assigns nonnegative probabilities summing to one over all offer sets at every state, with unit mass at $\emptyset$ when capacity is zero. Its achieved revenue $J^\mu$ has the same zero boundaries and averages the same sale/no-sale expression over $S$:
--   $$
--   J^\mu_t(x)=\sum_{S\subseteq N}\mu_{t,x}(S)\big[aR(S)+aQ(S)J^\mu_{t-1}(x-1)+(1-aQ(S))J^\mu_{t-1}(x)\big].
--   $$
--   The policy definitions apply to every finite choice model. No MNL-specific assumption is bundled into them. Three definitional bridges identify the two published namespaces' identical complete-set, nondominance, and static fare-order predicates. No copy of an existing model, maximum, or dominance definition is introduced.
-- source:
--   Talluri and van Ryzin, Revenue Management Under a General Discrete Choice Model of Consumer Behavior, UPF Economics Working Paper 533, October 21, 2001, Model §1 p. 5; equations (1)–(3) p. 7; Markov and randomized policies p. 8; Definition 3 p. 15; complete sets p. 17, printed p. 7 (PDF p. 7), https://econ-papers.upf.edu/papers/533.pdf; PDF SHA-256 053050fd8f6c12672e0e41e7782705b4f3a78b906f24bb52c7697a6d8c453c2c.

import Mathlib
import Definitions.Def_ChoiceRM_Policy_Value
import Definitions.Def_ChoiceRM_MNL_Models
import Definitions.Def_ChoiceRM_MNL_Dominance
import Definitions.Def_ChoiceRM_FareOrder_FareOrder

namespace TalluriMNLFull.Policy

open RevenueManagement

/-- A deterministic Markov offer rule, indexed by periods and capacity remaining
(p. 8). Admissibility at zero inventory is stated separately. -/
def MarkovPolicy (n : ℕ) := ℕ → ℕ → Finset (Fin n)

def IsAdmissible {n : ℕ} (π : MarkovPolicy n) : Prop :=
  ∀ t, π t 0 = ∅

/-- Revenue actually earned by a policy in the model of pp. 5–8. This recursion
does not use the Bellman value or optimize over offers. -/
noncomputable def policyRevenue {n : ℕ} (a : ℝ)
    (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (π : MarkovPolicy n) :
    ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | t + 1, x + 1 =>
      a * expRevenue P r (π (t + 1) (x + 1)) +
      a * purchaseProb P (π (t + 1) (x + 1)) * policyRevenue a P r π t x +
      (1 - a * purchaseProb P (π (t + 1) (x + 1))) * policyRevenue a P r π t (x + 1)

/-- The fixed fare-order family A_0,...,A_n from pp. 17–18, applied to one
index function. The requirement k_t(0)=0 is a conclusion of the goal. -/
def prefixPolicy {n : ℕ} (k : ℕ → ℕ → Fin (n + 1)) : MarkovPolicy n :=
  fun t x => ChoiceRM.MNL.complete n (k t x).val

/-- Definition 3 (p. 15), specialized to the fixed fare-order family. The same
index function works at all states in the finite horizon/capacity rectangle. -/
def IsFareOrderNested {n : ℕ} (H C : ℕ) (π : MarkovPolicy n)
    (k : ℕ → ℕ → Fin (n + 1)) : Prop :=
  (∀ t x, t ≤ H → x ≤ C → π t x = ChoiceRM.MNL.complete n (k t x).val) ∧
    ∀ t, t ≤ H → ∀ x y, x ≤ y → y ≤ C → (k t x).val ≤ (k t y).val

/-- A randomized Markov rule (p. 8), distributing mass over every offer set. -/
def RandomizedPolicy (n : ℕ) := ℕ → ℕ → Finset (Fin n) → ℝ

def IsRandomizedPolicy {n : ℕ} (μ : RandomizedPolicy n) : Prop :=
  (∀ t x S, 0 ≤ μ t x S) ∧ (∀ t x, ∑ S, μ t x S = 1) ∧
    (∀ t, μ t 0 ∅ = 1)

/-- Achieved revenue of a randomized rule, averaging the source's one-step
sale/no-sale recurrence. Zero horizon and zero capacity have value zero. -/
noncomputable def randomizedRevenue {n : ℕ} (a : ℝ)
    (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (μ : RandomizedPolicy n) :
    ℕ → ℕ → ℝ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | t + 1, x + 1 =>
      ∑ S, μ (t + 1) (x + 1) S *
        (a * expRevenue P r S +
          a * purchaseProb P S * randomizedRevenue a P r μ t x +
          (1 - a * purchaseProb P S) * randomizedRevenue a P r μ t (x + 1))

/-- The two published complete-set definitions have exactly the same body. -/
theorem complete_namespaces_agree (n k : ℕ) :
    ChoiceRM.MNL.complete n k = ChoiceRM.FareOrder.complete n k := rfl

/-- The two published dominance predicates have exactly the same body. -/
theorem nondominated_namespaces_agree {n : ℕ}
    (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (S : Finset (Fin n)) :
    ChoiceRM.MNL.IsNondominated P r S ↔ ChoiceRM.Policy.IsNondominated P r S := Iff.rfl

/-- Definition 4 is shared, without changing the domain of ordered real scores. -/
theorem fare_order_namespaces_agree {n : ℕ} (P : Finset (Fin n) → Fin n → ℝ) :
    ChoiceRM.MNL.HasFareOrderNesting P ↔ ChoiceRM.FareOrder.HasFareOrderNesting P := Iff.rfl

end TalluriMNLFull.Policy


