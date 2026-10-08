-- Prove2me | Definitions.Def_ChoiceRM_MNL_Dominance
-- name    : ChoiceRM_MNL_Dominance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:29.62656+00:00
-- url     : https://prove2.me/theorems/bb7669bf-b38f-4c7a-b2d2-80c171afa94c
-- title:
--   Definition 1, p. 8 — dominated and nondominated offer sets
-- statement:
--   Fix $n$ fare products $N = \{1, \dots, n\}$, a choice model $P_j(S)$ (the probability that an arriving customer buys product $j$ when the set $S \subseteq N$ is offered) and revenues $r_1, \dots, r_n$. Write $Q(S) = \sum_{j \in S} P_j(S)$ for the purchase probability and $R(S) = \sum_{j \in S} P_j(S) r_j$ for the expected revenue of the offer set $S$.
--
--   A set $T \subseteq N$ is **dominated** if there are probabilities $\alpha(S) \ge 0$, $S \subseteq N$, with $\sum_{S} \alpha(S) = 1$, such that either
--
--   $$
--   \sum_{S} \alpha(S) Q(S) \le Q(T) \quad\text{and}\quad \sum_{S} \alpha(S) R(S) > R(T),
--   $$
--
--   or
--
--   $$
--   \sum_{S} \alpha(S) Q(S) < Q(T) \quad\text{and}\quad \sum_{S} \alpha(S) R(S) \ge R(T).
--   $$
--
--   A set is **nondominated** if it is not dominated. A randomization over offer sets that uses no more capacity in expectation and earns strictly more, or uses strictly less capacity and earns no less, makes the dominated set $T$ unattractive in the dynamic program.
--
--   **Formalization Note** The choice model is a function `P : Finset (Fin n) → Fin n → ℝ`, products are indexed $0, \dots, n-1$, and $Q$, $R$ are `purchaseProb` and `expRevenue` of the published definition `RevenueManagement_singleResource`. The randomization $\alpha$ ranges over all subsets of $N$. This file is shared, with identical names and bodies, with the other missions of this series.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 8, Definition 1

import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace ChoiceRM.MNL

open RevenueManagement

variable {n : ℕ}

/-- Definition 1 (p. 8): `T` is dominated if a distribution over offer sets has either
no larger purchase probability and strictly larger revenue, or strictly smaller purchase
probability and no smaller revenue. -/
def IsDominated (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (T : Finset (Fin n)) : Prop :=
  ∃ α : Finset (Fin n) → ℝ, (∀ S, 0 ≤ α S) ∧ ∑ S, α S = 1 ∧
    ((∑ S, α S * purchaseProb P S ≤ purchaseProb P T ∧
        expRevenue P r T < ∑ S, α S * expRevenue P r S) ∨
      (∑ S, α S * purchaseProb P S < purchaseProb P T ∧
        expRevenue P r T ≤ ∑ S, α S * expRevenue P r S))

/-- Definition 1 (p. 8): a set is nondominated if it is not dominated. -/
def IsNondominated (P : Finset (Fin n) → Fin n → ℝ) (r : Fin n → ℝ) (T : Finset (Fin n)) : Prop :=
  ¬ IsDominated P r T

end ChoiceRM.MNL


