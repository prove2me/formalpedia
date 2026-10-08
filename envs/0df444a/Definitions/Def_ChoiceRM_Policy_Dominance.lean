-- Prove2me | Definitions.Def_ChoiceRM_Policy_Dominance
-- name    : ChoiceRM_Policy_Dominance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:45.236976+00:00
-- url     : https://prove2.me/theorems/9fb14be5-6628-4bdf-a524-b6fc85b1b07d
-- title:
--   Definition 1, p. 8 — dominated and nondominated offer sets
-- statement:
--   Let $N$ be a finite set of fare products. For an offer set $S\subseteq N$, write $Q(S)$ for its purchase probability and $R(S)$ for its expected revenue. A set $T$ is **dominated** if there are nonnegative weights $\alpha(S)$ summing to one such that either
--
--   $$\sum_S\alpha(S)Q(S)\le Q(T)\quad\text{and}\quad R(T)<\sum_S\alpha(S)R(S),$$
--
--   or
--
--   $$\sum_S\alpha(S)Q(S)<Q(T)\quad\text{and}\quad R(T)\le\sum_S\alpha(S)R(S).$$
--
--   A set is **nondominated** when neither kind of randomization dominates it. This is the frontier on which the optimal offer policy can be sought.
--
--   **Formalization Note** The distribution ranges over all subsets, including the empty set, as in Definition 1.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 8, Definition 1

import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace ChoiceRM.Policy

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

end ChoiceRM.Policy


