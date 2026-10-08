-- Prove2me | Definitions.Def_ChoiceRM_MNL_FareOrder
-- name    : ChoiceRM_MNL_FareOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:45:33.775794+00:00
-- url     : https://prove2.me/theorems/03bce056-c2dc-4bd3-be6b-851b1e6cdfea
-- title:
--   Definition 4, p. 18 — complete sets and the nesting-by-fare-order property
-- statement:
--   Fare products $N = \{1, \dots, n\}$ are indexed so that $r_1 \ge r_2 \ge \dots \ge r_n$. A choice model assigns to each offer set $S \subseteq N$ purchase probabilities $P_j(S)$, with the convention $P_j(S) = 0$ for $j \notin S$. This file defines:
--
--   1. the **complete set** $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$ (with $A_0 = \emptyset$), and the predicate "$T$ is complete" ($T = A_k$ for some $k$); a set that is not complete is **incomplete**;
--   2. the objective of problem (9), $\sum_{j \in S} x_j P_j(S)$, for values $x_1, \dots, x_n$;
--   3. the **nesting-by-fare-order property** (Definition 4): (i) the purchase probability $Q(S) = \sum_{j\in S} P_j(S)$ is increasing, $Q(S) \le Q(T)$ whenever $S \subseteq T$; and (ii) for every $x_1 \ge x_2 \ge \dots \ge x_n$ the problem
--   $$
--   \max_{S \subseteq N} \sum_{j=1}^n x_j P_j(S) \qquad (9)
--   $$
--   has an optimal solution that is complete;
--   4. for convex weights $\alpha_0, \dots, \alpha_n$, the mixed probabilities $\bar P_j(\alpha) = \sum_{k=0}^n \alpha_k P_j(A_k)$ of Theorem 2.
--
--   In the paper's model, $x_j = r_j - v$ for an opportunity cost $v$, so property (ii) says the optimal offer set is always a top segment of the fare ladder.
--
--   **Formalization Note** Products are `Fin n` (index $j-1$ for fare $j$), $A_k$ is `complete n k = {j | j.val < k}`, and the order $x_1 \ge \dots \ge x_n$ is `Antitone x`. The empty set $A_0$ counts as complete, and the weights of $\bar P$ are indexed by $k \in \{0, \dots, n\}$; the page writes complete sets as $A_k$ "for some $k$" and indexes Theorem 2's weights by $k = 1, \dots, n$. Without $A_0$ property (ii) fails for every model with $n \ge 1$ when all $x_j < 0$, where only $\emptyset$ is optimal. The paper notes (p. 21) that Theorem 2 holds for any specified family of sets. The maximum in (9) is over all subsets of $N$. This file is shared, with identical names and bodies, with the other missions of this series.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), pp. 5, 17–19, §1 (P_j(S) = 0 for j ∉ S), complete sets (p. 17), Definition 4 (p. 18), Theorem 2 (p. 19)

import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace ChoiceRM.MNL

open RevenueManagement

variable {n : ℕ}

/-- The model's convention `P_j(S) = 0` for `j ∉ S` (§1, p. 5). -/
def SupportedOn (P : Finset (Fin n) → Fin n → ℝ) : Prop :=
  ∀ S j, j ∉ S → P S j = 0

/-- The complete set `A_k = {1, …, k}` (p. 17), here `{j | j.val < k}` on `Fin n`; `A_0 = ∅`. -/
def complete (n k : ℕ) : Finset (Fin n) := Finset.univ.filter (fun j => j.val < k)

/-- `T` is complete: `T = A_k` for some `k ∈ {0, …, n}`. -/
def IsComplete (T : Finset (Fin n)) : Prop := ∃ k ≤ n, T = complete n k

/-- The objective of (9): `Σ_{j∈S} x_j P_j(S)`. -/
def fareValue (P : Finset (Fin n) → Fin n → ℝ) (x : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  ∑ j ∈ S, x j * P S j

/-- Definition 4 (p. 18): (i) `Q` is increasing, `Q(S) ≤ Q(T)` for `S ⊆ T`; (ii) for every
`x_1 ≥ x_2 ≥ … ≥ x_n` problem (9) has an optimal solution that is complete. -/
def HasFareOrderNesting (P : Finset (Fin n) → Fin n → ℝ) : Prop :=
  (∀ S T : Finset (Fin n), S ⊆ T → purchaseProb P S ≤ purchaseProb P T) ∧
    ∀ x : Fin n → ℝ, Antitone x →
      ∃ k ≤ n, ∀ S : Finset (Fin n), fareValue P x S ≤ fareValue P x (complete n k)

/-- `P̄_j(α) = Σ_k α_k P_j(A_k)` (Theorem 2, p. 19), with the convex weights indexed by
`k ∈ {0, …, n}`. -/
def mixProb (P : Finset (Fin n) → Fin n → ℝ) (α : Fin (n + 1) → ℝ) (j : Fin n) : ℝ :=
  ∑ k : Fin (n + 1), α k * P (complete n k.val) j

end ChoiceRM.MNL


