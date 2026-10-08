-- Prove2me | Definitions.Def_ChoiceRM_FareOrder_FareOrder
-- name    : ChoiceRM_FareOrder_FareOrder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:44:50.754979+00:00
-- url     : https://prove2.me/theorems/0b1564b9-2acb-4264-9dce-baf5f10c0b47
-- title:
--   Definition 4, p. 18 — complete sets, objective (9), the nesting-by-fare-order property, and the mixture P̄(α)
-- statement:
--   Fix $n$ fare products $N = \{1, \dots, n\}$ and a choice model $P_j(S)$ ($S \subseteq N$, $j \in N$): $P_j(S) \ge 0$ is the probability that an arriving customer buys product $j$ when the set $S$ is offered, and $Q(S) = \sum_{j \in S} P_j(S) \le 1$ is the probability of a purchase.
--
--   This file defines the objects of §3.2 of the paper.
--
--   1. **Support convention.** $P_j(S) = 0$ whenever $j \notin S$ (§1, p. 5).
--   2. **Complete sets.** $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$ (p. 17), with $A_0 = \emptyset$. A set $T$ is *complete* if $T = A_k$ for some $0 \le k \le n$, and *incomplete* otherwise.
--   3. **Objective of (9).** For values $x = (x_1, \dots, x_n)$ and an offer set $S$, $\;\sum_{j \in S} x_j P_j(S)$.
--   4. **Nesting by fare order** (Definition 4, p. 18). The choice model has the nesting-by-fare-order property if (i) $Q$ is increasing, $Q(S) \le Q(T)$ whenever $S \subseteq T$, and (ii) for every $x_1 \ge x_2 \ge \dots \ge x_n$ the problem
--
--   $$\max_{S \subseteq N} \sum_{j=1}^n x_j P_j(S) \tag{9}$$
--
--   has an optimal solution that is complete: some $A_k$ attains the maximum.
--
--   5. **Mixture of complete sets** (Theorem 2, p. 19). For weights $\alpha = (\alpha_0, \dots, \alpha_n)$, $\;\bar P_j(\alpha) = \sum_{k=0}^{n} \alpha_k P_j(A_k)$.
--
--   These are the objects of the paper's characterization of choice models for which an optimal revenue-management policy opens fares in fare order.
--
--   **Formalization Note** Fare $j \in \{1, \dots, n\}$ is the element $j - 1$ of `Fin n`; the order $x_1 \ge \dots \ge x_n$ is `Antitone x`; $A_k$ is `complete n k`; the choice-model axioms are `IsChoiceModel P` (platform definition `RevenueManagement_singleResource`) together with `SupportedOn P` ($P_j(S) = 0$ off $S$, the model's own convention on p. 5). Complete sets are indexed by $k \in \{0, \dots, n\}$, so $A_0 = \emptyset$ counts as complete and the weights $\alpha$ live on $n + 1$ sets. The page indexes the weights by $k = 1, \dots, n$; the paper notes on p. 21 that Theorem 2 holds for any specified family of sets, and with $A_0$ included the property is the one the paper's Propositions 5 and 6 need (for MNL and all $x_j < 0$, the unique optimum of (9) is $\emptyset$). The maximum in (9) is over all subsets $S \subseteq N$ (the page writes $S \subset N$ for $\subseteq$).
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 5 (§1, P_j(S) = 0 for j ∉ S); p. 17 (complete sets A_k); p. 18, Definition 4 and eq. (9); p. 19, Theorem 2 (P̄_j(α))

import Mathlib
import Definitions.Def_RevenueManagement_singleResource

namespace ChoiceRM.FareOrder

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

end ChoiceRM.FareOrder


