-- Prove2me | Definitions.Def_ChoiceRM_FareOrder_Systems
-- name    : ChoiceRM_FareOrder_Systems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:05.909329+00:00
-- url     : https://prove2.me/theorems/f5a840f1-d2c3-4014-b055-eab6a00e4258
-- title:
--   Proof of Theorem 2, p. 20 — the system (10)–(11), its Farkas dual, and mixtures over an arbitrary family
-- statement:
--   Throughout, $N = \{1, \dots, n\}$ is the set of fare products, indexed in fare order $r_1 \ge r_2 \ge \dots \ge r_n \ge 0$. A **choice model** assigns to every offer set $S \subseteq N$ and product $j$ a purchase probability $P_j(S) \ge 0$, with $P_j(S) = 0$ for $j \notin S$ and $Q(S) = \sum_{j \in S} P_j(S) \le 1$ (the no-purchase probability is $P_0(S) = 1 - Q(S)$). The **complete sets** are $A_k = \{1, \dots, k\}$ for $k = 0, 1, \dots, n$, with $A_0 = \emptyset$; every other set is **incomplete**.
--
--   Fix an offer set $T \subseteq N$. This file names three objects of the proof of Theorem 2 (pp. 20–21).
--
--   1. **The system (10)–(11) is unsolvable for $T$.** There are no values $x_1 \ge x_2 \ge \dots \ge x_n$ and no scalar $u$ such that
--
--   $$u < \sum_{j \in T} x_j P_j(T) \qquad\text{and}\qquad \sum_{j \in A_k} x_j P_j(A_k) \le u \quad (k = 0, 1, \dots, n).$$
--
--   In words: no fare-ordered values make $T$ earn strictly more in (9) than every complete set.
--
--   2. **The dual system is solvable for $T$.** There are weights $\alpha_0, \dots, \alpha_n \ge 0$ with $\sum_k \alpha_k = 1$ and numbers $z_0, \dots, z_n \ge 0$ with $z_0 = z_n = 0$ such that
--
--   $$\sum_{k=0}^n \alpha_k P_j(A_k) - z_j + z_{j-1} = P_j(T), \qquad j = 1, \dots, n.$$
--
--   3. **Mixture over a family.** For any family of offer sets $F_1, \dots, F_m$ and weights $\alpha \in \mathbb R^m$, $\;\sum_{k=1}^m \alpha_k P_j(F_k)$ (used for the remark on p. 21 that Theorem 2 holds for any specified family).
--
--   These are the intermediate objects of the paper's proof: Farkas' lemma links 1 and 2, and eliminating $z$ turns 2 into the majorization condition of Theorem 2.
--
--   **Formalization Note** Fare $j \in \{1, \dots, n\}$ is the element $j - 1$ of `Fin n`; the order $x_1 \ge \dots \ge x_n$ is `Antitone x`; $A_k$ is `complete n k`; the choice-model axioms are `IsChoiceModel P` (platform definition `RevenueManagement_singleResource`) together with `SupportedOn P` ($P_j(S) = 0$ off $S$, the model's own convention on p. 5). The variables $z_0, \dots, z_n$ are a vector indexed by `Fin (n + 1)`; $z_j$ for fare $j$ (0-based index $j-1$) is `z j.succ` and $z_{j-1}$ is `z j.castSucc`. The constraints (11) include $k = 0$ (the empty set, giving $u \ge 0$) because complete sets include $A_0 = \emptyset$; the page lists $k = 1, \dots, n$. The page writes the sums of (10)–(11) with index $k$ for $j$; they run over the products.
-- source:
--   Talluri, van Ryzin, Revenue management under a general discrete choice model of consumer behavior, working paper of October 21, 2001 (UPF Economics Working Paper 533; published Management Science 50(1), 2004, DOI 10.1287/mnsc.1030.0147), p. 20, proof of Theorem 2, eqs. (10)–(11) and the dual system; p. 21, remark after the proof

import Mathlib
import Definitions.Def_RevenueManagement_singleResource
import Definitions.Def_ChoiceRM_FareOrder_FareOrder

namespace ChoiceRM.FareOrder

open RevenueManagement

variable {n : ℕ}

/-- The linear system (10)–(11) of the proof of Theorem 2 (p. 20) has **no** solution for the
offer set `T`: there are no values `x_1 ≥ x_2 ≥ … ≥ x_n` and no scalar `u` with
`u < Σ_{j∈T} x_j P_j(T)` (10) and `Σ_{j∈A_k} x_j P_j(A_k) ≤ u` for every complete set
`A_k`, `k ∈ {0, …, n}` (11). In words: no fare-ordered values make `T` earn strictly more
than every complete set. -/
def NoStrictImprovement (P : Finset (Fin n) → Fin n → ℝ) (T : Finset (Fin n)) : Prop :=
  ¬ ∃ (x : Fin n → ℝ) (u : ℝ), Antitone x ∧ u < fareValue P x T ∧
      ∀ k ≤ n, fareValue P x (complete n k) ≤ u

/-- The dual system of the proof of Theorem 2 (p. 20) is solvable for the offer set `T`:
there are weights `α_k ≥ 0`, `k ∈ {0, …, n}`, with `Σ_k α_k = 1`, and `z_0, …, z_n ≥ 0` with
`z_0 = z_n = 0`, such that `Σ_k α_k P_j(A_k) − z_j + z_{j−1} = P_j(T)` for `j = 1, …, n`.
Fare `j ∈ {1, …, n}` is the index `i : Fin n` with `i.val + 1 = j`, so `z_j` is `z i.succ` and
`z_{j−1}` is `z i.castSucc` (in the Lean statement below the bound variable `i` is named `j`). -/
def DualSolvable (P : Finset (Fin n) → Fin n → ℝ) (T : Finset (Fin n)) : Prop :=
  ∃ α : Fin (n + 1) → ℝ, ∃ z : Fin (n + 1) → ℝ,
    (∀ k, 0 ≤ α k) ∧ (∀ j, 0 ≤ z j) ∧ z 0 = 0 ∧ z (Fin.last n) = 0 ∧ ∑ k, α k = 1 ∧
      ∀ j : Fin n, mixProb P α j - z j.succ + z j.castSucc = P T j

/-- The mixture `Σ_k α_k P_j(F_k)` over an arbitrary specified family of offer sets
`F_1, …, F_m` (remark after the proof of Theorem 2, p. 21). -/
def familyMixProb (P : Finset (Fin n) → Fin n → ℝ) {m : ℕ} (F : Fin m → Finset (Fin n))
    (α : Fin m → ℝ) (j : Fin n) : ℝ :=
  ∑ k : Fin m, α k * P (F k) j

end ChoiceRM.FareOrder


