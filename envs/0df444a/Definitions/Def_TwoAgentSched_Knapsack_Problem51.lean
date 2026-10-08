-- Prove2me | Definitions.Def_TwoAgentSched_Knapsack_Problem51
-- name    : TwoAgentSched_Knapsack_Problem51
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:38:16.505187+00:00
-- url     : https://prove2.me/theorems/c9520598-81f7-4fd8-b9b3-73bbc736b7fb
-- title:
--   Problem 5.1 — KNAPSACK with two constraints, and its binary language
-- statement:
--   **KNAPSACK** (Problem 5.1 of Agnetis, Mirchandani, Pacciarelli and Pacifici). An instance consists of a number $n\ge 0$ of items, two families of nonnegative integers $u_1,\dots,u_n$ and $w_1,\dots,w_n$, and two integers $b$ and $W$ (which may be negative). It is a **yes-instance** if there is a subset $S\subseteq\{1,\dots,n\}$ with
--
--   $$\sum_{i\in S}u_i\le b\qquad\text{and}\qquad\sum_{i\in S}w_i\ge W.$$
--
--   An instance is coded as the sequence of integers $n,u_1,\dots,u_n,w_1,\dots,w_n,b,W$, each written in binary (a minus sign for a negative number, then the binary digits, then a separator symbol). Since $n$ comes first, the code determines the instance. The **KNAPSACK language** is the set of codes of yes-instances.
--
--   KNAPSACK is the source problem of the reduction proving Theorem 5.2 (the paper cites its NP-completeness from Garey and Johnson 1979; that fact is not part of this definition).
--
--   **Formalization Note** Items are indexed by `Fin n` (0-based). The alphabet `BSym` and the binary codes `encInt`/`encInts` are the published definitions of `ProjSchedTW.Complexity.Encoding` (Neumann, Schwindt and Zimmermann series). This is the two-constraint knapsack problem of the paper, not subset sum.
-- source:
--   Agnetis, Mirchandani, Pacciarelli & Pacifici, Scheduling Problems with Two Competing Agents, Oper. Res. 52(2) (2004), p. 233, Problem 5.1

import Mathlib
import Definitions.Def_ProjSchedTW_Complexity_Encoding

namespace TwoAgentSched.Knapsack

open CookPvsNP ProjSchedTW.Complexity

/-- Problem 5.1, KNAPSACK (Agnetis, Mirchandani, Pacciarelli & Pacifici 2004, p. 233): given
nonnegative integers `u_1, …, u_n` and `w_1, …, w_n` (here `u w : Fin n → ℕ`, 0-based: the
paper's `u_1` is `u 0`) and two integers `b` and `W`, is there a subset `S ⊆ {1, …, n}` such that
`∑_{i ∈ S} u_i ≤ b` and `∑_{i ∈ S} w_i ≥ W`? The integers `b`, `W` may be negative. -/
def KnapsackYes {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ) : Prop :=
  ∃ S : Finset (Fin n), ((∑ i ∈ S, u i : ℕ) : ℤ) ≤ b ∧ W ≤ ((∑ i ∈ S, w i : ℕ) : ℤ)

/-- The binary code of a KNAPSACK instance: the integers `n, u_1, …, u_n, w_1, …, w_n, b, W`,
each in binary by `encInt` (a minus sign for a negative integer, then the binary digits and a
separator), one after the other. The first number `n` fixes how many numbers follow, so the code
determines the instance. -/
def knapsackCode {n : ℕ} (u w : Fin n → ℕ) (b W : ℤ) : List BSym :=
  encInts ((n : ℤ) :: (List.ofFn fun i => (u i : ℤ)) ++ (List.ofFn fun i => (w i : ℤ)) ++ [b, W])

/-- The KNAPSACK language: binary codes of the yes-instances of Problem 5.1. -/
def knapsackLang : Lang BSym :=
  { x | ∃ (n : ℕ) (u w : Fin n → ℕ) (b W : ℤ), KnapsackYes u w b W ∧ x = knapsackCode u w b W }

end TwoAgentSched.Knapsack


