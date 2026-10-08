-- Prove2me | Definitions.Def_WhitneyMatroid_RankCircuit_IsCircuitSystem
-- name    : WhitneyMatroid_RankCircuit_IsCircuitSystem
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T12:05:08.720758+00:00
-- url     : https://prove2.me/theorems/2da0a69d-623f-486b-bc63-0b8c6c5b605c
-- title:
--   Whitney's circuit postulates (C₁), (C₂) and the rank defined from circuits (§8)
-- statement:
--   Let $M$ be a finite set of elements, and let each subset of $M$ either be or not be a **circuit**. Whitney's **circuit postulates** are:
--
--   1. $(\mathrm C_1)$ no proper subset of a circuit is a circuit;
--   2. $(\mathrm C_2)$ if $P_1$ and $P_2$ are circuits, $e_1$ is in both $P_1$ and $P_2$, and $e_2$ is in $P_1$ but not in $P_2$, then there is a circuit $P_3 \subseteq P_1 \cup P_2$ containing $e_2$ but not $e_1$.
--
--   **Rank from circuits.** For an ordered list $(e_1, \dots, e_p)$ of elements, set $\Gamma_i = 0$ if there is a circuit contained in $\{e_1, \dots, e_i\}$ that contains $e_i$, and $\Gamma_i = 1$ otherwise. The rank of the ordered list is
--   $$r(e_1, \dots, e_p) = \sum_{i=1}^{p} \Gamma_i .$$
--   The rank of a subset $N$ is the rank of one fixed enumeration of its elements. Whitney's Lemma 8 asserts that, under $(\mathrm C_1)$, $(\mathrm C_2)$, the value does not depend on the enumeration.
--
--   These are the objects of the circuit side of Whitney's equivalence between the circuit postulates and the rank postulates.
--
--   **Formalization Note** The elements form a finite type `α`; subsets are `Finset α`; the circuit family is a predicate `C : Finset α → Prop`. `ClosesCircuit C l i` is "$\Gamma_{i+1} = 0$" for the list `l` (indices are 0-based in Lean). `rankSeq C l` is $\sum_i \Gamma_i$ for an arbitrary list. `rankOfCircuits C N` is `rankSeq` of the enumeration `N.toList`, which is a specific but unspecified ordering. Nothing in the definition makes the choice of ordering irrelevant; that is the content of Lemma 8. The rank is integer valued.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 516, §8 (postulates (C₁), (C₂); Γᵢ and r(e₁, ⋯, e_p))

import Mathlib

namespace WhitneyMatroid.RankCircuit

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Whitney's circuit postulates (§8, p. 516) for a family `C` of subsets ("circuits") of the finite
set of elements `α`:
(C₁) no proper subset of a circuit is a circuit;
(C₂) if `P₁` and `P₂` are circuits, `e₁` is in both `P₁` and `P₂`, and `e₂` is in `P₁` but not in
`P₂`, then there is a circuit `P₃` in `P₁ + P₂` containing `e₂` but not `e₁`. -/
structure IsCircuitSystem (C : Finset α → Prop) : Prop where
  C1 : ∀ P Q : Finset α, C P → Q ⊂ P → ¬ C Q
  C2 : ∀ (P₁ P₂ : Finset α) (e₁ e₂ : α), C P₁ → C P₂ → e₁ ∈ P₁ → e₁ ∈ P₂ → e₂ ∈ P₁ → e₂ ∉ P₂ →
    ∃ P₃ : Finset α, C P₃ ∧ P₃ ⊆ P₁ ∪ P₂ ∧ e₂ ∈ P₃ ∧ e₁ ∉ P₃

/-- For an ordered list `l = (e₁, …, e_p)` and an index `i` (0-based, so `l.get i = e_{i+1}`),
`ClosesCircuit C l i` says that there is a circuit contained in `e₁ + ⋯ + e_{i+1}` (the first
`i + 1` entries of `l`) which contains `e_{i+1}` (p. 516). -/
def ClosesCircuit (C : Finset α → Prop) (l : List α) (i : Fin l.length) : Prop :=
  ∃ P : Finset α, C P ∧ P ⊆ (l.take (i.val + 1)).toFinset ∧ l.get i ∈ P

open Classical in
/-- Whitney's rank of an ordered set of elements from circuits (§8, p. 516): `Γᵢ = 0` if there is a
circuit in `e₁ + ⋯ + eᵢ` containing `eᵢ`, and `Γᵢ = 1` otherwise; `r(e₁, …, e_p) = Σᵢ Γᵢ`. -/
noncomputable def rankSeq (C : Finset α → Prop) (l : List α) : ℤ :=
  ∑ i : Fin l.length, if ClosesCircuit C l i then 0 else 1

/-- The rank of a subset `N` from circuits (§8, p. 516): `rankSeq` of one fixed enumeration
`N.toList` of the elements of `N`. That the choice of enumeration does not matter is Lemma 8. -/
noncomputable def rankOfCircuits (C : Finset α → Prop) (N : Finset α) : ℤ :=
  rankSeq C N.toList

end WhitneyMatroid.RankCircuit


