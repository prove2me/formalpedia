-- Prove2me | Definitions.Def_Erdos20_defs
-- name    : Erdos20_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T17:23:53.912177+00:00
-- url     : https://prove2.me/theorems/795a555f-e240-4732-bf15-d40f39626758
-- title:
--   Sunflowers and the sunflower threshold $f(n,k)$
-- statement:
--   Let $\alpha$ be any type (ground set). For a family $\mathcal F$ of subsets of $\alpha$ and a set $Y \subseteq \alpha$:
--
--   1. $\mathcal F$ is a **sunflower with kernel $Y$** if $A \cap B = Y$ for all distinct $A, B \in \mathcal F$.
--   2. $\mathcal F$ is a **sunflower** if it is a sunflower with some kernel $Y$. In particular the empty family and every one-member family are sunflowers.
--
--   For natural numbers $n, k$ the **sunflower threshold** is
--
--   $$
--   f(n,k) = \min\Bigl\{ m \in \mathbb N \;:\; \text{for every type } \alpha \text{ and every } \mathcal F \text{ with } |A| = n \ (A \in \mathcal F) \text{ and } m \le |\mathcal F|, \ \exists\, \mathcal S \subseteq \mathcal F,\ |\mathcal S| = k,\ \mathcal S \text{ a sunflower} \Bigr\}.
--   $$
--
--   That is, $f(n,k)$ is the least $m$ such that every $n$-uniform family with at least $m$ members contains a $k$-sunflower. These are the basic objects of the Erdős–Rado sunflower problem (Erdős Problem 20).
--
--   **Formalization Note** Sizes are `Set.ncard`, which is $0$ for infinite sets, so for $n \ge 1$ only finite members count as $n$-element and the size condition $m \le |\mathcal F|$ with $m \ge 1$ only concerns finite families. The minimum is `sInf` on $\mathbb N$, which would be $0$ if no admissible $m$ existed. Ground types range over `Type` (universe 0).
-- source:
--   Formal Conjectures, `FormalConjectures/ErdosProblems/20.lean` (Erdős Problem 20), https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/20.lean ; https://www.erdosproblems.com/20 ; P. Erdős and R. Rado, Intersection theorems for systems of sets, J. London Math. Soc. 35 (1960), 85–90, https://doi.org/10.1112/jlms/s1-35.1.85

import Mathlib

namespace Erdos20

/-- A family `F` is a sunflower with kernel `S` if any two distinct members of `F`
intersect exactly in `S`. -/
def IsSunflowerWithKernel {α : Type*} (F : Set (Set α)) (S : Set α) : Prop :=
  F.Pairwise (fun A B => A ∩ B = S)

/-- A family `F` is a sunflower if all pairwise intersections of distinct members coincide. -/
def IsSunflower {α : Type*} (F : Set (Set α)) : Prop :=
  ∃ S, IsSunflowerWithKernel F S

theorem isSunflower_empty {α : Type*} : IsSunflower (∅ : Set (Set α)) :=
  ⟨∅, by simp [IsSunflowerWithKernel]⟩

theorem isSunflower_singleton {α : Type*} (A : Set α) : IsSunflower {A} :=
  ⟨∅, by simp [IsSunflowerWithKernel]⟩

/-- `f n k` is the least `m` such that every family of `n`-element sets with at least `m`
members contains a `k`-sunflower. -/
noncomputable def f (n k : ℕ) : ℕ :=
  sInf {m | ∀ {α : Type}, ∀ (F : Set (Set α)),
    ((∀ A ∈ F, A.ncard = n) ∧ m ≤ F.ncard) → ∃ S ⊆ F, S.ncard = k ∧ IsSunflower S}

end Erdos20


