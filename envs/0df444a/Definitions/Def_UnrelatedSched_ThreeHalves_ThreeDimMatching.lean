-- Prove2me | Definitions.Def_UnrelatedSched_ThreeHalves_ThreeDimMatching
-- name    : UnrelatedSched_ThreeHalves_ThreeDimMatching
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:04:54.005119+00:00
-- url     : https://prove2.me/theorems/3050a4f6-5e48-4f7a-b818-a22e84967426
-- title:
--   3-dimensional matching: instances and matchings (Section 4, proof of Theorem 4)
-- statement:
--   An instance of **3-dimensional matching** consists of three disjoint sets
--   $A = \{a_1,\dots,a_n\}$, $B = \{b_1,\dots,b_n\}$, $C = \{c_1,\dots,c_n\}$ of the same size $n$, and a family $F = \{T_1,\dots,T_m\}$ of triples, each containing exactly one element of $A$, one of $B$ and one of $C$:
--   $$|T_i \cap A| = |T_i \cap B| = |T_i \cap C| = 1, \qquad i = 1,\dots,m.$$
--
--   A **matching** is a subfamily $F' \subseteq F$ with $|F'| = n$ whose triples together cover $A \cup B \cup C$:
--   $$|F'| = n \quad\text{and}\quad \bigcup_{T_i \in F'} T_i = A \cup B \cup C.$$
--   Since the $n$ triples of $F'$ have $3n$ elements in total and cover all $3n$ elements, they are pairwise disjoint. The instance **has a matching** if such an $F'$ exists; deciding this is the classical NP-complete problem 3-DIMENSIONAL MATCHING, the source of the reductions in Section 4 of the paper.
--
--   **Formalization Note** The elements are indexed by $\mathrm{Fin}\,n$ and the triples by $\mathrm{Fin}\,m$; the instance is a map $T : \mathrm{Fin}\,m \to \mathrm{Fin}\,n \times \mathrm{Fin}\,n \times \mathrm{Fin}\,n$, with $T_i = (j,k,l)$ standing for $(a_j, b_k, c_l)$. Because the family is indexed, a triple may occur more than once. A matching is a set $F'$ of indices with $|F'| = n$ such that every $a_j$, every $b_k$ and every $c_l$ occurs in some $T_i$, $i \in F'$ (the covering form of the paper's definition).
-- source:
--   Lenstra, Shmoys, Tardos, Approximation algorithms for scheduling unrelated parallel machines, CWI Report OS-R8714 (1987), p. 7, Section 4, proof of Theorem 4 (3-DIMENSIONAL MATCHING)

import Mathlib

namespace UnrelatedSched.ThreeHalves

/-- A matching of an instance of 3-DIMENSIONAL MATCHING (Lenstra, Shmoys, Tardos, CWI Report
OS-R8714 (1987), §4, p. 7, proof of Theorem 4).

The instance consists of disjoint sets `A = {a_1, …, a_n}`, `B = {b_1, …, b_n}`,
`C = {c_1, …, c_n}` and a family `F = {T_1, …, T_m}` of triples with one element in each of
`A`, `B`, `C`. Here the elements `a_j`, `b_k`, `c_l` are indexed by `j, k, l : Fin n`, and the
triple `T_i` is `T i = (j, k, l)`, standing for `(a_j, b_k, c_l)`; the triples are indexed by
`i : Fin m`, so the same triple may occur several times in the family.

A matching is a subfamily `F' ⊆ F`, given by its index set `F' : Finset (Fin m)`, with `|F'| = n`
whose union is `A ∪ B ∪ C`: every `a_j`, every `b_k` and every `c_l` lies in some triple of `F'`.
(With `|F'| = n` this covering condition forces the triples of `F'` to be pairwise disjoint.) -/
def IsMatching {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) (F' : Finset (Fin m)) : Prop :=
  F'.card = n ∧
    (∀ j : Fin n, ∃ i ∈ F', (T i).1 = j) ∧
    (∀ k : Fin n, ∃ i ∈ F', (T i).2.1 = k) ∧
    (∀ l : Fin n, ∃ i ∈ F', (T i).2.2 = l)

/-- The instance `T` of 3-DIMENSIONAL MATCHING has a matching (the question of the problem). -/
def HasMatching {m n : ℕ} (T : Fin m → Fin n × Fin n × Fin n) : Prop :=
  ∃ F' : Finset (Fin m), IsMatching T F'

end UnrelatedSched.ThreeHalves


