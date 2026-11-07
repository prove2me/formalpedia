-- Prove2me | Definitions.Def_ClawFreeChoosable_IsPeculiar
-- name    : ClawFreeChoosable_IsPeculiar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:18.159911+00:00
-- url     : https://prove2.me/theorems/8535fa90-f9c5-434c-8c6f-bf99c0b3972e
-- title:
--   Peculiar graphs (Definition 12.4 and the standard nondegenerate definition)
-- statement:
--   A **peculiar partition** of a graph $G$ is a partition of $V(G)$ into nine pairwise disjoint cliques $A_1, B_1, A_2, B_2, A_3, B_3, K_1, K_2, K_3$, with indices modulo 3, such that
--
--   1. the six cliques $A_i, B_i$ are nonempty (the $K_i$ may be empty);
--   2. each pair $(A_i, B_{i+1})$ contains a nonadjacent pair, and the three sets $A_1 \cup B_2$, $A_2 \cup B_3$, $A_3 \cup B_1$ are pairwise complete to one another;
--   3. the cliques $K_1, K_2, K_3$ are pairwise anticomplete;
--   4. for each $i$, $K_i$ is anticomplete to $A_i \cup B_i$ and complete to $A_j \cup B_j$ for every $j \ne i$.
--
--   $G$ is **peculiar** (Definition 12.4) if it admits a peculiar partition. $G$ is **peculiar in the standard nondegenerate sense** of Chvátal–Sbihi if it admits a peculiar partition in which all nine cliques, including $K_1, K_2, K_3$, are nonempty.
--
--   Peculiar graphs are, with elementary graphs, the two kinds of claw-free perfect atoms (Theorem 1.2).
--
--   **Formalization Note** Indices are elements of $\mathbb Z/3$, so $B_{i+1}$ wraps around.
-- source:
--   Mishra, Narayanan N, Shankar, Claw-free perfect graphs are chromatic-choosable, arXiv:2611.01068v1, Definition 12.4, p.33

import Mathlib
import Definitions.Def_ClawFreeChoosable_IsAnticomplete

set_option autoImplicit false

namespace ClawFreeChoosable

/-- **Peculiar partition** (arXiv:2611.01068v1, Definition 12.4, p.33, after [CS88]): nine
pairwise disjoint cliques `A₁, B₁, A₂, B₂, A₃, B₃, K₁, K₂, K₃` partitioning `V(G)`, indices
modulo 3, such that
1. the six cliques `Aᵢ, Bᵢ` are nonempty (the `Kᵢ` may be empty);
2. each pair `(Aᵢ, Bᵢ₊₁)` contains a nonadjacent pair, and the three sets `A₁ ∪ B₂`,
   `A₂ ∪ B₃`, `A₃ ∪ B₁` are pairwise complete to one another;
3. the cliques `K₁, K₂, K₃` are pairwise anticomplete;
4. for each `i`, `Kᵢ` is anticomplete to `Aᵢ ∪ Bᵢ` and complete to `Aⱼ ∪ Bⱼ` for every `j ≠ i`.

**Formalization Note.** Indices are `Fin 3`, whose addition is addition modulo 3, so
`B (i + 1)` is `Bᵢ₊₁` and `A i ∪ B (i + 1)` runs over `A₁ ∪ B₂, A₂ ∪ B₃, A₃ ∪ B₁`. -/
def IsPeculiarPartition {V : Type} (G : SimpleGraph V) (A B K : Fin 3 → Set V) : Prop :=
  -- the nine sets are pairwise disjoint and cover `V`
  (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i j, i ≠ j → Disjoint (B i) (B j)) ∧
  (∀ i j, i ≠ j → Disjoint (K i) (K j)) ∧ (∀ i j, Disjoint (A i) (B j)) ∧
  (∀ i j, Disjoint (A i) (K j)) ∧ (∀ i j, Disjoint (B i) (K j)) ∧
  (∀ v : V, ∃ i, v ∈ A i ∨ v ∈ B i ∨ v ∈ K i) ∧
  -- each of them is a clique
  (∀ i, G.IsClique (A i) ∧ G.IsClique (B i) ∧ G.IsClique (K i)) ∧
  -- condition 1
  (∀ i, (A i).Nonempty ∧ (B i).Nonempty) ∧
  -- condition 2
  (∀ i, ∃ a ∈ A i, ∃ b ∈ B (i + 1), ¬ G.Adj a b) ∧
  (∀ i j, i ≠ j → IsComplete G (A i ∪ B (i + 1)) (A j ∪ B (j + 1))) ∧
  -- condition 3
  (∀ i j, i ≠ j → IsAnticomplete G (K i) (K j)) ∧
  -- condition 4
  (∀ i, IsAnticomplete G (K i) (A i ∪ B i) ∧ ∀ j, j ≠ i → IsComplete G (K i) (A j ∪ B j))

/-- **Peculiar graph** in the sense of Definition 12.4 (arXiv:2611.01068v1, p.33): the vertex set
admits a peculiar partition; the cliques `K₁, K₂, K₃` may be empty. -/
def IsPeculiar {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ A B K : Fin 3 → Set V, IsPeculiarPartition G A B K

/-- **Peculiar graph, standard nondegenerate definition** (arXiv:2611.01068v1, Definition 12.4
item 1, p.33; [CS88]): a peculiar partition in which all nine cliques are nonempty, i.e. also
`K₁, K₂, K₃ ≠ ∅`. -/
def IsPeculiarStd {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ A B K : Fin 3 → Set V, IsPeculiarPartition G A B K ∧ ∀ i, (K i).Nonempty

end ClawFreeChoosable


