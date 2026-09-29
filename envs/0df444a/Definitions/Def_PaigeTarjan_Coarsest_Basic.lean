-- Prove2me | Definitions.Def_PaigeTarjan_Coarsest_Basic
-- name    : PaigeTarjan_Coarsest_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T17:45:15.508496+00:00
-- url     : https://prove2.me/theorems/1750f8b1-8fcf-4eb5-a6a5-eb6054d1e6ee
-- title:
--   Partitions, refinement, preimage E⁻¹(S), stability and split(S, Q)
-- statement:
--   This file fixes the basic vocabulary of the relational coarsest partition problem.
--
--   Let $U$ be a finite set and $E \subseteq U \times U$ a binary relation on $U$; write $xEy$ for $(x,y) \in E$. For $S \subseteq U$ the **preimage set** is
--   $$E^{-1}(S) = \{x \in U \mid \exists y \in S \text{ such that } xEy\}.$$
--
--   1. A **partition** of $U$ is a family of nonempty, pairwise disjoint subsets of $U$ (its **blocks**) whose union is $U$.
--   2. A partition $R$ is a **refinement** of a partition $P$ if every block of $R$ is contained in a block of $P$; every partition is a refinement of itself.
--   3. A set $S$ is a **union of blocks** of $Q$ if $S = \bigcup T$ for some subfamily $T \subseteq Q$.
--   4. A set $B$ is **stable with respect to** $S$ if $B \subseteq E^{-1}(S)$ or $B \cap E^{-1}(S) = \emptyset$. A partition $P$ is stable with respect to $S$ if all of its blocks are, and $P$ is **stable** if it is stable with respect to each of its own blocks.
--   5. For a family of blocks $Q$ and $S \subseteq U$, $\mathrm{split}(S, Q)$ replaces each block $B \in Q$ with $B \cap E^{-1}(S) \neq \emptyset$ and $B - E^{-1}(S) \neq \emptyset$ by the two blocks $B \cap E^{-1}(S)$ and $B - E^{-1}(S)$, and keeps every other block whole.
--   6. $Q$ is the **coarsest stable refinement** of the partition $P$ if $Q$ is a stable partition refining $P$ and every stable partition refining $P$ is a refinement of $Q$.
--
--   These notions are the objects of the relational coarsest partition problem: given $E$ and an initial partition $P$, find the coarsest stable refinement of $P$. A partition $Q$ is stable exactly when, for every pair of blocks $B_1, B_2$ of $Q$, either $B_1 \subseteq E^{-1}(B_2)$ or $B_1 \cap E^{-1}(B_2) = \emptyset$.
--
--   **Formalization Note** $U$ is a `Fintype` with decidable equality and $E$ a decidable relation `U → U → Prop`. A partition is a `Finset (Finset U)` together with the predicate `IsPartition`; blocks are required to be nonempty, which the paper's definition (p. 973) leaves implicit (its proof of Theorem 2 counts "between one and $n$" blocks). `split` is defined on any finite family of sets by keeping the nonempty parts $B \cap E^{-1}(S)$ and $B - E^{-1}(S)$ of every block, which is the paper's operation: a block with one empty part stays whole. "Every other stable partition is a refinement of it" (p. 978) is read as every other stable partition *refining $P$*.
-- source:
--   Paige, Tarjan, Three Partition Refinement Algorithms, SIAM J. Comput. 16 (1987), p. 973, §1 (partition, refinement) and pp. 977–978, §3 (E⁻¹(S), stability, the relational coarsest partition problem, split(S, Q))

import Mathlib

namespace PaigeTarjan.Coarsest

/-!
Relational coarsest partition: the basic objects (Paige–Tarjan 1987, §1, p. 973, and §3,
pp. 977–978).

The ground set `U` is a finite type with decidable equality; a binary relation `E ⊆ U × U` is a
decidable predicate `E : U → U → Prop` (`E x y` is the paper's `xEy`). Subsets of `U` are
`Finset U`; a family of blocks is a `Finset (Finset U)`, and "is a partition of `U`" is the
predicate `IsPartition`.
-/

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The preimage set `E⁻¹(S) = {x | ∃ y ∈ S such that xEy}` (p. 977). -/
def preimage (E : U → U → Prop) [DecidableRel E] (S : Finset U) : Finset U :=
  Finset.univ.filter (fun x => ∃ y ∈ S, E x y)

/-- `P` is a partition of `U` (p. 973): its blocks are nonempty, pairwise disjoint, and their
union is all of `U`. (Nonemptiness of blocks is the standard reading; the page leaves it
implicit.) -/
def IsPartition (P : Finset (Finset U)) : Prop :=
  (∀ B ∈ P, B.Nonempty) ∧
  (∀ B ∈ P, ∀ C ∈ P, B ≠ C → Disjoint B C) ∧
  (∀ x : U, ∃ B ∈ P, x ∈ B)

/-- `R` is a refinement of `P` (p. 973): every block of `R` is contained in a block of `P`. -/
def Refines (R P : Finset (Finset U)) : Prop :=
  ∀ B ∈ R, ∃ C ∈ P, B ⊆ C

/-- `S` is a union of some of the blocks of `Q` (p. 978). -/
def IsUnionOfBlocks (S : Finset U) (Q : Finset (Finset U)) : Prop :=
  ∃ T ⊆ Q, S = T.biUnion id

/-- A set `B` is stable with respect to `S` (p. 978): `B ⊆ E⁻¹(S)` or `B ∩ E⁻¹(S) = ∅`. -/
def StableBlock (E : U → U → Prop) [DecidableRel E] (B S : Finset U) : Prop :=
  B ⊆ preimage E S ∨ Disjoint B (preimage E S)

/-- A partition `P` is stable with respect to `S` (p. 978): every block of `P` is stable with
respect to `S`. -/
def StableWrt (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) (S : Finset U) :
    Prop :=
  ∀ B ∈ P, StableBlock E B S

/-- A partition `P` is stable (p. 978): it is stable with respect to each of its own blocks. -/
def Stable (E : U → U → Prop) [DecidableRel E] (P : Finset (Finset U)) : Prop :=
  ∀ S ∈ P, StableWrt E P S

/-- `split(S, Q)` (p. 978): replace each block `B ∈ Q` with `B ∩ E⁻¹(S) ≠ ∅` and
`B − E⁻¹(S) ≠ ∅` by the two blocks `B ∩ E⁻¹(S)` and `B − E⁻¹(S)`; a block for which one of
the two parts is empty stays whole (only the nonempty parts are kept). -/
def split (E : U → U → Prop) [DecidableRel E] (S : Finset U) (Q : Finset (Finset U)) :
    Finset (Finset U) :=
  Q.biUnion (fun B =>
    ({B ∩ preimage E S, B \ preimage E S} : Finset (Finset U)).filter (fun C => C.Nonempty))

/-- `Q` is the coarsest stable refinement of the partition `P` (p. 978): `Q` is a stable
partition refining `P`, and every stable partition refining `P` is a refinement of `Q`. -/
def IsCoarsestStableRefinement (E : U → U → Prop) [DecidableRel E]
    (P Q : Finset (Finset U)) : Prop :=
  IsPartition Q ∧ Refines Q P ∧ Stable E Q ∧
    ∀ R : Finset (Finset U), IsPartition R → Refines R P → Stable E R → Refines R Q

end PaigeTarjan.Coarsest


