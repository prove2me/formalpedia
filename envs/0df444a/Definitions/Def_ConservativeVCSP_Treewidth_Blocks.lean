-- Prove2me | Definitions.Def_ConservativeVCSP_Treewidth_Blocks
-- name    : ConservativeVCSP_Treewidth_Blocks
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:47:51.46506+00:00
-- url     : https://prove2.me/theorems/605dbcc9-6e40-4e57-b1c2-4e519de6f85f
-- title:
--   The move graph G_Γ, its blocks, reversing blocks, and sets belonging to a block
-- statement:
--   The **move graph** $G_\Gamma$ has a vertex $(a,b)$ for each ordering of an interacting pair $\{a,b\}$, and an edge between $(a,b)$ and $(c,d)$ when a finite-valued move from $(a,b)$ to $(c,d)$ lies in $\mathrm{pow}(\Gamma)$. With $\rho(a,b)=(b,a)$, a **block** is a set
--   $$B=C\cup\rho(C)$$
--   for the vertex set $C$ of a connected component; it is **reversing** if $C=\rho(C)$ and nonreversing otherwise. A pairwise interacting set $S$ with $|S|\ge2$ **belongs** to $B$ when every ordered pair of distinct elements of $S$ lies in $B$; sets with $|S|\le1$ belong to no block.
--
--   **Formalization Note** Loops are dropped and the edge relation is symmetrized (`SimpleGraph.fromRel`); neither changes the components. `component Γ p` is the vertex set of the component of `p` (empty if `p` is not a vertex). "Belongs" uses the every-pair wording of §2.2, which equals Definition 6.10's for finite, finite-valued hard-list languages by Lemma 2.10.
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 33, Definitions 6.6, 6.8, 6.9; p. 34, Definition 6.10; p. 12 (§2.2)

import Definitions.Def_ConservativeVCSP_Treewidth_Moves

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

variable {D : Type} [Fintype D]

/-- The vertices of the move graph `G_Γ` (Definition 6.6, p. 33): the orderings `(a, b)` of
interacting pairs `{a, b}`. -/
def MoveVertex (Γ : Set (CostFn D)) : Type :=
  {p : D × D // Interacting Γ p.1 p.2}

/-- The move graph `G_Γ` (Definition 6.6, p. 33): `(a, b)` and `(c, d)` are joined when a
finite-valued move from `(a, b)` to `(c, d)` belongs to `pow(Γ)`. Loops (allowed in the paper) do
not affect connectivity and are omitted; the edge relation is symmetrized. -/
def moveGraph (Γ : Set (CostFn D)) : SimpleGraph (MoveVertex Γ) :=
  SimpleGraph.fromRel fun p q => FVMove Γ p.1.1 p.1.2 q.1.1 q.1.2

/-- The vertex set (as ordered pairs) of the connected component of `G_Γ` containing `p`
(empty when `p` is not a vertex). -/
def component (Γ : Set (CostFn D)) (p : D × D) : Set (D × D) :=
  {q | ∃ (hp : Interacting Γ p.1 p.2) (hq : Interacting Γ q.1 q.2),
    (moveGraph Γ).Reachable ⟨p, hp⟩ ⟨q, hq⟩}

/-- `ρ(S)`: reverse every ordered pair of `S`. -/
def reverseSet (S : Set (D × D)) : Set (D × D) :=
  Prod.swap '' S

/-- `B` is a block of `G_Γ` (Definition 6.8, p. 33): `B = C ∪ ρ(C)` for the vertex set `C` of a
connected component of `G_Γ`. -/
def IsBlock (Γ : Set (CostFn D)) (B : Set (D × D)) : Prop :=
  ∃ p : D × D, Interacting Γ p.1 p.2 ∧ B = component Γ p ∪ reverseSet (component Γ p)

/-- `B` is a reversing block (Definition 6.8): `B = C ∪ ρ(C)` with `C = ρ(C)`. -/
def IsReversingBlock (Γ : Set (CostFn D)) (B : Set (D × D)) : Prop :=
  ∃ p : D × D, Interacting Γ p.1 p.2 ∧ B = component Γ p ∪ reverseSet (component Γ p) ∧
    component Γ p = reverseSet (component Γ p)

/-- `B` is a nonreversing block (Definition 6.8). -/
def IsNonreversingBlock (Γ : Set (CostFn D)) (B : Set (D × D)) : Prop :=
  IsBlock Γ B ∧ ¬ IsReversingBlock Γ B

/-- A set `S ⊆ D` belongs to the block `B` (Definitions 6.9–6.10, pp. 33–34; §2.2, p. 12): `S` is
pairwise interacting, `|S| ≥ 2`, and every ordered pair of distinct elements of `S` lies in `B`.
A set with `|S| ≤ 1` belongs to no block. -/
def BelongsTo (Γ : Set (CostFn D)) (S : Set D) (B : Set (D × D)) : Prop :=
  PairwiseInteracting Γ S ∧ 2 ≤ S.ncard ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → (a, b) ∈ B

end ConservativeVCSP.Treewidth


