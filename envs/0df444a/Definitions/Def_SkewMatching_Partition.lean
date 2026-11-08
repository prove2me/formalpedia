-- Prove2me | Definitions.Def_SkewMatching_Partition
-- name    : SkewMatching_Partition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:09:33.280482+00:00
-- url     : https://prove2.me/theorems/eaa1952f-ab76-4007-ba6e-413f21067188
-- title:
--   Definition 8 — barriers, pauses and violating pairs
-- statement:
--   A **barrier** from $s$ to $s'$ of a sub-multigraph $H$ is a partition $(A,A',X_1,\dots,X_k,M)$ of the vertex set, with $A'$ the symmetric set of $A$ and each fragment $X_i$ self-symmetric, such that:
--
--   1. $s\in A$;
--   2. there are no edges of $H$ from $A$ to $A'$ or from $A$ to $M$;
--   3. there are no edges of $H$ between $X_i$ and $X_j$ for $i\ne j$, or between $X_i$ and $M$, in either direction;
--   4. for every $i$, exactly one edge of $H$ goes from $A$ to $X_i$.
--
--   A **pause** is a barrier for which $A\cup X_1\cup\dots\cup X_k$ is the set of vertices reachable from $s$ by regular paths in $H$. A symmetric pair $\{e,e'\}$ **violates** a barrier of $H$ if the partition is not a barrier of $H\cup\{e,e'\}$.
--
--   Barriers are to regular paths what cuts are to augmenting paths in ordinary flows.
--
--   **Formalization Note** A partition is given by $A$ and the list of fragments; $A'$ and $M$ are derived. "Between" is read in both directions, as in Figure 1.
-- source:
--   Li, Li, Zhang, Maximum Cardinality Matching in n^{2+o(1)} Time, STOC 2027 submission (manuscript sha256 3fc151f5…), Definition 8, p.3; §3.2, p.6; Appendix A, p.15; Lemma 23 (i), p.16

import Mathlib
import Definitions.Def_SkewMatching_SkewGraph_IsRegularPathIn

namespace SkewMatching

open scoped Classical

/-- A candidate partition `(A, A′, X₁, …, X_k, M)` of the vertex set, given by `A` and the fragments.
`A′` and `M` are derived.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Definition 8, p.3. -/
structure Partition (V : Type*) where
  A : Finset V
  frags : List (Finset V)

/-- The union `X₁ ∪ ⋯ ∪ X_k` of the fragments. -/
noncomputable def Partition.fragUnion {V : Type*} (P : Partition V) : Finset V :=
  P.frags.toFinset.biUnion id

namespace SkewGraph

variable {V E : Type*} (G : SkewGraph V E)

/-- The symmetric set `S′ = {σ(v) : v ∈ S}` (p.3). -/
noncomputable def symm (S : Finset V) : Finset V := S.image G.σV

/-- `M`, the vertices in none of `A`, `A′`, `X₁, …, X_k`. -/
noncomputable def restM [Fintype V] (P : Partition V) : Finset V :=
  Finset.univ \ (P.A ∪ G.symm P.A ∪ P.fragUnion)

/-- **Definition 8**, p.3: a barrier from `s` to `s′` of the sub-multigraph `H`.

* the sets are pairwise disjoint, `A′` is symmetric to `A`, each fragment is self-symmetric, and `M` is the
  rest of the vertices;
* `s ∈ A`;
* there are no edges of `H` from `A` to `A′`, or from `A` to `M`;
* there are no edges of `H` between `X_i` and `X_j` for `i ≠ j`, or between `X_i` and `M`, in either direction;
* for every `i`, exactly one edge of `H` goes from `A` to `X_i`.

Li, Li, Zhang, *Maximum Cardinality Matching in n^{2+o(1)} Time*, STOC 2027 submission (manuscript
sha256 3fc151f5…), Definition 8, p.3; restated §3.2, p.6.

**Formalization Note.** `M` is self-symmetric automatically on a partition. The third bullet of p.3 and p.6 is
read in both directions ("between"), as Figure 1 shows. -/
structure IsBarrier [Fintype V] (H : Finset E) (s : V) (P : Partition V) : Prop where
  s_mem : s ∈ P.A
  disj_A : Disjoint P.A (G.symm P.A)
  frag_symm : ∀ X ∈ P.frags, G.symm X = X
  frag_disj : ∀ X ∈ P.frags, Disjoint X P.A ∧ Disjoint X (G.symm P.A)
  frag_pairwise : P.frags.Pairwise Disjoint
  no_A_A' : ∀ e ∈ H, G.tail e ∈ P.A → G.head e ∉ G.symm P.A
  no_A_M : ∀ e ∈ H, G.tail e ∈ P.A → G.head e ∉ G.restM P
  no_frag_frag : P.frags.Pairwise fun X Y =>
    ∀ e ∈ H, ¬ (G.tail e ∈ X ∧ G.head e ∈ Y) ∧ ¬ (G.tail e ∈ Y ∧ G.head e ∈ X)
  no_frag_M : ∀ X ∈ P.frags, ∀ e ∈ H,
    ¬ (G.tail e ∈ X ∧ G.head e ∈ G.restM P) ∧ ¬ (G.tail e ∈ G.restM P ∧ G.head e ∈ X)
  unique_edge : ∀ X ∈ P.frags, ∃! e, e ∈ H ∧ G.tail e ∈ P.A ∧ G.head e ∈ X

/-- The state of a pause (Lemma 23 (i), p.16): a barrier of `H` such that `A ∪ X₁ ∪ ⋯ ∪ X_k` is the set of
vertices reachable from `s` by regular paths in `H`. -/
def IsPause [Fintype V] (H : Finset E) (s : V) (P : Partition V) : Prop :=
  G.IsBarrier H s P ∧ ((P.A ∪ P.fragUnion : Finset V) : Set V) = G.regularReach H s

/-- A pair `{e, e′}` **violates** a barrier of `H` (Appendix A, p.15): the partition is a barrier of `H` but not of
`H ∪ {e, e′}`. -/
def Violates [Fintype V] (H : Finset E) (s : V) (P : Partition V) (e : E) : Prop :=
  G.IsBarrier H s P ∧ ¬ G.IsBarrier (H ∪ {e, G.σE e}) s P

end SkewGraph

end SkewMatching


