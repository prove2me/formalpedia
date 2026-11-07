-- Prove2me | Definitions.Def_FewInnerTSP_MixedInstance
-- name    : FewInnerTSP_MixedInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:27:03.276231+00:00
-- url     : https://prove2.me/theorems/4b805ca6-7d61-416a-a166-44d3fa690547
-- title:
--   The mixed instance: edges with identities, the reduced skeleton, mixed Hamiltonian cycles
-- statement:
--   A **mixed instance** on an instance $P$ has a fixed cyclic **skeleton** $\Gamma$: $m$ vertices $v_0,\dots,v_{m-1}$ (indices of $P$) in cyclic order, with skeleton edge $j$ joining $v_j$ and $v_{j+1}$ (mod $m$), a status (mandatory or optional) and a stored weight. Edges carry **identities**: a free edge is an unordered pair of indices, a skeleton edge is its position $j$; for $m=2$ the two skeleton edges are parallel.
--
--   1. A skeleton is **convex** if $m\ge 2$, its vertices are distinct and every triple in cyclic order turns counterclockwise.
--   2. The **reduced skeleton** of §3: the retained vertices $H_0$ in hull order; the edge from a retained position $p$ to the next retained position is optional when $p$ is a retained gap (it is then that hull edge) and mandatory otherwise (it suppresses a maximal forced hull chain). In both cases its weight is the **sum of the original edge lengths** along the hull from $p$ to the next retained position, never the chord.
--   3. The vertex set is $I\cup H_0$. A **mixed Hamiltonian cycle** is a set $T$ of edges such that every free edge in $T$ has distinct endpoints in $I\cup H_0$, at least one of them in $I$ (so no other $H_0$–$H_0$ chord occurs); every mandatory skeleton edge is in $T$; every vertex of $I\cup H_0$ has degree $2$ (parallel edges counted separately); and $T$ is connected on $I\cup H_0$.
--   4. The **weight** of $T$ is the sum of Euclidean lengths of its free edges plus the stored weights of its skeleton edges; a **minimum** mixed cycle minimizes it among mixed Hamiltonian cycles.
--
--   Also defined: the free edges of $T$, and the edge set of a tour $\pi$ as unordered index pairs.
--
--   **Formalization Note** A mandatory edge weighted by its chord would break Lemma 3.3 (the page's negative controls, p.27).
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), §3 and Definition 3.2, p.4 (PDF p.6)

import Mathlib
import Definitions.Def_FewInnerTSP_RetainedGaps
import Definitions.Def_FewInnerTSP_HullOrder

namespace FewInnerTSP

/-- An edge of a mixed instance, with its **identity**: a free edge is an unordered pair of original
indices, a skeleton edge is its position `j` on the cyclic skeleton. Identities matter because
`|H₀| = 2` gives two parallel skeleton edges.
Source: Li, Ma, Gong, STOC 2027 submission (manuscript sha256 6541f631…), Definition 3.2, p.4 (PDF p.6). -/
inductive Edge (n m : ℕ) where
  | free (e : Sym2 (Fin n))
  | skel (j : Fin m)
  deriving DecidableEq

/-- **A fixed cyclic skeleton** `Γ` on `m` retained vertices in cyclic order. The edge `j` joins
`vert j` and `vert (j+1)` (cyclic), carries a status (`mand j` = mandatory, otherwise optional) and a
stored weight `wt j`. Source: Li, Ma, Gong, §3, p.4 (PDF p.6). -/
structure Skeleton (n m : ℕ) where
  vert : Fin m → Fin n
  mand : Fin m → Prop
  wt : Fin m → ℝ

/-- The two endpoints of an edge of a mixed instance. -/
def Skeleton.ends {n m : ℕ} (Γ : Skeleton n m) : Edge n m → Sym2 (Fin n)
  | Edge.free e => e
  | Edge.skel j => s(Γ.vert j, Γ.vert (finRotate m j))

/-- A convex skeleton in the plane: at least two vertices, pairwise distinct, every triple in cyclic
order positively oriented. For `m = 2` this is two distinct points with two parallel skeleton edges.
Source: Li, Ma, Gong, §3, p.4 (PDF p.6): "When |H0| ≥ 3, its straight chord drawing is convex. The
case |H0| = 2 has two parallel skeleton edges". -/
structure IsConvexSkeleton {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) : Prop where
  two_le : 2 ≤ m
  injective : Function.Injective Γ.vert
  ccw : ∀ i j l : Fin m, i < j → j < l → 0 < orient (P (Γ.vert i)) (P (Γ.vert j)) (P (Γ.vert l))

/-- The hull position `d` steps after position `p`, cyclically. -/
def cycPos {h : ℕ} (p : Fin h) (d : ℕ) : Fin h :=
  ⟨(p.val + d) % h, Nat.mod_lt _ (Nat.zero_lt_of_lt p.isLt)⟩

/-- The hull position of the `i`-th retained vertex, in increasing position order. -/
noncomputable def skelPos {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n)
    (i : Fin (retainedPos P hull).card) : Fin h :=
  (retainedPos P hull).orderEmbOfFin rfl i

/-- The number of hull edges from the `i`-th retained vertex to the next one, cyclically. -/
noncomputable def skelSpan {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n)
    (i : Fin (retainedPos P hull).card) : ℕ :=
  ((skelPos P hull (finRotate _ i)).val + h - (skelPos P hull i).val) % h

/-- **The reduced skeleton.** The vertices are the retained vertices `H₀` in hull order. The edge from
a retained position `p` to the next retained position is optional when `p` is a retained gap, and
then it is that gap's hull edge; otherwise it is mandatory and suppresses a maximal forced hull chain.
In both cases its stored weight is the sum of the original edge lengths on it.
Source: Li, Ma, Gong, §3, p.4 (PDF p.6): "replacing it by a mandatory edge of weight equal to the sum
of the original edge lengths on that chain".

**Formalization Note** A mandatory edge is never weighted by its chord (the paper's negative
controls, p.27, exist for this bug). The defining sum uses `skelSpan`, a positive number for `k > 0`,
when there are at least two retained vertices. -/
noncomputable def reducedSkeleton {n h : ℕ} (P : Fin n → Pt) (hull : Fin h → Fin n) :
    Skeleton n (retainedPos P hull).card where
  vert i := hull (skelPos P hull i)
  mand i := skelPos P hull i ∉ retainedGaps P hull
  wt i := ∑ d ∈ Finset.range (skelSpan P hull i),
    dist (P (hull (cycPos (skelPos P hull i) d))) (P (hull (cycPos (skelPos P hull i) (d + 1))))

/-- The vertices `I ∪ H₀` of a mixed instance with skeleton `Γ`.
Source: Li, Ma, Gong, Definition 3.2, p.4 (PDF p.6). -/
noncomputable def mixedVerts {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) : Finset (Fin n) :=
  interiorIdx P ∪ Finset.univ.image Γ.vert

/-- The Euclidean length of an unordered pair of indices. -/
noncomputable def edgeLen {n : ℕ} (P : Fin n → Pt) (e : Sym2 (Fin n)) : ℝ :=
  Sym2.lift ⟨fun a b => dist (P a) (P b), fun _ _ => dist_comm _ _⟩ e

/-- The weight of an edge of the mixed instance: free edges have their Euclidean length, skeleton
edges their stored weight. -/
noncomputable def mixedEdgeWeight {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) : Edge n m → ℝ
  | Edge.free e => edgeLen P e
  | Edge.skel j => Γ.wt j

open Classical in
/-- The number of edges of `C` incident to `v`, counting parallel edges separately. -/
noncomputable def edgeDeg {n m : ℕ} (Γ : Skeleton n m) (C : Finset (Edge n m)) (v : Fin n) : ℕ :=
  (C.filter fun e => v ∈ Γ.ends e).card

/-- `a` and `b` are joined by an edge of `C`. -/
def edgeAdj {n m : ℕ} (Γ : Skeleton n m) (C : Finset (Edge n m)) (a b : Fin n) : Prop :=
  ∃ e ∈ C, Γ.ends e = s(a, b)

/-- `a` and `b` lie in one component of the graph formed by the edge set `C`. -/
def edgeReach {n m : ℕ} (Γ : Skeleton n m) (C : Finset (Edge n m)) (a b : Fin n) : Prop :=
  Relation.ReflTransGen (edgeAdj Γ C) a b

/-- **A mixed Hamiltonian cycle**: only allowed edges (a free edge has distinct endpoints in `I ∪ H₀`,
at least one in `I`, so no other `H₀–H₀` chord occurs; skeleton edges are allowed), every mandatory
edge is present, degree `2` at every vertex of `I ∪ H₀`, and connected.
Source: Li, Ma, Gong, Definition 3.2, p.4 (PDF p.6). -/
structure IsMixedCycle {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (T : Finset (Edge n m)) :
    Prop where
  free_allowed : ∀ e, Edge.free e ∈ T →
    ¬ e.IsDiag ∧ (∀ v ∈ e, v ∈ mixedVerts P Γ) ∧ ∃ v ∈ e, v ∈ interiorIdx P
  mandatory : ∀ j, Γ.mand j → Edge.skel j ∈ T
  degree : ∀ v ∈ mixedVerts P Γ, edgeDeg Γ T v = 2
  connected : ∀ x ∈ mixedVerts P Γ, ∀ y ∈ mixedVerts P Γ, edgeReach Γ T x y

/-- The total weight of a mixed edge set. -/
noncomputable def mixedWeight {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m)
    (T : Finset (Edge n m)) : ℝ :=
  ∑ e ∈ T, mixedEdgeWeight P Γ e

/-- A minimum-weight mixed Hamiltonian cycle. -/
def IsMinMixedCycle {n m : ℕ} (P : Fin n → Pt) (Γ : Skeleton n m) (T : Finset (Edge n m)) : Prop :=
  IsMixedCycle P Γ T ∧ ∀ T', IsMixedCycle P Γ T' → mixedWeight P Γ T ≤ mixedWeight P Γ T'

open Classical in
/-- The free edges of a mixed edge set, as unordered pairs of indices. -/
noncomputable def freeEdges {n m : ℕ} (C : Finset (Edge n m)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => Edge.free e ∈ C

/-- The edges of the tour `π`, as unordered pairs of indices. -/
noncomputable def tourEdges {n : ℕ} (π : Equiv.Perm (Fin n)) : Finset (Sym2 (Fin n)) :=
  Finset.univ.image fun i => s(π i, π (finRotate n i))

end FewInnerTSP


