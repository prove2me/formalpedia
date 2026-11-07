-- Prove2me | Definitions.Def_LineVsPoint_prunedGraph
-- name    : LineVsPoint_prunedGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:04:59.588843+00:00
-- url     : https://prove2.me/theorems/e813054d-4f69-4aa4-a560-344543b682ec
-- title:
--   The pruned incidence graph $G$ of Section 3 (three deletions, then the $k$-core)
-- statement:
--   Work in $\mathbb F^2$ with a point table $f$, a degree-$d$ line table $\{P_L\}$, a trivariate polynomial $A$ and $S=D_\lambda A$. Start from the bipartite graph of **accepted incidences** $(x,L)$ (points on one side, lines on the other). Step 2 of the paper deletes
--
--   1. every accepted incidence on a line with $A(L(t),p_L(t))\not\equiv 0$;
--   2. every accepted incidence on a remaining line with $S(L(t),p_L(t))\equiv 0$;
--   3. every remaining incidence $(x,L)$ with $S(x,f(x))=0$;
--
--   and then repeatedly removes vertices of degree below $k$. The surviving incidences are the accepted ones with $A(L(t),p_L(t))\equiv0$, $S(L(t),p_L(t))\not\equiv0$ and $S(x,f(x))\ne0$. Repeated removal of low-degree vertices leaves, in any order, the **$k$-core**: the largest set of vertices in which every vertex keeps at least $k$ surviving neighbours. The **pruned graph** $G$ is the graph of surviving incidences on the $k$-core; its point side is $X$, its line side $T$ and its edge set $E$.
--
--   **Formalization Note** `Survives` is the conjunction above, `kCore` the union of all vertex sets in which every vertex has $\ge k$ surviving neighbours (itself such a set), `prunedGraph` the `SimpleGraph` on points `inl x` and lines `inr L` whose edges are surviving incidences inside the $k$-core, and `prunedEdges` its edge set as point–line pairs. Vertices outside the $k$-core are isolated and are not vertices of the paper's $G$.
-- source:
--   Dao, Kominers, Thaler, Zheng, Cube-Root Soundness Is Optimal for the Line–versus–Point Test (manuscript, sha256 328a8943…), §3.2, pp.15–16

import Definitions.Def_LineVsPoint_LineTable
import Definitions.Def_LineVsPoint_lineRestrict

set_option autoImplicit false

namespace LineVsPoint

/-- An incidence `(x, L)` of `F²` **survives the three deletions** of Step 2: Dao, Kominers,
Thaler, Zheng, *Cube-Root Soundness Is Optimal for the Line–versus–Point Test* (manuscript,
sha256 328a8943…), §3.2, p.15. Starting from the accepted incidences, the paper deletes
(1) every accepted incidence on a line with `A(L(t), p_L(t)) ≢ 0`; (2) every accepted incidence
on a remaining line with `S(L(t), p_L(t)) ≡ 0`; (3) every remaining incidence `(x, L)` with
`S(x, f(x)) = 0`. So `(x, L)` survives iff it is accepted, `A(L(t), p_L(t)) ≡ 0`,
`S(L(t), p_L(t)) ≢ 0` and `S(x, f(x)) ≠ 0`. -/
def Survives {F : Type*} [Field F] {d : ℕ} (f : (Fin 2 → F) → F) (P : LineTable F 2 d)
    (A S : MvPolynomial (Fin 3) F) (x : Fin 2 → F) (L : Line F 2) : Prop :=
  Accepted f P x L ∧ graphRestrict (P.a L) (P.u L) (P.p L) A = 0 ∧
    graphRestrict (P.a L) (P.u L) (P.p L) S ≠ 0 ∧ MvPolynomial.eval ![x 0, x 1, f x] S ≠ 0

/-- Adjacency of the bipartite graph of surviving incidences, on points `inl x` and lines
`inr L`. -/
def survAdj {F : Type*} [Field F] {d : ℕ} (f : (Fin 2 → F) → F) (P : LineTable F 2 d)
    (A S : MvPolynomial (Fin 3) F) : (Fin 2 → F) ⊕ Line F 2 → (Fin 2 → F) ⊕ Line F 2 → Prop
  | Sum.inl x, Sum.inr L => Survives f P A S x L
  | Sum.inr L, Sum.inl x => Survives f P A S x L
  | _, _ => False

open Classical in
/-- A vertex set `W` in which every vertex has at least `k` surviving neighbours inside `W`. -/
def IsKClosed {F : Type*} [Field F] [Fintype F] {d : ℕ} (f : (Fin 2 → F) → F)
    (P : LineTable F 2 d) (A S : MvPolynomial (Fin 3) F) (k : ℕ)
    (W : Set ((Fin 2 → F) ⊕ Line F 2)) : Prop :=
  ∀ v ∈ W, k ≤ (Finset.univ.filter fun w => w ∈ W ∧ survAdj f P A S v w).card

/-- The **`k`-core** of the surviving incidence graph: the union of all vertex sets in which every
vertex has at least `k` surviving neighbours. This is what "After these deletions, repeatedly
remove vertices of degree below `k`" (manuscript, sha256 328a8943…, §3.2, p.15) leaves,
whatever the order of removals: the largest vertex set with minimum degree `≥ k`. -/
def kCore {F : Type*} [Field F] [Fintype F] {d : ℕ} (f : (Fin 2 → F) → F)
    (P : LineTable F 2 d) (A S : MvPolynomial (Fin 3) F) (k : ℕ) :
    Set ((Fin 2 → F) ⊕ Line F 2) :=
  {v | ∃ W, IsKClosed f P A S k W ∧ v ∈ W}

/-- The **pruned graph `G`** of Lemma 3.3 (manuscript, sha256 328a8943…, §3.2, pp.15–16): the
bipartite graph on points `inl x` and lines `inr L` of `F²` whose edges are the surviving
incidences between vertices of the `k`-core. Vertices outside the `k`-core are isolated and are
not vertices of the paper's `G`; its point side is `X = {x | inl x ∈ kCore}`, its line side
`T = {L | inr L ∈ kCore}`. -/
def prunedGraph {F : Type*} [Field F] [Fintype F] {d : ℕ} (f : (Fin 2 → F) → F)
    (P : LineTable F 2 d) (A S : MvPolynomial (Fin 3) F) (k : ℕ) :
    SimpleGraph ((Fin 2 → F) ⊕ Line F 2) where
  Adj v w := v ∈ kCore f P A S k ∧ w ∈ kCore f P A S k ∧ survAdj f P A S v w
  symm := ⟨by
    rintro (x | L) (y | M) ⟨hv, hw, h⟩
    · exact h.elim
    · exact ⟨hw, hv, h⟩
    · exact ⟨hw, hv, h⟩
    · exact h.elim⟩
  loopless := ⟨by
    rintro (x | L) ⟨_, _, h⟩
    · exact h
    · exact h⟩

open Classical in
/-- The **edge set `E`** of the pruned graph, as point–line pairs `(x, L)`. -/
noncomputable def prunedEdges {F : Type*} [Field F] [Fintype F] {d : ℕ}
    (f : (Fin 2 → F) → F) (P : LineTable F 2 d) (A S : MvPolynomial (Fin 3) F) (k : ℕ) :
    Finset ((Fin 2 → F) × Line F 2) :=
  Finset.univ.filter fun xL => Sum.inl xL.1 ∈ kCore f P A S k ∧
    Sum.inr xL.2 ∈ kCore f P A S k ∧ Survives f P A S xL.1 xL.2

end LineVsPoint


