-- Prove2me | Definitions.Def_SharpPauliEntanglement_Exact_PathTree
-- name    : SharpPauliEntanglement_Exact_PathTree
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:55:11.199199+00:00
-- url     : https://prove2.me/theorems/0fdd626b-73c6-48f1-8deb-9c922648ce7c
-- title:
--   Canonical simple-path tree, endpoint map, and red-component preservation
-- statement:
--   Fix a vertex $v$ in a finite simple graph $G$. The simple-path tree has one vertex for each distinct-vertex path $(v=v_0,\ldots,v_k)$ in $G$. A child extends a path by one vertex, the root is $(v)$, and the endpoint map is $\pi(v_0,\ldots,v_k)=v_k$. An extension edge is red exactly when its projected edge belongs to the spanning red subgraph $A\subseteq G$.
--
--   $$p\sim q\quad\Longleftrightarrow\quad q=p\mathbin{+\!+}[a]\ \text{or}\ p=q\mathbin{+\!+}[a],\qquad \pi(p)=\operatorname{last}(p).$$
--
--   A lift preserves red components when the image map $C\mapsto\pi(C)$ bijects the red components of the lift onto those of $A[\gamma]$. The theorem separately requires that endpoints biject the whole lifted set onto $\gamma$.
--
--   This is the particular simple-path tree constructed in Lemma 3.6, not an arbitrary covering tree. Its connected sums can therefore be compared with those of the original graph.
--
--   **Formalization Note** The finite carrier is explicitly enumerated from lists of length at most $|V|$, filtered for distinct vertices, adjacency, and root. Tree graphs on lists are used only on this carrier. The endpoint default on an empty list is the root; no path on the carrier is empty.
-- source:
--   Bobak T. Kiani, Sharp universal death of entanglement threshold for Pauli Hamiltonians, STOC 2027 submission #159 (October 2026), p. 14, Lemma 3.6 and Eq. (3.22)

import Definitions.Def_SharpPauliEntanglement_Exact_GraphWeights

set_option autoImplicit false
noncomputable section

attribute [local instance] Classical.decEq Classical.propDecidable
open scoped BigOperators
namespace SharpPauliEntanglement.Exact

/-- Explicit finite enumeration of the simple paths in Eq. (3.22).
Lists of length at most |V| are filtered for distinct vertices, edges, and root. -/
def simplePaths {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : Finset (List V) :=
  ((Finset.range (Fintype.card V + 1)).biUnion (fun k =>
    (Finset.univ : Finset (Fin k → V)).image List.ofFn)).filter
      (fun p => p.Nodup ∧ p.head? = some v ∧ p.IsChain G.Adj)

/-- Endpoint; its default is never used on a simple path, since root paths are nonempty. -/
def pathEndpoint {V : Type} (v : V) (p : List V) : V := p.getLast?.getD v

def IsPathChild {V : Type} (v : V) (p q : List V) : Prop :=
  q = p ++ [pathEndpoint v q]

/-- Only the finite carrier `simplePaths G v` is part of the tree. -/
def pathTree {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) : SimpleGraph (List V) where
  Adj p q := p ∈ simplePaths G v ∧ q ∈ simplePaths G v ∧ p ≠ q ∧
    (IsPathChild v p q ∨ IsPathChild v q p)
  symm := ⟨by intro p q h; exact ⟨h.2.1, h.1, h.2.2.1.symm, h.2.2.2.symm⟩⟩
  loopless := ⟨by intro p h; exact h.2.2.1 rfl⟩

/-- A tree edge is red exactly when its projected endpoint edge is red. -/
def redPathTree {V : Type} [Fintype V] [DecidableEq V]
    (G A : SimpleGraph V) (v : V) : SimpleGraph (List V) where
  Adj p q := (pathTree G v).Adj p q ∧ A.Adj (pathEndpoint v p) (pathEndpoint v q)
  symm := ⟨by intro p q h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro p h; exact (pathTree G v).loopless.irrefl p h.1⟩

def pathChildren {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (p : List V) : Finset (List V) :=
  (simplePaths G v).filter (IsPathChild v p)

/-- Red-component bijection, specified by the endpoint image on entire components. -/
def PreservesRedComponents {V : Type} [Fintype V] [DecidableEq V]
    (G A : SimpleGraph V) (v : V) (lift : Finset (List V)) (γ : Finset V) : Prop :=
  Set.BijOn (fun C : Finset (List V) => C.image (pathEndpoint v))
    (components (redPathTree G A v) lift : Set (Finset (List V)))
    (components A γ : Set (Finset V))

end SharpPauliEntanglement.Exact


