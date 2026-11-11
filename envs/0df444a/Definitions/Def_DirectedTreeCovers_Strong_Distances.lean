-- Prove2me | Definitions.Def_DirectedTreeCovers_Strong_Distances
-- name    : DirectedTreeCovers_Strong_Distances
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:39.524242+00:00
-- url     : https://prove2.me/theorems/b15f1f47-4da9-47c7-9f47-0ac95f33d921
-- title:
--   Directed weighted walks and extended distances
-- statement:
--   Let $G=(V,E,\omega)$ be a finite directed graph. A walk in a subgraph uses original edge identities in their given directions, stays in its vertex set, and has length equal to the sum of its inherited nonnegative weights. The empty walk at a present vertex has length zero. Define
--
--   $$d_H(u,v)=\inf\{\ell(P):P\text{ is a directed walk in }H\text{ from }u\text{ to }v\},\qquad r_H(u,v)=d_H(u,v)+d_H(v,u).$$
--
--   Distances take values in $[0,\infty]$, with infinity for a missing walk or absent endpoint. Roundtrip distance describes a closed walk and permits repeated vertices. The file also defines the nonnegative-weight and strong-connectivity predicates and the minimum number of edges among shortest walks, used to break zero-weight ties in searches. These definitions supply the common distance layer for every item.
--
--   **Formalization Note** The published graph carrier has head = source and tail = target. Nonnegativity is an explicit theorem assumption. The minimum-hop function has a totalized empty-set value zero, but searches use it only on reachable vertices of finite nonnegative graphs, where a shortest walk exists.
-- source:
--   Gur Lifshitz, Shiri Chechik, STOC 2027 submission #840 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/840.pdf, §2, printed p.6 (PDF p.7); shortest-path searches in §4.1, printed p.13 (PDF p.14), and §5.1, printed p.16 (PDF p.17)

import Mathlib
import Definitions.Def_EulerSparsify_DiGraph

noncomputable section

namespace DirectedTreeCovers.Strong

open scoped Classical
open EulerSparsify

variable {V E : Type} [Fintype V] [Fintype E]

/-- Nonnegativity is a separate assumption, including zero weights (§2, printed p.6 / PDF p.7). -/
def Nonnegative (G : DiGraph V E) : Prop := ∀ e, 0 ≤ G.w e

/-- Directed edge walks in a subgraph with vertex set X and original edge identities F.
The empty walk exists only at a vertex of X. Head is source in the published carrier. -/
def WalkIn (G : DiGraph V E) (X : Finset V) (F : Finset E) :
    V → V → List E → Prop
  | u, v, [] => u = v ∧ u ∈ X
  | u, v, e :: p => u ∈ X ∧ e ∈ F ∧ G.head e = u ∧ WalkIn G X F (G.tail e) v p

/-- Inherited nonnegative edge lengths; under Nonnegative, ofReal changes no weight. -/
def walkLength (G : DiGraph V E) (p : List E) : ENNReal :=
  (p.map (fun e => ENNReal.ofReal (G.w e))).sum

/-- Infinity for no walk, including a missing endpoint; no real infimum is used (§2). -/
def subdist (G : DiGraph V E) (X : Finset V) (F : Finset E) (u v : V) : ENNReal :=
  ⨅ (p : List E) (_ : WalkIn G X F u v p), walkLength G p

/-- Distance in the induced subgraph on X. -/
def inducedDist (G : DiGraph V E) (X : Finset V) (u v : V) : ENNReal :=
  subdist G X Finset.univ u v

def dist (G : DiGraph V E) (u v : V) : ENNReal := inducedDist G Finset.univ u v

/-- The shortest closed walk through the two vertices, not a simple cycle. -/
def roundtrip (G : DiGraph V E) (u v : V) : ENNReal := dist G u v + dist G v u

def inducedRoundtrip (G : DiGraph V E) (X : Finset V) (u v : V) : ENNReal :=
  inducedDist G X u v + inducedDist G X v u

def StronglyConnected (G : DiGraph V E) : Prop := ∀ u v, dist G u v ≠ ⊤

/-- Minimum edge count among shortest walks. Its empty-set default is used only on bad
inputs; searches include only reachable vertices. This breaks zero-weight cycles. -/
def shortestHops (G : DiGraph V E) (X : Finset V) (u v : V) : ℕ :=
  sInf {m | ∃ p : List E, WalkIn G X Finset.univ u v p ∧
    p.length = m ∧ walkLength G p = inducedDist G X u v}

end DirectedTreeCovers.Strong


