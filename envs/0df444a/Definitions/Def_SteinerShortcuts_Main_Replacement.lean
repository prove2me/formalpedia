-- Prove2me | Definitions.Def_SteinerShortcuts_Main_Replacement
-- name    : SteinerShortcuts_Main_Replacement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:34:36.656505+00:00
-- url     : https://prove2.me/theorems/75ce20f2-4fb1-462b-a8a0-ee3f4e0db90f
-- title:
--   Shortest shortcut paths, Steiner components and replacement intervals
-- statement:
--   Let $G$ be a finite layered DAG, $\mathcal P$ its critical family and $G^+$ a Steiner shortcut. Select one shortest path $P^+$ between the endpoints of each $P\in\mathcal P$ and discard added edges used by none of the selected paths. Let $C$ be a weakly connected component of the retained Steiner vertices with an incident retained edge, and let $H$ include the edges incident to $C$ and their original endpoints. Isolated unused Steiner vertices are excluded explicitly.
--
--   For every vertex $x$ of $H$, set $\mathcal F_x=\{P\in\mathcal P:x\in P^+\}$. For an original vertex let $I_x=\{x\}$, and for a Steiner vertex let $I_x$ be the common original vertices of all members of $\mathcal F_x$. Define
--   $$
--   \ell_x=\min\{\operatorname{layer}(v):v\in I_x\},\qquad
--   r_x=\max\{\operatorname{layer}(v):v\in I_x\},\qquad
--   \mu_y=\max\{\ell_u:u\text{ reaches }y\text{ in }H\}.
--   $$
--   The last maximum includes $y$ itself. Empty candidate sets receive endpoints zero only to totalize the definitions; their nonemptiness under (P1), (P2) and the retained-component setup is not assumed and remains to be established. The setup records shortestness through equality to the imported hop distance. No interval intersection or bound on $\mu_y$ is included in a definition.
--
--   This layer supplies the independently auditable setup for Claim A.1 and the non-Steiner replacement template.
-- source:
--   Aaron Bernstein, Henry Fleischmann, Bernhard Haeupler, Gary Hoppenworth, Thatchaphol Saranurak, STOC 2027 submission #1034 (October 2026), pp. 34–35, Appendix A setup of Claim A.1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1034.pdf

import Mathlib
import Definitions.Def_SteinerShortcuts_Main_Graphs

namespace SteinerShortcuts.Main

noncomputable section
open scoped Classical

/-- Chosen shortest paths in the augmentation, one for each original critical path. -/
def ShortestSelection {V W : Type} (G : Digraph V)
    (extra : Finset ((V ⊕ W) × (V ⊕ W))) (paths : Finset (Route V))
    (chosen : Route V → Route (V ⊕ W)) : Prop :=
  ∀ P ∈ paths,
    IsPath (augment G extra) (chosen P) ∧
    (chosen P).start = Sum.inl P.start ∧ (chosen P).finish = Sum.inl P.finish ∧
    ((chosen P).length : ℕ∞) = PredAdvice.dist (augment G extra) (Sum.inl P.start) (Sum.inl P.finish)

/-- Delete only unused added edges, as on printed p.34. -/
def prunedEdges {V W : Type} (extra : Finset ((V ⊕ W) × (V ⊕ W)))
    (paths : Finset (Route V)) (chosen : Route V → Route (V ⊕ W)) :
    Finset ((V ⊕ W) × (V ⊕ W)) :=
  extra.filter fun e => ∃ P ∈ paths, e ∈ (chosen P).arcs

def SteinerAdjacent {V W : Type} (extra : Finset ((V ⊕ W) × (V ⊕ W))) (x y : W) : Prop :=
  (Sum.inr x, Sum.inr y) ∈ extra ∨ (Sum.inr y, Sum.inr x) ∈ extra

/-- A whole weak component of Steiner vertices that has a retained incident edge.
Isolated unused Steiner vertices are excluded, rather than assigned a spurious F_x. -/
def ActiveComponent {V W : Type} (extra : Finset ((V ⊕ W) × (V ⊕ W)))
    (C : Finset W) : Prop :=
  (∃ root ∈ C, ∀ w, w ∈ C ↔ Relation.ReflTransGen (SteinerAdjacent extra) root w) ∧
  ∀ w ∈ C, ∃ e ∈ extra, e.1 = Sum.inr w ∨ e.2 = Sum.inr w

def componentEdges {V W : Type} (extra : Finset ((V ⊕ W) × (V ⊕ W)))
    (C : Finset W) : Finset ((V ⊕ W) × (V ⊕ W)) :=
  extra.filter fun e => ∃ w ∈ C, e.1 = Sum.inr w ∨ e.2 = Sum.inr w

def componentVertices {V W : Type} (extra : Finset ((V ⊕ W) × (V ⊕ W)))
    (C : Finset W) : Finset (V ⊕ W) :=
  ((componentEdges extra C).image Prod.fst) ∪ ((componentEdges extra C).image Prod.snd)

def componentGraph {V W : Type} (extra : Finset ((V ⊕ W) × (V ⊕ W)))
    (C : Finset W) : Digraph (V ⊕ W) where
  Adj x y := (x,y) ∈ componentEdges extra C

def vertexFamily {V W : Type} (paths : Finset (Route V))
    (chosen : Route V → Route (V ⊕ W)) (x : V ⊕ W) : Finset (Route V) :=
  paths.filter fun P => x ∈ (chosen P).vertices

/-- I_x is the singleton {x} for an original vertex, otherwise the common original vertices. -/
def replacements {V W : Type} [Fintype V] (paths : Finset (Route V))
    (chosen : Route V → Route (V ⊕ W)) (x : V ⊕ W) : Finset V :=
  match x with
  | .inl v => {v}
  | .inr _ => Finset.univ.filter fun v => ∀ P ∈ vertexFamily paths chosen x, v ∈ P.vertices

/-- Zero is used only for the unused empty candidate set. In Claim A.1, nonemptiness follows
from P1/P2 and the retained-edge component setup; it is not a hypothesis of the claim. -/
def leftLayer {V W : Type} [Fintype V] (layer : V → ℕ) (paths : Finset (Route V))
    (chosen : Route V → Route (V ⊕ W)) (x : V ⊕ W) : ℕ :=
  let ls := (replacements paths chosen x).image layer
  if h : ls.Nonempty then ls.min' h else 0

def rightLayer {V W : Type} [Fintype V] (layer : V → ℕ) (paths : Finset (Route V))
    (chosen : Route V → Route (V ⊕ W)) (x : V ⊕ W) : ℕ :=
  (replacements paths chosen x).sup layer

/-- Maximum over ancestors inside H, including y itself. -/
def ancestorMax {V W : Type} [Fintype V] (layer : V → ℕ) (paths : Finset (Route V))
    (chosen : Route V → Route (V ⊕ W))
    (extra : Finset ((V ⊕ W) × (V ⊕ W))) (C : Finset W) (y : V ⊕ W) : ℕ :=
  ((componentVertices extra C).filter fun u => Reaches (componentGraph extra C) u y).sup
    (leftLayer layer paths chosen)

end
end SteinerShortcuts.Main


