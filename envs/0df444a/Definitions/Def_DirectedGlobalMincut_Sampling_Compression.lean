-- Prove2me | Definitions.Def_DirectedGlobalMincut_Sampling_Compression
-- name    : DirectedGlobalMincut_Sampling_Compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:01:11.242284+00:00
-- url     : https://prove2.me/theorems/7bd0bb95-12ff-46a7-a598-c8e0d68942d7
-- title:
--   Explicit heavy-light and segment-tree compression
-- statement:
--   The underlying rooted tree determines descendant-subtree sizes. A tree edge is heavy when the child subtree exceeds half its parent's subtree; all other tree edges are light. Maximal heavy chains and singleton light edges partition the tree arcs. Each nonempty chain is given the published balanced segment tree over its edge indices. Its leaves are the original tree-edge sinks, and internal nodes are zero-demand Steiner vertices.
--
--   For each original arc $e$, let $P_T(e)$ be its undirected tree path. The compressed network contains
--
--   $$y_e\longrightarrow\text{the maximal segment nodes contained in }P_T(e),$$
--
--   and downward parent-to-child segment arcs, all of infinite capacity. Source arcs, their $q_e$ capacities, and their demands are retained. The projection reads exactly those source arcs, with the same zero convention at the root.
--
--   This defines the actual heavy-light/segment-tree construction, rather than allowing any network with a chosen reachability relation. Empty chains create no nodes. The extensional data definition does not itself claim an efficient implementation; the algorithmic theorem targets must establish the cost of constructing their queries.
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), §4.4, pp.7–9; Lemma 4.3, p. 8 (PDF p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_DirectedGlobalMincut_Sampling_Flows
import Definitions.Def_MenuPricing_segTree

open scoped ENNReal NNReal

namespace DirectedGlobalMincut.Sampling

/-- Descendants include the vertex itself. -/
noncomputable def subtreeSize {n m : ℕ} (G : Graph n m) (T : Finset (Fin m)) (v : Fin n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun u => Relation.ReflTransGen
    (fun x y => ∃ e ∈ T, G.tail e = x ∧ G.head e = y) v u)).card

/-- A standard heavy-light choice: an edge to a subtree larger than half its parent's subtree.
At most one such child exists; all other tree edges are light (§4.4, pp.7–9). -/
noncomputable def heavyEdges {n m : ℕ} (G : Graph n m) (T : Finset (Fin m)) : Finset (Fin m) := by
  classical
  exact T.filter (fun e => subtreeSize G T (G.tail e) < 2 * subtreeSize G T (G.head e))

noncomputable def heavyChain {n m : ℕ} (G : Graph n m) (T : Finset (Fin m)) :
    ℕ → Fin n → List (Fin m)
  | 0, _ => []
  | fuel + 1, v =>
      match ((heavyEdges G T).filter (fun e => G.tail e = v)).sort (· ≤ ·) |>.head? with
      | none => []
      | some e => e :: heavyChain G T fuel (G.head e)

/-- Heavy paths are indexed by their top vertex; each light edge is a singleton piece. -/
abbrev PieceKey (n m : ℕ) := Fin n ⊕ Fin m

/-- An actual maximal heavy chain, or one light edge. Empty heavy chains have no segment nodes. -/
noncomputable def pieceEdges {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) :
    PieceKey n m → List (Fin m)
  | .inl v =>
      if v = r ∨ ∃ e ∈ T \ heavyEdges G T, G.head e = v then heavyChain G T n v else []
  | .inr e => if e ∈ T \ heavyEdges G T then [e] else []

/-- The published balanced segment-tree construction, over indices of this edge list. -/
def segmentIntervals {A : Type} (es : List A) : List (ℕ × ℕ × ℕ) :=
  if es.isEmpty then [] else MenuPricing.segTree 0 es.length 0

def intervalChild (p q : ℕ × ℕ × ℕ) : Prop :=
  q.2.2 = p.2.2 + 1 ∧ p.1 ≤ q.1 ∧ q.2.1 ≤ p.2.1

def intervalEdges {A : Type} (es : List A) (p : ℕ × ℕ × ℕ) : List A :=
  (es.drop p.1).take (p.2.1 - p.1)

/-- Maximal contained segment nodes: exactly the usual disjoint canonical cover. -/
noncomputable def intervalCover {A : Type} [DecidableEq A] (es : List A) (F : Finset A) :
    Finset (ℕ × ℕ × ℕ) := by
  classical
  exact (segmentIntervals es).toFinset.filter (fun p =>
    (intervalEdges es p).toFinset ⊆ F ∧
      ∀ parent ∈ segmentIntervals es, intervalChild parent p →
        ¬ (intervalEdges es parent).toFinset ⊆ F)

noncomputable def segmentPositions {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) :
    Finset (PieceKey n m × (ℕ × ℕ × ℕ)) := by
  classical
  exact Finset.univ.biUnion (fun key =>
    ((segmentIntervals (pieceEdges G r T key)).map (key, ·)).toFinset)

abbrev SegmentNode {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) :=
  ↥(segmentPositions G r T)

abbrev CompressedNode {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) :=
  {v : Fin n // v ≠ r} ⊕ (Fin m ⊕ SegmentNode G r T)

noncomputable def compressedAdj {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) :
    CompressedNode G r T → CompressedNode G r T → Prop
  | .inl v, .inr (.inl e) => e ∈ G.arcs ∧ G.head e = v.val
  | .inr (.inl e), .inr (.inr p) => e ∈ G.arcs ∧
      p.val.2 ∈ intervalCover (pieceEdges G r T p.val.1) (pathEdges G T e)
  | .inr (.inr p), .inr (.inr q) => p.val.1 = q.val.1 ∧ intervalChild p.val.2 q.val.2
  | _, _ => False

/-- Explicit heavy-light/segment-tree compression. Leaves themselves are the tree-edge sinks.
No arbitrary network or reachability certificate is supplied by the caller. -/
noncomputable def compressedNetwork {n m : ℕ} (G : Graph n m) (r : Fin n)
    (T : Finset (Fin m)) (q : Fin m → ℝ) :
    Network (CompressedNode G r T) (CompressedNode G r T × CompressedNode G r T) := by
  classical
  exact {
    graph := ⟨Prod.fst, Prod.snd, Finset.univ.filter (fun a => compressedAdj G r T a.1 a.2)⟩
    capacity := fun a => match a with
      | (.inl _, .inr (.inl e)) => ENNReal.ofReal (q e)
      | _ => ⊤
    demand := fun v => match v with
      | .inl _ => -1
      | .inr (.inl _) => 0
      | .inr (.inr p) => if p.val.2.2.1 = p.val.2.1 + 1 then 1 else 0 }

noncomputable def compressedProjection {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m))
    (g : (CompressedNode G r T × CompressedNode G r T) → ℝ) (e : Fin m) : ℝ :=
  if h : G.head e ≠ r then g (.inl ⟨G.head e, h⟩, .inr (.inl e)) else 0

end DirectedGlobalMincut.Sampling


