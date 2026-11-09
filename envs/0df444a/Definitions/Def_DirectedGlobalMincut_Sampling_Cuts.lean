-- Prove2me | Definitions.Def_DirectedGlobalMincut_Sampling_Cuts
-- name    : DirectedGlobalMincut_Sampling_Cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:59:02.987212+00:00
-- url     : https://prove2.me/theorems/d888fdcc-3740-49e5-9246-0a2a5c7f6a74
-- title:
--   Directed cuts, spanning rooted arborescences and their polytope
-- statement:
--   A finite directed graph has separate arc identities with tail and head maps. For a nonempty proper vertex set $S$, let $\delta^-(S)$ be its entering arcs. A minimum incoming cut minimizes
--
--   $$w(\delta^-(S))=\sum_{e\in\delta^-(S)}w_e.$$
--
--   A rooted cut is nonempty and excludes the specified root $r$. The tree predicate wraps the published out-arborescence with all vertices present and root $r$. Its incidence vector $1_T$ defines the polytope $A_r=\operatorname{conv}\{1_T\}$. A vector $q$ dominates this polytope when it is nonnegative and bounds some point of $A_r$ coordinatewise; that point is not algorithmic input. Tree paths are undirected, defined by deletion of a tree arc separating the endpoints.
--
--   The global input domain has $n\ge2$, $m\ge n$, positive integral weights at most $W$, and $m,W\le n^b$ for the fixed bound exponent $b$. Reversal exchanges the tail and head maps without changing arc identities. These definitions retain zero cuts, loops and parallel arcs.
-- source:
--   Henry Fleischmann, Jason Li, Thatchaphol Saranurak, Benyu Wang, STOC 2027 submission #504 (October 2026), §1 standing assumptions; §2 definitions; §4.1 undirected paths, pp.1–2,5, p. 2 (PDF p. 2); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/504.pdf

import Mathlib
import Definitions.Def_BasicPackArb_Main_RootedDigraph

namespace DirectedGlobalMincut.Sampling

open BasicPackArb.Main

/-- Enumerating vertices and arc identities changes neither parallel arcs nor loops (§1–2, pp.1–2). -/
abbrev Graph (n m : ℕ) := Digraph (Fin n) (Fin m)

/-- The enumeration of the arc set is exhaustive. -/
def AllArcs {n m : ℕ} (G : Graph n m) : Prop := G.arcs = Finset.univ

/-- A nonempty proper incoming cut. -/
def IsCut {n : ℕ} (S : Finset (Fin n)) : Prop := S.Nonempty ∧ S ≠ Finset.univ

def IsRootedCut {n : ℕ} (r : Fin n) (S : Finset (Fin n)) : Prop := S.Nonempty ∧ r ∉ S

noncomputable def cutWeight {n m : ℕ} (G : Graph n m) (w : Fin m → ℝ)
    (S : Finset (Fin n)) : ℝ := ∑ e ∈ G.enteringArcs S, w e

def IsMinimumCut {n m : ℕ} (G : Graph n m) (w : Fin m → ℝ)
    (S : Finset (Fin n)) : Prop :=
  IsCut S ∧ ∀ U, IsCut U → cutWeight G w S ≤ cutWeight G w U

def IsRootedMinimum {n m : ℕ} (G : Graph n m) (w : Fin m → ℝ)
    (r : Fin n) (S : Finset (Fin n)) : Prop :=
  IsRootedCut r S ∧ ∀ U, IsRootedCut r U → cutWeight G w S ≤ cutWeight G w U

def reverseGraph {n m : ℕ} (G : Graph n m) : Graph n m :=
  ⟨G.head, G.tail, G.arcs⟩

/-- A spanning out-arborescence, using the published arborescence without changing its direction. -/
def IsTree {n m : ℕ} (G : Graph n m) (r : Fin n) (T : Finset (Fin m)) : Prop :=
  ∃ A : Arborescence G, A.verts = Finset.univ ∧ A.root = r ∧ A.arcs = T

noncomputable def incidence {m : ℕ} (T : Finset (Fin m)) (e : Fin m) : ℝ :=
  if e ∈ T then 1 else 0

noncomputable def arborescencePolytope {n m : ℕ} (G : Graph n m) (r : Fin n) :
    Set (Fin m → ℝ) := convexHull ℝ {x | ∃ T, IsTree G r T ∧ x = incidence T}

def Dominates {n m : ℕ} (G : Graph n m) (r : Fin n) (q : Fin m → ℝ) : Prop :=
  (∀ e, 0 ≤ q e) ∧ ∃ x ∈ arborescencePolytope G r, ∀ e, x e ≤ q e

def OneRespects {n m : ℕ} (G : Graph n m) (T : Finset (Fin m))
    (S : Finset (Fin n)) : Prop := (T ∩ G.enteringArcs S).card = 1

/-- Undirected connectivity along precisely the supplied arc identities. -/
def UndirectedReach {n m : ℕ} (G : Graph n m) (T : Finset (Fin m)) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (fun x y => ∃ e ∈ T,
    (G.tail e = x ∧ G.head e = y) ∨ (G.tail e = y ∧ G.head e = x)) u v

/-- On a tree, deleting f disconnects the endpoints of e exactly when f lies on their path.
This gives the unique undirected path, including an empty path for a loop (§4.1, p.5). -/
noncomputable def pathEdges {n m : ℕ} (G : Graph n m) (T : Finset (Fin m))
    (e : Fin m) : Finset (Fin m) := by
  classical
  exact T.filter (fun f => ¬ UndirectedReach G (T.erase f) (G.tail e) (G.head e))

/-- The integral input domain of §1. No connectivity promise is made. -/
def InputDomain {n m : ℕ} (b : ℕ) (G : Graph n m) (W : ℕ) (w : Fin m → ℕ) : Prop :=
  2 ≤ n ∧ n ≤ m ∧ AllArcs G ∧ m ≤ n ^ b ∧ W ≤ n ^ b ∧
    ∀ e, 1 ≤ w e ∧ w e ≤ W

end DirectedGlobalMincut.Sampling


