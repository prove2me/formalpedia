-- Prove2me | Definitions.Def_EvenCycleListing723_Main_GraphModel
-- name    : EvenCycleListing723_Main_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T12:20:36.081952+00:00
-- url     : https://prove2.me/theorems/b292a99a-1941-4ade-b390-f895617b9b47
-- title:
--   Finite graph, cycle-copy, and tree-layer interfaces
-- statement:
--   Let $G$ be a finite simple undirected graph. For an active set $A$, the neighborhood of $u$ consists of its adjacent vertices in $A$; repeated neighborhood expansion defines the radius-$r$ ball. Distinct simple cycles are represented by their edge sets, using the published cycle definition. Thus
--
--   $$t_{2k}(G)=|\{E: E\text{ is a simple cycle edge set in }G,\ |E|=2k\}|.$$
--
--   A vertex list is normalized over all rotations and its reversal. A correct listing contains exactly one canonical list for each cycle edge set. Chords are permitted. In particular, $K_4$ has three copies of $C_4$.
--
--   A rooted tree in $G$ is a connected acyclic graph on a vertex subset, whose edges are ambient edges. Its depth and layers are measured in this tree, without an inducedness or BFS restriction. For disjoint sets $L,R$, the cross-edge count includes every ambient edge between them, and $d_L=|E(L,R)|/|L|$, $d_R=|E(L,R)|/|R|$ are real averages. The constants are
--
--   $$\alpha_k=2^{-6k}(2k)^{-(2k-2)},\qquad S_k=\sum_{h=1}^{k-1}2^{h+2}.$$
--
--   These interfaces support all three lemmas and the headline listing theorem. Empty denominators return zero in Lean; Lemma 3.3's positive degree thresholds rule those cases out. All finite vertex sets are represented by relabeling onto $\mathrm{Fin}(n)$.
-- source:
--   Neha Pant and Virginia Vassilevska Williams, Listing Even Cycles Even Faster, STOC 2027 submission #723 (October 2026), pp.1,4,6–8, cycle-copy convention, Section 2, Lemma 3.3 and proof of Lemma 3.2; canonical PDF https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/723.pdf (SHA256 653ba349d1e9c1a87fe327137dddf959c6871a48cf5a052e91a47e341e9e9d8f)

import Mathlib
import Definitions.Def_ForestBackdoorFPT_cycleEdgeSets

set_option autoImplicit false

namespace EvenCycleListing723.Main

noncomputable section

/-- Section 2, p.4: degrees in the subgraph induced on the active labels. -/
def neighbors {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n) : Finset (Fin n) := by
  classical
  exact A.filter (G.Adj u)

def degree {n : ℕ} (G : SimpleGraph (Fin n)) (u : Fin n) : ℕ :=
  (neighbors G Finset.univ u).card

/-- A finite BFS expansion; disconnected vertices are never at distance zero. -/
def ball {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u : Fin n) : ℕ → Finset (Fin n)
  | 0 => if u ∈ A then {u} else ∅
  | r + 1 => let B := ball G A u r
             B ∪ B.biUnion (neighbors G A)

/-- Edge-set copies, using the published definition; chords are allowed. -/
def cycleCopies {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : Finset (Finset (Sym2 (Fin n))) := by
  classical
  exact Finset.univ.powerset.filter fun E =>
    E.card = 2 * k ∧ (E : Set (Sym2 (Fin n))) ∈ ForestBackdoorFPT.cycleEdgeSets G

def cycleCount {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  (cycleCopies G k).card

/-- All cyclic edges, including last to first; no vertex-set quotient. -/
def sequenceEdges {n : ℕ} (xs : List (Fin n)) : Finset (Sym2 (Fin n)) := by
  classical
  exact (xs.zip (xs.rotate 1)).toFinset.image fun p => s(p.1, p.2)

/-- Canonical representative of the dihedral orbit, sorted lexicographically. -/
def canonical {n : ℕ} (xs : List (Fin n)) : List (Fin n) :=
  (((List.range xs.length).flatMap fun i => [xs.rotate i, xs.reverse.rotate i]).mergeSort
    (fun a b => (compare a b != Ordering.gt))).headD []

def cycleSequence {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (xs : List (Fin n)) : Prop :=
  xs.length = 2 * k ∧ xs.Nodup ∧
    ∀ p ∈ xs.zip (xs.rotate 1), G.Adj p.1 p.2

/-- Exact output: every copy once, with a canonical vertex-list representation. -/
def correctListing {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (L : List (List (Fin n))) : Prop :=
  (∀ xs ∈ L, cycleSequence G k xs ∧ canonical xs = xs) ∧
  (L.map sequenceEdges).Nodup ∧ (L.map sequenceEdges).toFinset = cycleCopies G k

/-- Lemma 3.3, p.6: tree subgraph data, with no BFS or inducedness promise. -/
structure RootedTreeIn {n : ℕ} (G : SimpleGraph (Fin n)) where
  vertices : Finset (Fin n)
  tree : SimpleGraph {v // v ∈ vertices}
  root : {v // v ∈ vertices}
  isTree : tree.IsTree
  subgraph : ∀ a b, tree.Adj a b → G.Adj a.val b.val

def treeLayer {n : ℕ} {G : SimpleGraph (Fin n)} (T : RootedTreeIn G) (j : ℕ) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun v => T.tree.dist T.root v = j).image Subtype.val

def treeDepth {n : ℕ} {G : SimpleGraph (Fin n)} (T : RootedTreeIn G) (h : ℕ) : Prop :=
  (∀ v, T.tree.dist T.root v ≤ h) ∧ ∃ v, T.tree.dist T.root v = h

/-- All ambient edges across the two sets, counted once from left to right. -/
def crossEdges {n : ℕ} (G : SimpleGraph (Fin n)) (L R : Finset (Fin n)) : ℕ := by
  classical
  exact ((L ×ˢ R).filter fun p => G.Adj p.1 p.2).card

def averageLeft {n : ℕ} (G : SimpleGraph (Fin n)) (L R : Finset (Fin n)) : ℝ :=
  (crossEdges G L R : ℝ) / L.card

def averageRight {n : ℕ} (G : SimpleGraph (Fin n)) (L R : Finset (Fin n)) : ℝ :=
  (crossEdges G L R : ℝ) / R.card

def copiesMeeting {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (S : Finset (Fin n)) : ℕ := by
  classical
  exact ((cycleCopies G k).filter fun E => ∃ v ∈ S, ∃ e ∈ E, v ∈ e).card

/-- The exact alpha in Lemma 3.3 (p.6). -/
def alpha (k : ℕ) : ℝ := (1 / (2 : ℝ) ^ (6 * k)) * (1 / (2 * (k : ℝ))) ^ (2 * k - 2)

def bucketSum (k : ℕ) : ℕ := ∑ h ∈ Finset.Icc 1 (k - 1), 2 ^ (h + 2)

/-- Explicit coefficients obtained from the proof on pp.6–8, without logarithmic loss. -/
def pairQuadraticCoefficient (k : ℕ) : ℝ := 2 * (1 + 512 * (k : ℝ) ^ 2 * bucketSum k)
def pairCycleCoefficient (k : ℕ) : ℝ := 16 * (k : ℝ) ^ 2 * bucketSum k / alpha k

end
end EvenCycleListing723.Main


