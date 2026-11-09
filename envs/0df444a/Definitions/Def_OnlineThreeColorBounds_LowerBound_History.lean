-- Prove2me | Definitions.Def_OnlineThreeColorBounds_LowerBound_History
-- name    : OnlineThreeColorBounds_LowerBound_History
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:09.728196+00:00
-- url     : https://prove2.me/theorems/fb86fa50-c3e1-40f0-b2bd-aaf6aaac5a7f
-- title:
--   Ordered graph histories, fold colors, sides, and post-degree
-- statement:
--   An ordered graph is revealed by adding one vertex at a time. A record contains the arriving vertex's earlier neighbors and its irrevocable finite set of color names. A history $h$ is the chronological list of records; its graph has the $|h|$ arrival indices as vertices. Only the later endpoint's record determines an edge. A legal $t$-fold history assigns exactly $t$ distinct colors at each arrival and avoids all colors of its earlier neighbors.
--
--   For a set $S$ of arrived vertices define
--   $$
--   \operatorname{col}_h(S)=\bigcup_{v\in S}\operatorname{col}_h(v),\qquad C(h)=\left|\operatorname{col}_h(V)\right|.
--   $$
--   A covering bipartition consists of two disjoint sides covering all vertices, with every edge crossing. Its two-sided colors are $\operatorname{col}_h(S)\cap\operatorname{col}_h(R)$. The post-degree of vertex $v$ is the number of its neighbors arriving later than $v$.
--
--   These definitions distinguish online outputs from offline graph colorability and supply the common counting conventions for all five lemmas. Empty histories and empty sides are allowed. Neither connectedness nor use of all three offline colors is required.
--
--   Differences from the source:
--   - encoding: finite ordered graphs and t-element online color sets → chronological lists of earlier-neighbor and natural-color finsets; the resulting graph has carrier Fin h.length; reason: arrival indices encode every finite order, and arbitrary finite color sets can be renamed into the unbounded natural palette
--   - encoding: two sides of a bipartite graph, and col of a side → Mathlib IsBipartiteWith plus union equal to the entire vertex set, and finset unions of assigned colors; reason: isolated vertices must belong to a side; colors are counted by distinct names and two-sidedness is global across components
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a, §1, printed p. 1 / PDF p. 2; §2–2.2, printed pp. 5–6 / PDF pp. 6–7

import Mathlib
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound

/-- Chronological records: earlier neighbors, then the irrevocable color set. -/
abbrev History := List (Finset ℕ × Finset ℕ)

def neighborsAt (h : History) (i : ℕ) : Finset ℕ := (h.getD i (∅, ∅)).1

def colorsAt (h : History) (i : ℕ) : Finset ℕ := (h.getD i (∅, ∅)).2

/-- Arrival indices identify vertices; a later record alone determines an edge. -/
def historyGraph (h : History) : SimpleGraph (Fin h.length) where
  Adj u v := u ≠ v ∧ min u.val v.val ∈ neighborsAt h (max u.val v.val)
  symm := ⟨by
    intro u v huv
    exact ⟨Ne.symm huv.1, by simpa only [min_comm, max_comm] using huv.2⟩⟩
  loopless := ⟨by intro u hu; exact hu.1 rfl⟩

/-- No restriction on color names except exact multiplicity and avoidance of neighbors. -/
def LegalResponse (t : ℕ) (h : History) (s x : Finset ℕ) : Prop :=
  x.card = t ∧ ∀ j ∈ s, Disjoint x (colorsAt h j)

/-- All old records have earlier-only edges and proper, exact-size color sets. -/
def LegalHistory (t : ℕ) (h : History) : Prop :=
  ∀ i < h.length, neighborsAt h i ⊆ Finset.range i ∧
    LegalResponse t (h.take i) (neighborsAt h i) (colorsAt h i)

def allColors (h : History) : Finset ℕ :=
  (Finset.range h.length).biUnion (colorsAt h)

def colorCount (h : History) : ℕ := (allColors h).card

def colorsOn (h : History) (s : Finset (Fin h.length)) : Finset ℕ :=
  s.biUnion (fun v => colorsAt h v.val)

/-- Includes isolated vertices, and permits empty sides. -/
def CoveringBipartition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (s r : Finset V) : Prop :=
  G.IsBipartiteWith (s : Set V) (r : Set V) ∧ s ∪ r = Finset.univ

/-- Colors on opposite sides anywhere in the whole graph, including different components. -/
def twoSidedColors (h : History) (s r : Finset (Fin h.length)) : Finset ℕ :=
  colorsOn h s ∩ colorsOn h r

/-- Counts later neighbors, rather than earlier neighbors or total degree. -/
noncomputable def postDegree (h : History) (v : Fin h.length) : ℕ := by
  classical
  exact (Finset.univ.filter (fun w : Fin h.length => v.val < w.val ∧
    (historyGraph h).Adj v w)).card

end OnlineThreeColorBounds.LowerBound


