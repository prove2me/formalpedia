-- Prove2me | Definitions.Def_ImprovedSteinerForest_Main_AuxForest
-- name    : ImprovedSteinerForest_Main_AuxForest
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:28:44.677179+00:00
-- url     : https://prove2.me/theorems/ff364400-7986-46fc-ac52-29c439fb02fb
-- title:
--   The auxiliary forest T₀ of a growth history and mst(T₀/𝒮)
-- statement:
--   Fix a growth run and an active class $A$, and replay the recorded mergers. When a merger joins two moats $X$ and $Y$ that both meet $A$, an **auxiliary edge** joins the vertex of $A\cap X$ with the largest label to the vertex of $A\cap Y$ with the largest label, with cost twice the merger time. The edges for $A$ form the tree $T_A$; the **auxiliary forest** is $T_0=\bigcup_A T_A$ and $c(T_0)$ is its total cost.
--
--   For a collection $\mathcal S$ of vertex sets, $\mathrm{mst}(T_0/\mathcal S)$ is the sum, over the active classes, of the minimum spanning tree costs within each class after the vertices of each set of $\mathcal S$ are identified:
--   $$\mathrm{mst}(T_0/\mathcal S)=\min\Bigl\{\textstyle\sum_{e\in X}c_e:\ X\subseteq T_0,\ X \text{ together with the identifications of } \mathcal S \text{ connects every active class}\Bigr\}.$$
--
--   These objects (§4.1) express gain as a spanning-tree saving (Lemma 4.1).
--
--   **Formalization Note.** $T_0$ is a list of triples (endpoint, endpoint, cost) in the order of the recorded mergers, one entry per (merger, class). Since active classes are disjoint and every auxiliary edge stays within its class, the minimum over sets of auxiliary edges connecting every class is the sum of the per-class minimum spanning trees. If no set of auxiliary edges connects every class (impossible on a run, since $T_A$ spans $A$), the value is $0$.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), pp. 19–20, §4.1

import Mathlib
import Definitions.Def_ImprovedSteinerForest_Main_Instance
import Definitions.Def_ImprovedSteinerForest_Main_Growth
set_option autoImplicit false

namespace ImprovedSteinerForest.Main

open Finset

namespace GrowthRun

variable {I : Instance} (R : GrowthRun I)

open scoped Classical in
/-- The auxiliary edges created by the merger of step `k` (§4.1, p. 19): if step `k` merges the
moats `X ∋ eu f` and `Y ∋ ev f`, then for every active class `A` meeting both, an auxiliary edge
joins the largest-label vertex of `A ∩ X` to the largest-label vertex of `A ∩ Y`, with cost twice
the merger time. -/
noncomputable def auxEdgesAt (k : ℕ) : List (Fin I.n × Fin I.n × ℚ) :=
  match R.merge k with
  | none => []
  | some f =>
    let X := R.moatOf k (I.eu f)
    let Y := R.moatOf k (I.ev f)
    R.activeClasses.toList.filterMap (fun A =>
      if h : (A ∩ X).Nonempty ∧ (A ∩ Y).Nonempty then
        some ((A ∩ X).max' h.1, (A ∩ Y).max' h.2, 2 * R.time k)
      else none)

/-- The auxiliary forest `T₀ = ⋃_A T_A` (§4.1, p. 19), as the list of its edges `(u, v, cost)` in
the order of the recorded mergers. -/
noncomputable def auxEdges : List (Fin I.n × Fin I.n × ℚ) :=
  (List.range R.len).flatMap R.auxEdgesAt

/-- `c(T₀)`, the total cost of the auxiliary edges. -/
noncomputable def auxCost : ℚ := (R.auxEdges.map (fun e => e.2.2)).sum

/-- The graph on `Fin n` with the auxiliary edges indexed by `X` and, for every set `S ∈ 𝒮`, all
pairs of vertices of `S` joined (the graph `T₀/𝒮` restricted to `X`, before identification). -/
noncomputable def auxGraphMod (𝒮 : Finset (Finset (Fin I.n))) (X : Finset (Fin R.auxEdges.length)) :
    SimpleGraph (Fin I.n) :=
  SimpleGraph.fromRel (fun x y =>
    (∃ i ∈ X, (R.auxEdges.get i).1 = x ∧ (R.auxEdges.get i).2.1 = y) ∨ ∃ S ∈ 𝒮, x ∈ S ∧ y ∈ S)

open scoped Classical in
/-- `mst(T₀/𝒮)` (§4.1, p. 20): the sum, over the original active classes, of the minimum spanning
tree costs of `T₀` after identifying the vertices of each set of `𝒮`; that is, the minimum cost of
a set `X` of auxiliary edges that, together with the identifications, connects every active class
(the classes are disjoint and every auxiliary edge stays within its class). `0` if no such `X`
exists, which never happens on a run (`T₀` spans every class). -/
noncomputable def mstMod (𝒮 : Finset (Finset (Fin I.n))) : ℚ :=
  let feas := (univ : Finset (Finset (Fin R.auxEdges.length))).filter (fun X =>
    ∀ A ∈ R.activeClasses, ∀ u ∈ A, ∀ v ∈ A, (R.auxGraphMod 𝒮 X).Reachable u v)
  if h : feas.Nonempty then feas.inf' h (fun X => ∑ i ∈ X, (R.auxEdges.get i).2.2) else 0

end GrowthRun

end ImprovedSteinerForest.Main


