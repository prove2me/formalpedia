-- Prove2me | Definitions.Def_OnlineThreeColorBounds_LowerBound_Supplement_Graphs
-- name    : OnlineThreeColorBounds_LowerBound_Supplement_Graphs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:36:51.353767+00:00
-- url     : https://prove2.me/theorems/ebcd058a-bd61-4992-9abf-cd9dee153a7e
-- title:
--   Offline-monochromatic classes, sides of components, and the CBIP rule
-- statement:
--   This file fixes the graph objects of §3.4 of the paper.
--
--   1. Let $G$ be a graph. A set $S$ of vertices is an **offline-monochromatic class** of $G$ when every proper coloring of $G$ with at most three colors is constant on $S$: for every proper $c:V(G)\to\{1,2,3\}$ and all $x,y\in S$, $c(x)=c(y)$.
--   2. For a graph $H$ and a vertex $x$, the **even side** of $x$ is the set of vertices $y$ joined to $x$ by a walk of even length, and the **odd side** is the set of vertices joined to $x$ by a walk of odd length. When the component of $x$ is bipartite, these are the side of that component containing $x$ and the side opposite $x$.
--   3. **CBIP** (Lovász, Saks and Trotter) is the deterministic online coloring rule that gives the arriving vertex $v$ the color
--   $$c=\min\Bigl(\mathbb N_{>0}\setminus\bigcup_{u\in Y}\operatorname{col}(u)\Bigr),$$
--   where $Y$ is the side opposite $v$ of $v$'s connected component in the graph revealed so far, $v$ included. Colors are the positive integers $1,2,\dots$, one per vertex.
--
--   The class notion is used by Lemma 3.1, and the CBIP rule and the two sides by Lemma 3.2.
--
--   **Formalization Note** A proper coloring with at most three colors is a Mathlib `G.Coloring (Fin 3)`. CBIP is an `OnlineRule` of the published base definition `OnlineAlgorithm`. It reads the base `History` of earlier records, builds the revealed graph with the arriving vertex as its last vertex (published `historyGraph`), and takes `sInf` of the positive integers absent from the colors on the odd side. That set is nonempty because only finitely many colors occur, so `sInf` is its least element. On a component that is not bipartite the odd side is the whole component. Lemma 3.2 assumes bipartiteness, so this case never arises there.
-- source:
--   Yaqiao Li, New bounds for online coloring three-colorable graphs, STOC 2027 submission #425 (October 2026), pinned submission PDF SHA256 ca491d3191fa544c55ed3f45022e4cb14e5570bbd8b8bfb36e98205a8a5c518a; offline-monochromatic class §1.1, printed p. 1 / PDF p. 2; CBIP §1.1, printed p. 2 / PDF p. 3 and rule (3.3), printed p. 13 / PDF p. 14

import Definitions.Def_OnlineThreeColorBounds_LowerBound_OnlineAlgorithm
set_option autoImplicit false

namespace OnlineThreeColorBounds.LowerBound.Supplement

open OnlineThreeColorBounds.LowerBound

/-- A vertex set `S` is an offline-monochromatic class of `G` when every proper coloring of `G`
with at most three colors is constant on `S` (§1, p. 1). Colorings into `Fin 3` represent every
proper coloring with at most three colors. -/
def OfflineMonochromatic {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ c : G.Coloring (Fin 3), ∀ x ∈ S, ∀ y ∈ S, c x = c y

/-- The vertices joined to `x` by a walk of even length in `H`. In a connected bipartite
component this is the side of the component containing `x`. -/
def evenSide {V : Type*} (H : SimpleGraph V) (x : V) : Set V :=
  {y | ∃ p : H.Walk x y, Even p.length}

/-- The vertices joined to `x` by a walk of odd length in `H`. In a connected bipartite
component this is the side of the component opposite `x`. -/
def oddSide {V : Type*} (H : SimpleGraph V) (x : V) : Set V :=
  {y | ∃ p : H.Walk x y, Odd p.length}

/-- The CBIP trial color of Lovász–Saks–Trotter (rule (3.3), p. 13): after the records `h`, a
vertex arrives with earlier-neighbor set `s`. In the graph revealed so far (the arriving vertex
included), let `Y` be the side of its connected component opposite it; the color is the least
positive integer absent from the colors on `Y`. The set of candidates is nonempty because only
finitely many colors occur. -/
noncomputable def cbipColor (h : History) (s : Finset ℕ) : ℕ := by
  classical
  let h' : History := h ++ [(s, ∅)]
  let v : Fin h'.length := ⟨h.length, by simp [h']⟩
  let Y : Finset (Fin h'.length) :=
    Finset.univ.filter (fun u => u ∈ oddSide (historyGraph h') v)
  exact sInf {c : ℕ | 0 < c ∧ c ∉ colorsOn h' Y}

/-- CBIP as a deterministic online rule: one color per arriving vertex. -/
noncomputable def cbip : OnlineRule := fun h s => {cbipColor h s}

end OnlineThreeColorBounds.LowerBound.Supplement


