-- Prove2me | Definitions.Def_RandDelMatroid_Indep_Graphic
-- name    : RandDelMatroid_Indep_Graphic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T18:28:30.879364+00:00
-- url     : https://prove2.me/theorems/f603a2a3-eb4f-4b80-829a-865f62714b13
-- title:
--   Graphic and cographic matroids of multigraphs, degrees, cuts (Definitions 6, 7)
-- statement:
--   Graphs are finite multigraphs $G=(V,E)$: parallel edges and loops are allowed. For $F\subseteq E$ let $\#\mathrm{Comps}(V,F)$ be the number of connected components of the subgraph $(V,F)$.
--
--   **Graphic matroid (Definition 6).** The graphic matroid $M(G)$ has ground set $E$, and $F\subseteq E$ is independent iff $(V,F)$ contains no cycle; equivalently, iff $|F|$ equals the rank
--
--   $$r_{M(G)}(F)=|V|-\#\mathrm{Comps}(V,F).$$
--
--   A matroid is **graphic** if it is isomorphic to $M(G)$ for some graph $G$.
--
--   **Cographic matroid (Definition 7).** $M^*(G)=(M(G))^*$; a matroid is **cographic** if it is isomorphic to $M^*(G)$ for some graph $G$, i.e. if its dual is graphic.
--
--   The file also defines the **degree** of a vertex (a loop counts twice), the **cut** $\delta_G(S)=\{\{u,v\}\in E: u\in S,\ v\in V\setminus S\}$ of a vertex set $S$, and the weight $w(F)=\sum_{e\in F}w(e)$ of a set under nonnegative weights.
--
--   **Formalization Note** A multigraph is an endpoint map `ends : β → Sym2 V` on a finite vertex type `V`; the edges are the elements of the matroid's ground set, so "isomorphic to $M(G)$" becomes "equal to $M(G)$ for a graph whose edges are the ground-set elements". Independence is stated through the paper's rank formula, `F.ncard = card V - numComps ends F`, where components are those of the simple graph on `V` joining two distinct vertices when an edge of `F` joins them (loops and parallel edges do not affect connectivity but do count in `|F|`, so a loop or a pair of parallel edges is dependent).
-- source:
--   Karthekeyan Chandrasekaran, Chandra Chekuri, Weihao Zhu, STOC 2027 submission #536 (October 2026), p. 9, Definitions 6 and 7; p. 9 (cuts δ_G(S))

import Mathlib

set_option autoImplicit false

namespace RandDelMatroid.Indep

open scoped NNReal

variable {β : Type}

/-- A finite multigraph on vertex type `V` whose edges are elements of `β`: edge `e` has the
unordered endpoint pair `ends e` (a loop when the pair is diagonal; parallel edges allowed).
`spanningGraph ends F` is the simple graph on `V` in which two distinct vertices are adjacent when
some edge of `F` joins them; it has the same connected components as the subgraph `(V, F)`. -/
def spanningGraph {V : Type} (ends : β → Sym2 V) (F : Set β) : SimpleGraph V :=
  SimpleGraph.fromRel (fun x y => ∃ e ∈ F, ends e = s(x, y))

/-- `#Comps(V, F)`: the number of connected components of the subgraph `(V, F)`. -/
noncomputable def numComps {V : Type} (ends : β → Sym2 V) (F : Set β) : ℕ :=
  Nat.card (spanningGraph ends F).ConnectedComponent

/-- Definition 6 (p. 9). `N` is the graphic matroid `M(G)` of the finite multigraph
`G = (V, N.E)` with endpoint map `ends`: `F ⊆ N.E` is independent iff
`|F| = r_{M(G)}(F) = |V| - #Comps(V, F)`, i.e. iff `(V, F)` contains no cycle. -/
def IsGraphicMatroidOf (N : Matroid β) (V : Type) [Fintype V] (ends : β → Sym2 V) : Prop :=
  N.E.Finite ∧ ∀ F : Set β, F ⊆ N.E → (N.Indep F ↔ F.ncard = Fintype.card V - numComps ends F)

/-- Definition 6 (p. 9). `N` is *graphic*: it is the graphic matroid of some finite multigraph
whose edge set is `N.E` (so isomorphic to `M(G)` for some graph `G`). -/
def IsGraphic (N : Matroid β) : Prop :=
  ∃ (V : Type) (_ : Fintype V) (ends : β → Sym2 V), IsGraphicMatroidOf N V ends

/-- Definition 7 (p. 9). `N` is *cographic*: `N = M*(G)` for some finite multigraph `G`,
i.e. its dual `N*` is graphic. -/
def IsCographic (N : Matroid β) : Prop :=
  IsGraphic N✶

/-- Degree of the vertex `x` in the multigraph `(V, E)` (a loop at `x` counts twice). -/
noncomputable def degree {V : Type} (ends : β → Sym2 V) (E : Set β) (x : V) : ℕ :=
  {e | e ∈ E ∧ x ∈ ends e}.ncard + {e | e ∈ E ∧ ends e = s(x, x)}.ncard

/-- The cut `δ_G(S)` of the multigraph `(V, E)`: the edges of `E` with one endpoint in `S` and the
other in `V \ S` (loops never lie in a cut). -/
def cut {V : Type} (ends : β → Sym2 V) (E : Set β) (S : Set V) : Set β :=
  {e | e ∈ E ∧ ∃ a ∈ S, ∃ b ∉ S, ends e = s(a, b)}

/-- The weight `w(F) = ∑_{e ∈ F} w(e)` of a finite set of elements under nonnegative weights. -/
noncomputable def setWeight {γ : Type} (w : γ → ℝ≥0) (F : Set γ) : ℝ :=
  ∑ᶠ e ∈ F, (w e : ℝ)

end RandDelMatroid.Indep


