-- Prove2me | Definitions.Def_OAI_Combinatorics_CliqueFree_WeightedGraph
-- name    : OAI_Combinatorics_CliqueFree_WeightedGraph
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T20:41:29.749625+00:00
-- url     : https://prove2.me/theorems/a219003f-dc17-412d-9472-d1fa0b2d0f33
-- title:
--   Vertex-weighted masses of sets, edges and triangles, and the cross-mass growth bound
-- statement:
--   Let $G$ be a simple graph on a finite vertex set $V$, write $u\sim v$ for adjacency, and let $w:V\to\mathbb{R}$ be a vertex weight (nonnegative or positive in all applications). For sets $A,B\subseteq V$ and vertices $u,v$ the file defines the following quantities.
--
--   1. **Mass** of a set: $w(A)=\sum_{v\in A}w(v)$.
--
--   2. **Neighbourhood** $N(v)=\{u\in V:\ v\sim u\}$ (the open neighbourhood), together with the membership rule $u\in N(v)\iff v\sim u$.
--
--   3. **Cross mass**, a sum over ordered pairs in which $A$ and $B$ may overlap:
--
--      $$e_w(A,B)=\sum_{u\in A}\ \sum_{v\in B,\ u\sim v}w(u)\,w(v).$$
--
--   4. **Edge mass** $E_w(G)=\tfrac12\,e_w(V,V)=\sum_{\{u,v\}\in E(G)}w(u)\,w(v)$.
--
--   5. **Neighbourhood mass** $d_w(u)=w(N(u))$ and **common mass** $c_w(u,v)=w\bigl(N(u)\cap N(v)\bigr)$.
--
--   6. **Local triangle mass** at $u$:
--
--      $$T_w(u)=\sum_{v\in N(u)}w(v)\,c_w(u,v)=\sum_{\substack{v,z\in N(u)\\ v\sim z}}w(v)\,w(z),$$
--
--      which is twice the weighted edge mass of the subgraph induced on $N(u)$.
--
--   7. **Triangle mass** $T_w(G)=\tfrac16\sum_{u\in V}w(u)\,T_w(u)$, which equals $\sum w(a)w(b)w(c)$ over all unordered triangles $\{a,b,c\}$ of $G$.
--
--   8. **Growth function.** For $x,s\in\mathbb{R}$,
--
--      $$g_x(s)=s\,\bigl(x+\max\{0,\log(1/s)\}\bigr),$$
--
--      so $g_x(s)=s\,(x+\log(1/s))$ for $0<s\le 1$, $g_x(s)=s\,x$ for $s\ge 1$, and $g_x(0)=0$; only $s\ge 0$ is intended.
--
--   9. **Cross-mass bound with constant $C\in\mathbb{R}$.** The property that for every real $x\ge 1$ and all sets $A,B\subseteq V$ (not necessarily disjoint),
--
--      $$w(A)\le e^{x}\ \text{ and }\ w(B)\le e^{x}\quad\Longrightarrow\quad e_w(A,B)\le C\,g_x\bigl(w(A)\bigr).$$
--
--   These are the basic quantities of the weighted approach to independent sets in clique-free graphs. The cross-mass bound says that two sets of mass at most $e^x$ span little weighted edge mass between them, with the size of the first set entering only through $g_x$. In the surrounding development it is established, with $C=16(k+2)^2$, for the maximiser of a variational potential on a graph without cliques of size $k+2$, and conversely it is the hypothesis under which the weighted triangle mass is bounded by a constant multiple of the weighted edge mass.
--
--   **Formalization Note** The Lean names are `mass`, `neighbors` (a `Finset` obtained by filtering all vertices with classical decidability, with the simp lemma `mem_neighbors`), `crossMass`, `edgeMass`, `neighborMass`, `commonMass`, `triangleAt`, `triangleMass`, `growth` and the `Prop` `CrossBound G w C`. The weight is an arbitrary real function. At $s=0$ Lean evaluates `Real.log (1/0) = Real.log 0 = 0`, which gives $g_x(0)=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/CliqueFree/WeightedGraph.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/CliqueFree/WeightedGraph.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the CliqueFreeLog mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_CliqueFreeLog
import Definitions.Def_OAI_Combinatorics_CliqueFree_Numerical

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

attribute [local instance] Classical.propDecidable

namespace CliqueFreeIndependence.WeightedGraph

universe u v

variable {V : Type u} [Fintype V]

def mass (w : V → ℝ) (A : Finset V) : ℝ := ∑ v ∈ A, w v

noncomputable def neighbors (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact univ.filter (G.Adj v)

@[simp] lemma mem_neighbors (G : SimpleGraph V) (u v : V) :
    v ∈ neighbors G u ↔ G.Adj u v := by
  classical
  simp [neighbors]

noncomputable def crossMass (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) : ℝ := by
  classical
  exact ∑ u ∈ A, ∑ v ∈ B, if G.Adj u v then w u * w v else 0

/-- Unordered edge mass, written as half the directed edge mass. -/
noncomputable def edgeMass (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  crossMass G w univ univ / 2

noncomputable def neighborMass (G : SimpleGraph V) (w : V → ℝ) (u : V) : ℝ :=
  mass w (neighbors G u)

noncomputable def commonMass (G : SimpleGraph V) (w : V → ℝ) (u v : V) : ℝ := by
  classical
  exact mass w (neighbors G u ∩ neighbors G v)

/-- Twice the triangle mass in the weighted neighborhood of u. -/
noncomputable def triangleAt (G : SimpleGraph V) (w : V → ℝ) (u : V) : ℝ :=
  ∑ v ∈ neighbors G u, w v * commonMass G w u v

/-- Unordered triangle mass, written as one sixth of the ordered triangle mass. -/
noncomputable def triangleMass (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  (∑ u, w u * triangleAt G w u) / 6

/-- The growth function `g_x`, including its zero convention. Only nonnegative `s` are used. -/
noncomputable def growth (x s : ℝ) : ℝ := s * (x + max 0 (Real.log (1 / s)))

/-- The full cross-mass property; sets may overlap. -/
def CrossBound (G : SimpleGraph V) (w : V → ℝ) (C : ℝ) : Prop :=
  ∀ (x : ℝ), 1 ≤ x → ∀ (A B : Finset V),
    mass w A ≤ Real.exp x → mass w B ≤ Real.exp x →
      crossMass G w A B ≤ C * growth x (mass w A)

end CliqueFreeIndependence.WeightedGraph

end

end OAI


