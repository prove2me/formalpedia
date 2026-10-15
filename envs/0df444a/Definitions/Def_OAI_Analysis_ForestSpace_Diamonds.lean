-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Diamonds
-- name    : OAI_Analysis_ForestSpace_Diamonds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:09:04.815521+00:00
-- url     : https://prove2.me/theorems/5711153a-f3a3-404c-82ab-9edf67ad7ba4
-- title:
--   Distance potential on refined networks and inclusion of old vertices into iterated refinements
-- statement:
--   A *network* $A$ consists of a vertex set $V_A$, an edge index set $E_A$ and, for each $e\in E_A$, two distinct endpoints $\ell(e),r(e)\in V_A$. Its graph $G_A$ is the simple graph in which $u$ and $v$ are adjacent iff some edge has endpoints $u$ and $v$ (in either order), and $d_A$ is the shortest-path distance of $G_A$. The *refinement* $A'$ replaces every edge by countably many internally disjoint paths of length two: $V_{A'}=V_A\sqcup(E_A\times\mathbb{N})$, and each new vertex $(e,j)$ is joined by one edge to $\ell(e)$ and by one edge to $r(e)$. The $n$-fold refinement is $A^{(n)}$ (with $A^{(0)}=A$ and $A^{(n+1)}=(A')^{(n)}$), and the countably branching diamond $D_k$ is the $k$-fold refinement of the network $D_0$ that has two vertices and one edge. The file defines:
--
--   1. **Refinement potential.** For a vertex $a\in V_A$, the function $\varphi_a:V_{A'}\to\mathbb{R}$ given by
--   $$
--   \varphi_a(u)=2\,d_A(a,u)\quad(u\in V_A),\qquad \varphi_a\bigl((e,j)\bigr)=d_A\bigl(a,\ell(e)\bigr)+d_A\bigl(a,r(e)\bigr)\quad(e\in E_A,\ j\in\mathbb{N}).
--   $$
--   2. **Old vertices in iterated refinements.** The maps $\iota^A_n:V_A\to V_{A^{(n)}}$ defined by $\iota^A_0=\mathrm{id}$ and $\iota^A_{n+1}(u)=\iota^{A'}_n(u)$: a vertex of $A$ is first regarded as an old vertex of $A'$ and then carried through the remaining $n$ refinements of $A'$.
--
--   The file also records the defining equations $\iota^A_0(u)=u$ and $\iota^A_{n+1}(u)=\iota^{A'}_n(u)$, and that $D_0$ is the single-edge network.
--
--   When $G_A$ is connected, $\varphi_a$ changes by at most $1$ along every edge of $A'$, so it bounds lengths of walks in $A'$ from below; this is how one shows that refinement exactly doubles distances between old vertices, and hence that $d_{A^{(n)}}\bigl(\iota^A_n(u),\iota^A_n(v)\bigr)=2^n\,d_A(u,v)$. These metric facts about the diamonds $D_k$ feed the lower bound $\sqrt{1+k/12}$ for the distortion of embeddings of $D_k$.
--
--   **Formalization Note** Graph distance is Mathlib's `SimpleGraph.dist`, a natural number (equal to $0$ when no path exists), cast to $\mathbb{R}$. The edges of $A'$ are indexed by $E_A\times\mathbb{N}\times\{\mathrm{true},\mathrm{false}\}$, oriented from $\ell(e)$ to $(e,j)$ and from $(e,j)$ to $r(e)$. The definitions are `refinePotential` and `old`; `old_zero`, `old_succ` and `diamond_zero` are definitional simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Diamonds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Diamonds.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry
import Definitions.Def_OAI_Analysis_ForestSpace_Paired
import Definitions.Def_OAI_Analysis_ForestSpace_Norm
import Definitions.Def_OAI_Analysis_ForestSpace_Completion
import Definitions.Def_OAI_Analysis_ForestSpace_Polar
import Definitions.Def_OAI_Analysis_ForestSpace_Projections
import Definitions.Def_OAI_Analysis_ForestSpace_Renorming
import Definitions.Def_OAI_Analysis_ForestSpace_Coordinates
import Definitions.Def_OAI_Analysis_ForestSpace_Trees
import Definitions.Def_OAI_Analysis_ForestSpace_Reflexivity
import Definitions.Def_OAI_Analysis_ForestSpace_Components
import Definitions.Def_OAI_Analysis_ForestSpace_FullDual

namespace OAI

noncomputable section

open scoped BigOperators
open Finset

namespace ForestSpace

attribute [local instance] Classical.propDecidable

namespace Diamond

namespace Network
variable (A : Network)

end Network

namespace Network

section
variable (A : Network)

noncomputable def refinePotential (a : A.V) : A.refine.V → ℝ
  | Sum.inl u => 2*(A.graph.dist a u : ℝ)
  | Sum.inr ⟨e,_⟩ => (A.graph.dist a (A.left e) : ℝ)+(A.graph.dist a (A.right e) : ℝ)

end

/-- The canonical inclusion of all old vertices through finitely many refinements. -/
def old : (A : Network) → (n : ℕ) → A.V → (A.iterate n).V
  | _,0 => id
  | A,n+1 => fun u => A.refine.old n (Sum.inl u)

@[simp] theorem old_zero (A : Network) (u : A.V) : A.old 0 u = u := rfl
@[simp] theorem old_succ (A : Network) (n : ℕ) (u : A.V) :
    A.old (n+1) u = A.refine.old n (Sum.inl u) := rfl

end Network

@[simp] theorem diamond_zero : diamond 0 = base := rfl

end Diamond

end ForestSpace

end

end OAI


