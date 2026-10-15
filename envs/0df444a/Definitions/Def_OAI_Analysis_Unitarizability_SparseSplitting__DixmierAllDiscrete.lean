-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:12:23.344913+00:00
-- url     : https://prove2.me/theorems/df04a56f-fe55-49bd-9873-3d64980df052
-- title:
--   Indicator vectors in $\ell^2(G)$ and labelled edges between two finite sets
-- statement:
--   Throughout, $\ell^2(G)$ is the complex Hilbert space of square-summable functions $\xi:G\to\mathbb{C}$ on a set $G$, with $\|\xi\|^2=\sum_{x\in G}|\xi(x)|^2$, and $\delta_x$ is the point mass at $x$.
--
--   1. **Scalar $\ell^2$ space.** The space $\ell^2(G)$ itself, introduced as an abbreviation.
--   2. **Indicator vectors.** For a finite set $U\subseteq G$,
--   $$\mathbf 1_U=\sum_{x\in U}\delta_x,\qquad\mathbf 1_U(x)=\begin{cases}1,&x\in U,\\0,&x\notin U,\end{cases}$$
--   the evaluation formula being recorded as a lemma.
--   3. **Rectangle edges.** Let $G$ be a group, $I$ a finite set and $s:I\to G$. For finite sets $U,V\subseteq G$,
--   $$R_s(U,V)=\{(x,i)\in U\times I:\ xs_i\in V\},$$
--   the labelled edges $x\to xs_i$ that start in $U$ and end in $V$; pairs with different labels count separately even when their products coincide.
--
--   These objects turn an operator-norm bound into a combinatorial density bound. For a bounded operator $A$ on $\ell^2(G)$ with $(A\xi)(x)=\sum_{i\in I}\xi(xs_i)$ one has $\langle\mathbf 1_U,A\mathbf 1_V\rangle=|R_s(U,V)|$, and the module proves that $\|A\|\le q$ implies $|R_s(U,V)|\le q\sqrt{|U|\,|V|}$ for all finite $U,V$. It then shows that such rectangle bounds with $0\le q\le r$, $r\in\mathbb{N}$, give the density condition $|F|\le r\bigl(|\mathrm{rows}(F)|+|\mathrm{cols}(F)|\bigr)$ for every finite set $F$ of edges, which is the input of the sparse endpoint assignment.
--
--   **Formalization Note** `ScalarL2 G` abbreviates `lp (fun _ : G => ℂ) 2`; `indicatorL2 U` is the finite sum of `lp.single 2 x 1` over `x ∈ U`, with evaluation lemma `indicatorL2_apply`, and `rectangleEdges s U V` is a `Finset (G × I)` obtained by filtering `U ×ˢ univ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SparseSplitting.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SparseSplitting.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete

namespace OAI

/-! Spectral norm bounds imply sparse endpoint assignments.
The input is a bounded convolution operator with its coefficient formula. -/
noncomputable section
namespace Dixmier
open Finset
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {G I : Type*} [Fintype I]

abbrev ScalarL2 (G : Type*) := lp (fun _ : G => ℂ) 2

def indicatorL2 (U : Finset G) : ScalarL2 G := ∑ x ∈ U, lp.single 2 x 1

@[simp] theorem indicatorL2_apply (U : Finset G) (x : G) :
    indicatorL2 U x = if x ∈ U then 1 else 0 := by
  change (∑ i ∈ U, lp.single 2 i (1 : ℂ)) x = _
  rw [lp.coeFn_sum]
  simp [Finset.sum_apply, lp.coeFn_single, Pi.single_apply]

variable [Group G]

def rectangleEdges (s : I → G) (U V : Finset G) : Finset (G × I) :=
  (U ×ˢ univ).filter fun e => e.1 * s e.2 ∈ V

end Dixmier

end

end OAI


