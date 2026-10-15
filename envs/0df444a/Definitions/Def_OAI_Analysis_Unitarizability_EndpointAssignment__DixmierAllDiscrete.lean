-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
-- name    : OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:11:40.306248+00:00
-- url     : https://prove2.me/theorems/b9b5949a-3d0d-4f6a-b022-b086a94a33f0
-- title:
--   Endpoint slots for assigning each edge to one of $r$ slots at its two endpoints
-- statement:
--   Let $E$ be a set of edges, $V$ a set of row vertices and $W$ a set of column vertices, with endpoint maps $\mathrm{row}:E\to V$ and $\mathrm{col}:E\to W$, and fix $r\in\mathbb{N}$. Write $[r]=\{0,1,\dots,r-1\}$. Every vertex carries $r$ numbered slots, so the set of all slots is the disjoint union
--   $$\Sigma_r=(V\times[r])\sqcup(W\times[r]).$$
--   No finiteness, countability or injectivity assumptions are made.
--
--   1. **Endpoint slots of an edge.** For $e\in E$, $\mathrm{Slots}(e)=\bigl(\{\mathrm{row}(e)\}\times[r]\bigr)\sqcup\bigl(\{\mathrm{col}(e)\}\times[r]\bigr)\subseteq\Sigma_r$, the $2r$ slots at the two endpoints of $e$; row slots and column slots are always distinct, lying in different summands even when $V=W$.
--   2. **Slot index.** The map $\Sigma_r\to[r]$ sending both $(v,j)$ and $(w,j)$ to $j$.
--   3. **Row-slot test.** The map $\Sigma_r\to\{\mathrm{true},\mathrm{false}\}$ that is $\mathrm{true}$ exactly on $V\times[r]$.
--
--   These are the bookkeeping devices for an infinite Hall-type assignment. If $f:E\to\Sigma_r$ is injective and $f(e)\in\mathrm{Slots}(e)$ for every edge $e$, then $f$ assigns each edge to one of its endpoints, and the module shows that every row vertex receives at most $r$ edges assigned to row slots and every column vertex at most $r$ edges assigned to column slots. For the edges $(x,i)$, $x\to xs_i$, of a labelled family $s:I\to G$ in a group, the module derives from the density condition $|F|\le r\bigl(|\mathrm{rows}(F)|+|\mathrm{cols}(F)|\bigr)$ for all finite edge sets $F$ the existence of a Boolean mask with at most $r$ row ones in every row and at most $r$ column zeros in every column.
--
--   **Formalization Note** The slot type is `(V × Fin r) ⊕ (W × Fin r)`; `endpointSlots row col r e` is the `Finset.disjSum` of `{row e} ×ˢ univ` and `{col e} ×ˢ univ`, and `slotIndex` and `isRowSlot` are defined by cases on the two summands. Decidability is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean by skeleton subtraction
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

namespace OAI

/-! Infinite endpoint assignment from a finite density inequality.
No countability or distinctness assumption on the edge labels is needed. -/
noncomputable section
namespace Dixmier
open Finset
attribute [local instance] Classical.propDecidable

variable {E V W : Type*}

def endpointSlots (row : E → V) (col : E → W) (r : ℕ)
    (e : E) : Finset ((V × Fin r) ⊕ (W × Fin r)) :=
  (({row e} : Finset V) ×ˢ univ).disjSum (({col e} : Finset W) ×ˢ univ)

def slotIndex {r : ℕ} : (V × Fin r) ⊕ (W × Fin r) → Fin r
  | .inl p => p.2
  | .inr p => p.2

def isRowSlot {r : ℕ} : (V × Fin r) ⊕ (W × Fin r) → Bool
  | .inl _ => true
  | .inr _ => false

end Dixmier

end

end OAI


