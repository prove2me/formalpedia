-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment
-- name    : OAI_Analysis_Unitarizability_EndpointAssignment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:51:59.898586+00:00
-- url     : https://prove2.me/theorems/b84b2113-646a-4571-a145-6391876ce490
-- title:
--   Endpoint slots for assigning edges to $r$ copies of their endpoints
-- statement:
--   Let $E$ be a set of edges, $V$ a set of row vertices and $W$ a set of column vertices, with endpoint maps $\mathrm{row}:E\to V$ and $\mathrm{col}:E\to W$, and fix a capacity $r\in\mathbb{N}$. Write $[r]=\{0,1,\dots,r-1\}$. Every vertex receives $r$ numbered *slots*, so the set of all slots is the disjoint union
--   $$\Sigma_r=(V\times[r])\ \sqcup\ (W\times[r]).$$
--
--   1. **Endpoint slots of an edge.** For $e\in E$,
--   $$\mathrm{Slots}(e)=\{(\mathrm{row}(e),j):\ j\in[r]\}\ \sqcup\ \{(\mathrm{col}(e),j):\ j\in[r]\},$$
--   the finite set of the $2r$ slots at the two endpoints of $e$ (row slots and column slots are always distinct, being in different summands).
--   2. **Slot index.** The map $\Sigma_r\to[r]$ sending both $(v,j)$ and $(w,j)$ to $j$.
--   3. **Row-slot test.** The map $\Sigma_r\to\{\mathrm{true},\mathrm{false}\}$ that is true exactly on the row part $V\times[r]$.
--
--   These are the bookkeeping devices for an infinite Hall-type assignment. An injective map $f:E\to\Sigma_r$ with $f(e)\in\mathrm{Slots}(e)$ for every edge sends each edge to one of its two endpoints, and injectivity together with the slot index shows that every vertex receives at most $r$ edges. The module obtains such an $f$ from the finite density condition $|F|\le r\,(|\mathrm{row}(F)|+|\mathrm{col}(F)|)$ for all finite $F\subseteq E$, with no countability or distinctness assumption on the edges; the row-slot test then turns $f$ into a sparse Boolean mask.
--
--   **Formalization Note** The slot type is `(V × Fin r) ⊕ (W × Fin r)`, and `endpointSlots row col r e` is the `Finset.disjSum` of `{row e} ×ˢ univ` and `{col e} ×ˢ univ`. `slotIndex` and `isRowSlot` are defined by pattern matching on the two summands; decidability is supplied classically.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/EndpointAssignment.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Dixmier mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Shrink
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Countable.Small
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Definitions.Def_Dixmier
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask

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


