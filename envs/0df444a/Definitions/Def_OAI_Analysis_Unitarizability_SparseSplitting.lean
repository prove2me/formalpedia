-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
-- name    : OAI_Analysis_Unitarizability_SparseSplitting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:52:21.381267+00:00
-- url     : https://prove2.me/theorems/a7de46c8-645f-4ef3-a225-b357d14282d0
-- title:
--   Indicator vectors in $\ell^2(G)$ and labelled rectangle edge sets
-- statement:
--   Throughout, $\ell^2(G)$ denotes the complex Hilbert space of square-summable functions $\xi:G\to\mathbb{C}$ on a type $G$, with $\|\xi\|^2=\sum_{x\in G}|\xi(x)|^2$, and $\delta_x$ is the point mass at $x$.
--
--   1. **Scalar $\ell^2$ space.** The space $\ell^2(G)$ itself, introduced as an abbreviation.
--   2. **Indicator vectors.** For a finite set $U\subseteq G$,
--   $$\mathbf 1_U=\sum_{x\in U}\delta_x\in\ell^2(G),\qquad \mathbf 1_U(x)=\begin{cases}1,&x\in U,\\ 0,&x\notin U.\end{cases}$$
--   The evaluation formula is recorded as a lemma.
--   3. **Rectangle edges.** Let $G$ be a group, $I$ a finite set of labels and $s:I\to G$. For finite sets $U,V\subseteq G$,
--   $$R_s(U,V)=\{(x,i)\in U\times I:\ xs_i\in V\},$$
--   the labelled edges $x\to xs_i$ that start in $U$ and end in $V$. Every pair $(x,i)$ counts separately, even when different labels give the same product $xs_i$.
--
--   These objects convert an operator-norm bound into a combinatorial density bound. For the convolution operator $(A\xi)(x)=\sum_{i\in I}\xi(xs_i)$ one has $\langle\mathbf 1_U,A\mathbf 1_V\rangle=|R_s(U,V)|$, so $\|A\|\le q$ gives $|R_s(U,V)|\le q\sqrt{|U|\,|V|}$. Applied to the endpoint sets of an arbitrary finite edge family, this yields the Hall density condition that produces sparse endpoint assignments (sparse masks) from a norm bound on a convolution operator.
--
--   **Formalization Note** `ScalarL2 G` abbreviates `lp (fun _ : G => ℂ) 2`; `indicatorL2 U` is the finite sum of `lp.single 2 x 1` over `x ∈ U`, with evaluation lemma `indicatorL2_apply`. `rectangleEdges s U V` is a `Finset (G × I)` obtained by filtering `U ×ˢ univ`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SparseSplitting.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SparseSplitting.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment

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


