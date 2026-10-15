-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SparseMask
-- name    : OAI_Analysis_Unitarizability_SparseMask
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:51:36.099984+00:00
-- url     : https://prove2.me/theorems/c80afeea-7a9d-4adc-9e5c-29e94a0c7905
-- title:
--   Row ones, column zeros and translation-difference sets of a Boolean edge mask
-- statement:
--   Let $G$ be a group and $I$ a finite set of labels. A family $s=(s_i)_{i\in I}$ in $G$ determines labelled edges: the pair $(x,i)\in G\times I$ is an edge from the *row* vertex $x$ to the *column* vertex $xs_i$. A *mask* is a function $a:G\times I\to\{\mathrm{true},\mathrm{false}\}$ that orients every edge: $a(x,i)=\mathrm{true}$ assigns the edge $(x,i)$ to its row endpoint and $a(x,i)=\mathrm{false}$ to its column endpoint. Labels are kept as elements of $I$ even when several products $s_i$ coincide. The file defines four finite subsets of $I$ and one scalar map.
--
--   1. **Row ones.** For $x\in G$,
--   $$\mathrm{Ones}_a(x)=\{i\in I:\ a(x,i)=\mathrm{true}\},$$
--   the edges leaving row $x$ that are assigned to that row.
--   2. **Column zeros.** For $y\in G$,
--   $$\mathrm{Zeros}_{a,s}(y)=\{i\in I:\ a(ys_i^{-1},i)=\mathrm{false}\},$$
--   the labels of the edges $(ys_i^{-1},i)$ arriving at column $y$ that are assigned to that column.
--   3. **Row difference.** For $g,x\in G$,
--   $$\Delta^{\mathrm{row}}_a(g,x)=\{i\in I:\ a(x,i)\ne a(g^{-1}x,i)\},$$
--   the labels at row $x$ where the mask and its left translate by $g$ disagree.
--   4. **Column difference.** For $g,y\in G$,
--   $$\Delta^{\mathrm{col}}_{a,s}(g,y)=\{i\in I:\ a(ys_i^{-1},i)\ne a(g^{-1}ys_i^{-1},i)\}.$$
--   5. **Bits as scalars.** $[b]\in\mathbb{C}$ equals $1$ if the bit $b$ is true and $0$ otherwise. The file records that for all bits $b,c$
--   $$\bigl|[b]-[c]\bigr|\le 1 .$$
--
--   A mask is *sparse with capacity $r$* when $|\mathrm{Ones}_a(x)|\le r$ for every row $x$ and $|\mathrm{Zeros}_{a,s}(y)|\le r$ for every column $y$. The difference sets locate where the operator built from the mask fails to commute with left translation by $g$. A disagreement at row $x$ forces $i$ to be a one at $x$ or at $g^{-1}x$ (and similarly for zeros at columns), so sparsity bounds both difference sets by $\min(2r,|I|)$, uniformly in $g$; this is the combinatorial input for the uniformly bounded coboundaries in the construction of a bounded nonunitarizable representation of a non-amenable group.
--
--   **Formalization Note** The mask is a curried function `a : G → I → Bool`. The four sets `rowOnes`, `columnZeros`, `rowDifference` and `columnDifference` are `Finset`s obtained by filtering `Finset.univ`, `boolComplex` is the bit-to-scalar map, and `difference_mask_norm` is the displayed bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SparseMask.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SparseMask.lean by skeleton subtraction
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

namespace OAI

/-! Finite support estimates for mask differences.
The label type is retained even when the products s_i collide. -/
namespace Dixmier

open Finset
variable {G I : Type*} [Group G] [Fintype I] [DecidableEq I]

noncomputable def rowOnes (a : G → I → Bool) (x : G) : Finset I :=
  univ.filter fun i => a x i = true

noncomputable def columnZeros (a : G → I → Bool) (s : I → G) (y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i = false

noncomputable def rowDifference (a : G → I → Bool) (g x : G) : Finset I :=
  univ.filter fun i => a x i ≠ a (g⁻¹ * x) i

noncomputable def columnDifference (a : G → I → Bool) (s : I → G)
    (g y : G) : Finset I :=
  univ.filter fun i => a (y * (s i)⁻¹) i ≠ a (g⁻¹ * (y * (s i)⁻¹)) i

def boolComplex (b : Bool) : ℂ := if b then 1 else 0

/-- The scalar difference mask has absolute value at most one. -/
theorem difference_mask_norm (b c : Bool) : ‖boolComplex b - boolComplex c‖ ≤ 1 := by
  cases b <;> cases c <;> simp [boolComplex]

end Dixmier

end OAI


