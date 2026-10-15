-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds
-- name    : OAI_Analysis_Unitarizability_LocalBounds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:08:36.583977+00:00
-- url     : https://prove2.me/theorems/193179fb-e1f1-426a-8c66-f738c743cc9e
-- title:
--   Row- and column-localized masks of a Boolean edge orientation
-- statement:
--   Notation follows the masked operators on $\mathcal H=\ell^2(G;\mathbb{C}^K)$: $G$ is a group, $I$ a finite set of labels with products $s:I\to G$, $a:G\times I\to\{\mathrm{true},\mathrm{false}\}$ a Boolean mask, and $[b]\in\mathbb{C}$ the scalar of a bit $b$ ($1$ if true, $0$ if false). The file defines two localized coefficient arrays.
--
--   1. **Row mask at $x_0$.** For $x_0\in G$,
--   $$c^{\mathrm{row}}_{x_0}(x,i)=\begin{cases}[a(x,i)],& x=x_0,\\ 0,& x\ne x_0.\end{cases}$$
--   2. **Column mask at $y_0$.** For $y_0\in G$,
--   $$c^{\mathrm{col}}_{y_0}(x,i)=\begin{cases}1-[a(x,i)],& xs_i=y_0,\\ 0,&\text{otherwise}.\end{cases}$$
--
--   It also records that both arrays, and $1-[a(x,i)]$ itself, have modulus at most $1$ everywhere, so they define masked operators. The row mask keeps the row-assigned edges leaving the single row $x_0$, and the column mask keeps the column-assigned edges arriving at the single column $y_0$. The module uses them for localization: the row $E_{x_0}T$ of the oriented operator $T$ equals the row at $x_0$ of the masked operator with coefficients $c^{\mathrm{row}}_{x_0}$, and the column $(A-T)\iota_{y_0}$ of the complementary part equals the column at $y_0$ of the masked operator with coefficients $c^{\mathrm{col}}_{y_0}$. For a sparse mask of capacity $r$ these localized masks are supported on at most $r$ labels, so a frame bound $b$ gives $\|E_{x_0}T\|\le b^2$ and $\|(A-T)\iota_{y_0}\|\le b^2$, the row and column hypotheses of the kernel obstruction.
--
--   **Formalization Note** `Masked.rowMask a x₀` and `Masked.columnMask a s y₀` are coefficient arrays `G → I → ℂ`; `rowMask_norm`, `complement_norm` and `columnMask_norm` are the modulus bounds.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/LocalBounds.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/LocalBounds.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting
import Definitions.Def_OAI_Analysis_Unitarizability_Regular
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
import Definitions.Def_OAI_Analysis_Unitarizability_Frames
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum
import Definitions.Def_OAI_Analysis_Unitarizability_Masked
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra

namespace OAI

/-! Individual block row and column bounds from the endpoint assignment. -/
noncomputable section
namespace Dixmier
namespace Masked
open Finset
variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]
local instance instDecidableEq_oAI_5 : DecidableEq G := Classical.decEq G
def rowMask (a : G → I → Bool) (x₀ x : G) (i : I) : ℂ :=
  if x = x₀ then boolComplex (a x i) else 0

def columnMask (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) : ℂ :=
  if x * s i = y₀ then 1 - boolComplex (a x i) else 0

omit [Group G] [Fintype I] in
theorem rowMask_norm (a : G → I → Bool) (x₀ x : G) (i : I) : ‖rowMask a x₀ x i‖ ≤ 1 := by
  unfold rowMask
  split_ifs
  · exact bool_mask_norm a x i
  · simp

omit [Group G] [Fintype I] in
theorem complement_norm (a : G → I → Bool) (x : G) (i : I) : ‖1 - boolComplex (a x i)‖ ≤ 1 := by
  cases a x i <;> simp [boolComplex]

omit [Fintype I] in
theorem columnMask_norm (a : G → I → Bool) (s : I → G) (y₀ x : G) (i : I) :
    ‖columnMask a s y₀ x i‖ ≤ 1 := by
  unfold columnMask
  split_ifs
  · exact complement_norm a x i
  · simp

end Masked
end Dixmier

end

end OAI


