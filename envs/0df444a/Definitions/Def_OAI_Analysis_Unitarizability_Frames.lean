-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Frames
-- name    : OAI_Analysis_Unitarizability_Frames
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:00:40.881262+00:00
-- url     : https://prove2.me/theorems/91ab6fbb-0f03-4abf-8d70-2423197dedbd
-- title:
--   Zero extension of real coordinate vectors along an injective selection
-- statement:
--   Let $J$ and $L$ be finite sets and $e:J\to L$ an injective map. For a real vector $z\in\mathbb{R}^J$, its **zero extension** along $e$ is the vector $\mathrm{ext}_e z\in\mathbb{R}^L$ with
--   $$(\mathrm{ext}_e z)_{e(j)}=z_j\quad (j\in J),\qquad (\mathrm{ext}_e z)_l=0\quad\text{for } l\notin e(J).$$
--
--   Zero extension is an isometry, $\|\mathrm{ext}_e z\|=\|z\|$, and it is compatible with synthesis along selections: for a sign matrix $\sigma$ and injective maps $f:J\to L$ and $e:L\to I$, synthesizing $\mathrm{ext}_f z$ along $e$ gives the same vector as synthesizing $z$ along the composite $e\circ f$. Hence a bound on the synthesis operators of all selections of exactly $p$ columns also bounds every smaller selection. This is how the module passes from $p$-element selections to all subfamilies of size at most $p$ and proves the frame lemma: for $n\ge 2$ and $r\ge 1$ there are $n$ unit vectors in $\mathbb{C}^{k}$, $k=\lceil 2r\log(2n)\rceil$, all of whose subfamilies of size at most $\min(2r,n)$ have synthesis norm at most $10$.
--
--   **Formalization Note** `SignMatrix.extendVector e z` is `WithLp.toLp 2 (SignMatrix.extend e z)` for an embedding `e : J ↪ L`; it is the only definition of this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Frames.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Frames.lean by skeleton subtraction
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

namespace OAI

/-! Frame existence with prescribed dimensions and bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J L K : Type*} [Fintype I] [Fintype J] [Fintype L] [Fintype K]
def extendVector (e : J ↪ L) (z : EuclideanSpace ℝ J) : EuclideanSpace ℝ L :=
  WithLp.toLp 2 (extend e z)

end SignMatrix
end Dixmier

end

end OAI


