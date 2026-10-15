-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames
-- name    : OAI_Analysis_Unitarizability_ComplexFrames
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:59:40.514978+00:00
-- url     : https://prove2.me/theorems/7454e899-0c15-4837-958e-39a104ccacaa
-- title:
--   Complexification, real parts and imaginary parts of Euclidean coordinate vectors
-- statement:
--   Let $K$ be a finite set, and let $\mathbb{R}^K$ and $\mathbb{C}^K$ be the real and complex Euclidean coordinate spaces.
--
--   1. **Complexification.** $\iota:\mathbb{R}^K\to\mathbb{C}^K$, $(\iota v)_a=v_a$, viewing each real coordinate as a complex number.
--   2. **Real part.** $\operatorname{Re}:\mathbb{C}^K\to\mathbb{R}^K$, $(\operatorname{Re}z)_a=\operatorname{Re}(z_a)$.
--   3. **Imaginary part.** $\operatorname{Im}:\mathbb{C}^K\to\mathbb{R}^K$, $(\operatorname{Im}z)_a=\operatorname{Im}(z_a)$.
--
--   The module shows $\|\iota v\|=\|v\|$ and
--   $$\|z\|^2=\|\operatorname{Re}z\|^2+\|\operatorname{Im}z\|^2 ,$$
--   and that the synthesis operator of a complexified real family acts separately on the real and imaginary parts of the coefficients. Consequently a real synthesis bound $\|\sum_{i\in J}z_iv_i\|\le b\|z\|$ for real coefficients transfers to the complexified family $(\iota v_i)$ with the same constant $b$. This is how the real random sign frames become complex frames for the fibres $\mathbb{C}^{k}$ used in the construction.
--
--   **Formalization Note** `ComplexFrames.ofReal`, `ComplexFrames.realPart` and `ComplexFrames.imagPart` are plain coordinatewise functions between `EuclideanSpace ℝ K` and `EuclideanSpace ℂ K`, built with `WithLp.toLp 2`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/ComplexFrames.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/ComplexFrames.lean by skeleton subtraction
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

namespace OAI

/-! Complexification preserves real synthesis norm bounds.
The real and imaginary coefficient vectors are handled separately. -/
noncomputable section
namespace Dixmier
namespace ComplexFrames
open Finset
variable {I K : Type*} [Fintype K]
def ofReal (v : EuclideanSpace ℝ K) : EuclideanSpace ℂ K := WithLp.toLp 2 (fun a => (v a : ℂ))
def realPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).re)
def imagPart (z : EuclideanSpace ℂ K) : EuclideanSpace ℝ K := WithLp.toLp 2 (fun a => (z a).im)

end ComplexFrames
end Dixmier

end

end OAI


