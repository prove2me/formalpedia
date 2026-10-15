-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport
-- name    : OAI_Analysis_Unitarizability_UniverseTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:15:52.394104+00:00
-- url     : https://prove2.me/theorems/79767ca2-bdf6-4e3a-9125-758a0d6cf99a
-- title:
--   Transporting bounded functions along a group isomorphism
-- statement:
--   Let $G$ and $Q$ be groups, each carrying the discrete topology, and let $e:G\to Q$ be a group isomorphism. Write $\ell^\infty(G)$ for the space of bounded functions $G\to\mathbb{C}$ (all of which are continuous, since $G$ is discrete), and similarly $\ell^\infty(Q)$. The **mean pullback** along $e$ is the $\mathbb{C}$-linear map
--   $$T_e:\ell^\infty(G)\to\ell^\infty(Q),\qquad (T_ef)(q)=f\bigl(e^{-1}(q)\bigr)\quad(q\in Q),$$
--   that is, $T_ef=f\circ e^{-1}$.
--
--   The name refers to its use: if $m$ is a positive, normalized, left-invariant mean on $\ell^\infty(Q)$, then $m\circ T_e$ is such a mean on $\ell^\infty(G)$, because $T_e$ sends the constant function $1$ to $1$, preserves nonnegativity, and intertwines left translations, $T_e(\lambda_gf)=\lambda_{e(g)}(T_ef)$ where $(\lambda_gf)(x)=f(g^{-1}x)$. Thus amenability is invariant under group isomorphisms, which is what allows the main theorem to be moved between a countable group and an isomorphic copy of it in another universe.
--
--   **Formalization Note** Bounded functions are bounded continuous functions `G →ᵇ ℂ` for the discrete topology, and the map is `meanPullback e`, defined by composing with `e.symm`; it is declared only as a linear map, and `meanPullback_apply` is its evaluation formula. The groups $G$ and $Q$ may live in different universes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/UniverseTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/UniverseTransport.lean by skeleton subtraction
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
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction

namespace OAI

/-! Countability lets a group be represented in any universe.
Transport by group equivalences preserves the positive normalized invariant mean
and the bounded nonunitarizable witness. -/
noncomputable section
namespace Dixmier
universe u v w
open scoped BoundedContinuousFunction
variable {G : Type u} {Q : Type v} [Group G] [Group Q]
variable [TopologicalSpace G] [DiscreteTopology G]
variable [TopologicalSpace Q] [DiscreteTopology Q]

def meanPullback (e : G ≃* Q) : (G →ᵇ ℂ) →ₗ[ℂ] (Q →ᵇ ℂ) where
  toFun f := f.compContinuous ⟨e.symm, continuous_of_discreteTopology⟩
  map_add' f h := by ext q; rfl
  map_smul' z f := by ext q; rfl

omit [DiscreteTopology G] in
@[simp] theorem meanPullback_apply (e : G ≃* Q) (f : G →ᵇ ℂ) (q : Q) :
    meanPullback e f q = f (e.symm q) := rfl

end Dixmier

end

end OAI


