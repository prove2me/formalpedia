-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection
-- name    : OAI_Analysis_Unitarizability_InvariantProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:11:49.232978+00:00
-- url     : https://prove2.me/theorems/d2797c68-c17c-432e-9ba0-9a56fc8655d2
-- title:
--   Conjugating a representation by a bounded invertible operator
-- statement:
--   Let $G$ be a group, let $H$ be a complex Hilbert space, and let $\pi:G\to B(H)$ be a group homomorphism into the bounded linear operators on $H$, so that each $\pi(g)$ is invertible with inverse $\pi(g^{-1})$; the file records the identity $\pi(g)\bigl(\pi(g^{-1})x\bigr)=x$.
--
--   For a bounded linear bijection $S:H\to H$ with bounded inverse, the **conjugated representation** $\pi^S:G\to B(H)$ is
--   $$\pi^S(g)=S\,\pi(g)\,S^{-1},\qquad\text{that is,}\qquad \pi^S(g)x=S\bigl(\pi(g)(S^{-1}x)\bigr)\quad(g\in G,\ x\in H).$$
--   It is again a group homomorphism: $\pi^S(1)=I$ and $\pi^S(gh)=\pi^S(g)\,\pi^S(h)$.
--
--   In the project, $\pi$ is *similar to a unitary representation* when there is such an $S$ for which every $\pi^S(g)$ is an isometry (hence unitary). The conjugated representation is the device behind the fact that a unitarizable representation admits, for every closed $\pi$-invariant subspace $M$, a bounded projection onto $M$ commuting with all $\pi(g)$: the image $S(M)$ is a closed $\pi^S$-invariant subspace, the orthogonal projection $Q$ onto it commutes with the unitary operators $\pi^S(g)$, and $S^{-1}QS$ is the required projection.
--
--   **Formalization Note** $S$ is a continuous linear equivalence of $H$ with itself, and $\pi^S$ is `conjugated π S`, with evaluation lemma `conjugated_apply`; the inverse identity is `rep_inv`. The file works over a complete space $H$, although the two lemmas do not use completeness.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/InvariantProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/InvariantProjection.lean by skeleton subtraction
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

namespace OAI

/-! A unitarizing similarity gives a bounded commuting projection
onto every closed invariant subspace. -/
noncomputable section
namespace Dixmier
namespace InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
@[simp] theorem rep_inv (U : G →* (H →L[ℂ] H)) (g : G) (x : H) : U g (U g⁻¹ x) = x := by
  have h : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  exact congrArg (fun T : H →L[ℂ] H => T x) h

def conjugated (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) : G →* (H →L[ℂ] H) where
  toFun g := S.toContinuousLinearMap.comp ((π g).comp S.symm.toContinuousLinearMap)
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [map_mul, mul_apply_eq_comp]

omit [CompleteSpace H] in
@[simp] theorem conjugated_apply (π : G →* (H →L[ℂ] H)) (S : H ≃L[ℂ] H) (g : G) (x : H) :
    conjugated π S g x = S (π g (S.symm x)) := rfl

end InvariantProjection
end Dixmier

end

end OAI


