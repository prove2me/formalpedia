-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_Cocycle
-- name    : OAI_Analysis_Unitarizability_Cocycle
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:02:38.03386+00:00
-- url     : https://prove2.me/theorems/dcb93d3a-6d1e-4398-b0ba-d69951eab706
-- title:
--   Conjugation and coboundaries for a group homomorphism into a ring
-- statement:
--   Let $G$ be a group, $R$ a ring (in the application, the bounded operators on a complex Hilbert space) and $U:G\to R$ a homomorphism into the multiplicative monoid of $R$, i.e. $U(gh)=U(g)U(h)$ and $U(1)=1$; in particular $U(g^{-1})$ is the inverse of $U(g)$.
--
--   1. **Conjugation.** For $g\in G$ and $T\in R$,
--   $$\operatorname{Ad}_U(g)\,T=U(g)\,T\,U(g^{-1}).$$
--   2. **Coboundary.** For $T\in R$, the map $\delta_UT:G\to R$,
--   $$\delta_UT(g)=T-U(g)\,T\,U(g^{-1}).$$
--
--   The file records $\operatorname{Ad}_U(1)T=T$ and $\delta_UT(1)=0$. The coboundary is the basic example of a cocycle: the module proves $\delta_UT(gh)=\delta_UT(g)+\operatorname{Ad}_U(g)\,\delta_UT(h)$, and that $\delta_UT(g)=\delta_UB(g)$ holds exactly when $T-B$ commutes with $U(g)$. In the construction, $U$ is the left translation representation on $\ell^2(G;\mathbb{C}^K)$ and $T$ is an oriented masked operator, whose coboundary is uniformly bounded although $T$ is far from every operator commuting with the translations. A bounded cocycle $D$ for a unitary $U$ yields the upper triangular representation $g\mapsto\begin{pmatrix}U(g)&D(g)U(g)\\0&U(g)\end{pmatrix}$, and similarity of that representation to a unitary one would force $D$ to be the coboundary of a bounded operator.
--
--   **Formalization Note** `conjugate U g T` is `U g * T * U g⁻¹` and `coboundary U T g` is `T - conjugate U g T`, for `U : G →* R` and an arbitrary `Ring R`; `conjugate_one` and `coboundary_one` are simp lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/Cocycle.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/Cocycle.lean by skeleton subtraction
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

namespace OAI

/-! Cocycle algebra in an arbitrary ring, specializing to bounded complex Hilbert-space operators. -/
namespace Dixmier
section Ring
variable {G R : Type*} [Group G] [Ring R]

def conjugate (U : G →* R) (g : G) (T : R) : R := U g * T * U g⁻¹

@[simp] theorem conjugate_one (U : G →* R) (T : R) : conjugate U 1 T = T := by
  simp [conjugate]

def coboundary (U : G →* R) (T : R) (g : G) : R := T - conjugate U g T

@[simp] theorem coboundary_one (U : G →* R) (T : R) : coboundary U T 1 = 0 := by
  simp [coboundary]

end Ring
end Dixmier

end OAI


