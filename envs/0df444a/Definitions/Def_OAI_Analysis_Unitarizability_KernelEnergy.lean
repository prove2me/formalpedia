-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy
-- name    : OAI_Analysis_Unitarizability_KernelEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:54:55.979014+00:00
-- url     : https://prove2.me/theorems/4f062341-b8e0-42d6-9a09-41d185d4845e
-- title:
--   Rank-one coefficient matrices and collision kernels of a labelled vector family
-- statement:
--   Let $K$ be a finite set and $\mathbb{C}^K$ the Euclidean space with inner product $\langle u,w\rangle=\sum_a\overline{u_a}\,w_a$. A matrix on $\mathbb{C}^K$ is represented by its vector of entries in $\mathbb{C}^{K\times K}$; the Euclidean norm of that vector is the unnormalized Hilbert–Schmidt (Frobenius) norm $\|M\|_{HS}=\bigl(\sum_{a,b}|M_{ab}|^2\bigr)^{1/2}$.
--
--   1. **Rank-one coefficients.** For $v\in\mathbb{C}^K$, the entry vector of the rank-one matrix $vv^*$,
--   $$(vv^*)_{ab}=v_a\,\overline{v_b},\qquad a,b\in K .$$
--   2. **Collision kernel.** Let $I$ be a finite set of labels, $v:I\to\mathbb{C}^K$ a family of vectors and $s:I\to G$ a labelling by elements of a type $G$. For $g\in G$,
--   $$\kappa_{v,s}(g)=\sum_{i\in I:\ s_i=g}v_iv_i^*\ \in\mathbb{C}^{K\times K},$$
--   the sum of the rank-one matrices of all labels whose value is $g$ (zero if there is none).
--
--   For the translation-invariant operator $(A\xi)(x)=\sum_{i}\langle v_i,\xi(xs_i)\rangle v_i$ on $\ell^2(G;\mathbb{C}^K)$, the matrix $\kappa_{v,s}(g)$ is the block of $A$ in position $(1,g)$, i.e. its convolution kernel. Since Hilbert–Schmidt inner products of positive rank-one matrices are nonnegative, $\langle vv^*,ww^*\rangle_{HS}=|\langle v,w\rangle|^2$, the module shows that for unit vectors $v_i$ the total kernel energy satisfies $\sum_g\|\kappa_{v,s}(g)\|_{HS}^2\ge|I|$, even when many labels collide. This lower bound feeds the kernel-energy obstruction.
--
--   **Formalization Note** Entry vectors live in `EuclideanSpace ℂ (K × K)` and are built with `WithLp.toLp 2`. `rankOneCoefficients_apply` is the entry formula, and `kernelCoefficients v s g` sums over `Finset.univ` filtered by `s i = g`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/KernelEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/KernelEnergy.lean by skeleton subtraction
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

namespace OAI

/-! Positive rank-one kernel energy. Matrices are represented by their entries
with the unnormalized Hilbert–Schmidt (Euclidean coefficient) norm. -/
noncomputable section
namespace Dixmier
attribute [local instance] Classical.propDecidable
open Finset
open scoped ComplexConjugate
variable {K I G : Type*} [Fintype K] [Fintype I]

def rankOneCoefficients (v : EuclideanSpace ℂ K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun p => v p.1 * conj (v p.2))

omit [Fintype K] in
@[simp] theorem rankOneCoefficients_apply (v : EuclideanSpace ℂ K) (a b : K) :
    rankOneCoefficients v (a, b) = v a * conj (v b) := rfl

/-- Collision blocks are sums of the rank-one matrices with that label value. -/
def kernelCoefficients (v : I → EuclideanSpace ℂ K) (s : I → G) (g : G) :
    EuclideanSpace ℂ (K × K) :=
  ∑ i ∈ (Finset.univ.filter fun i => s i = g), rankOneCoefficients (v i)

end Dixmier

end

end OAI


