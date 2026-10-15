-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction
-- name    : OAI_Analysis_Unitarizability_SumObstruction
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:13:49.451974+00:00
-- url     : https://prove2.me/theorems/65eb8cba-666b-4884-9ec2-6de7b290ed61
-- title:
--   The spaces $\ell^2(G;\mathbb{C}^{k_j})$, their Hilbert direct sum over $j\in\mathbb{N}$, and its double
-- statement:
--   Let $G$ be a group and let $k:\mathbb{N}\to\mathbb{N}$ be a sequence of fibre dimensions. The file names the three Hilbert spaces on which the direct-sum obstruction is built.
--
--   1. **Stage spaces.** For $j\in\mathbb{N}$,
--   $$\mathcal H_j=\ell^2\bigl(G;\mathbb{C}^{k_j}\bigr)=\Bigl\{\xi:G\to\mathbb{C}^{k_j}\ :\ \sum_{x\in G}\|\xi(x)\|^2<\infty\Bigr\},\qquad\|\xi\|=\Bigl(\sum_{x\in G}\|\xi(x)\|^2\Bigr)^{1/2},$$
--   where $\mathbb{C}^{k_j}$ carries its Euclidean norm.
--   2. **Total space.** $\mathcal H=\bigoplus_{j\in\mathbb{N}}\mathcal H_j$ is the Hilbert ($\ell^2$) direct sum of the stages: sequences $(\xi_j)_{j\in\mathbb{N}}$ with $\xi_j\in\mathcal H_j$ and $\sum_j\|\xi_j\|^2<\infty$.
--   3. **Carrier.** $\mathcal H\oplus_2\mathcal H$ is the Hilbert double of the total space: pairs $(\xi,\eta)$ of elements of $\mathcal H$ with norm $\bigl(\|\xi\|^2+\|\eta\|^2\bigr)^{1/2}$.
--
--   Each stage carries the fibre-valued left regular representation $(\lambda(g)\xi)(x)=\xi(g^{-1}x)$, and the total space carries the direct sum of these unitary representations. On the carrier, the direct-sum obstruction theorem of the project produces, from stage operators satisfying uniform local bounds and an energy growth condition relative to the dimensions $k_j$, a representation $\pi$ of $G$ with $\|\pi(g)\|\le1+\kappa$ that is not similar to a unitary representation: it is the upper-triangular representation built from this direct sum and from the direct sum of the stage coboundaries $g\mapsto T_j-\lambda(g)T_j\lambda(g^{-1})$, which are uniformly bounded even though the stage operators $T_j$ need not be.
--
--   **Formalization Note** These are abbreviations: `Stage G k j` is `KernelObstruction.Space G (Fin (k j))`, an `lp` space of functions from $G$ to `EuclideanSpace ℂ (Fin (k j))` with exponent 2; `Total G k` is `HilbertSum.Space (Stage G k)`, the `lp` space with exponent 2 over the index set $\mathbb{N}$; and `Carrier G k` is `Triangular.Double (Total G k)`. All Hilbert-space structure is inherited from these constructions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SumObstruction.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SumObstruction.lean by skeleton subtraction
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

namespace OAI

/-! The operator-theoretic direct-sum obstruction, constructed from stage operators
without any uniform bound on their norms. -/
noncomputable section
namespace Dixmier
namespace DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

abbrev Stage (G : Type*) (k : ℕ → ℕ) (j : ℕ) : Type _ := KernelObstruction.Space G (Fin (k j))
abbrev Total (G : Type*) (k : ℕ → ℕ) : Type _ := HilbertSum.Space (Stage G k)
abbrev Carrier (G : Type*) (k : ℕ → ℕ) := Triangular.Double (Total G k)

end DirectSumObstruction
end Dixmier

end

end OAI


