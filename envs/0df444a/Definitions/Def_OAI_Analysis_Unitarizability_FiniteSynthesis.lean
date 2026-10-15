-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis
-- name    : OAI_Analysis_Unitarizability_FiniteSynthesis
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:56:27.576384+00:00
-- url     : https://prove2.me/theorems/54bebcb4-0ea9-44ff-95f3-bf421bc62cac
-- title:
--   Synthesis operators of finite subfamilies and uniform subfamily frame bounds
-- statement:
--   Let $I$ be an index set, $K$ a finite set and $v=(v_i)_{i\in I}$ a family of vectors in $\mathbb{C}^K$. For a finite subset $J\subseteq I$, $\mathbb{C}^J$ is the Euclidean coordinate space on $J$ with standard basis $(e_i)_{i\in J}$; inner products are conjugate-linear in the first argument.
--
--   1. **Synthesis operator.** The linear map $\Phi_J:\mathbb{C}^J\to\mathbb{C}^K$,
--   $$\Phi_J=\sum_{i\in J}v_i\,e_i^{*},\qquad \Phi_Jz=\sum_{i\in J}z_i\,v_i .$$
--   Its adjoint is the analysis operator, $(\Phi_J^*x)_i=\langle v_i,x\rangle$ for $x\in\mathbb{C}^K$ and $i\in J$; both formulas are recorded as lemmas.
--   2. **Frame bound for small subfamilies.** For $p\in\mathbb{N}$ and $b\in\mathbb{R}$, the family $v$ satisfies the frame bound $(p,b)$ if
--   $$\|\Phi_J\|\le b\qquad\text{for every finite } J\subseteq I \text{ with } |J|\le p .$$
--   The empty subfamily is included, so the condition forces $b\ge 0$.
--
--   A frame bound says that any at most $p$ of the vectors are controlled like an orthonormal system up to the factor $b$: $\|\sum_{i\in J}z_iv_i\|\le b\|z\|$ and $\sum_{i\in J}|\langle v_i,x\rangle|^2\le b^2\|x\|^2$. In the construction each row and each column of a sparse mask activates few labels, and these subfamily bounds turn into operator-norm bounds for the masked operators.
--
--   **Formalization Note** `FiniteSynthesis.synthesis v J` is the sum over `i : J` of `InnerProductSpace.rankOne ℂ (v i) (EuclideanSpace.basisFun J ℂ i)`, with lemmas `synthesis_apply` and `synthesis_adjoint_apply`; `FrameBound v p b` is a `Prop`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/FiniteSynthesis.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/FiniteSynthesis.lean by skeleton subtraction
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

namespace OAI

/-! Finite synthesis maps and their adjoints, with bounds for all small subfamilies. -/
noncomputable section
namespace Dixmier
namespace FiniteSynthesis
open scoped ComplexConjugate
variable {I K : Type*} [Fintype K]
local instance instDecidableEq_oAI : DecidableEq I := Classical.decEq I

def synthesis (v : I → EuclideanSpace ℂ K) (J : Finset I) :
    EuclideanSpace ℂ J →L[ℂ] EuclideanSpace ℂ K :=
  ∑ i : J, InnerProductSpace.rankOne ℂ (v i) (EuclideanSpace.basisFun J ℂ i)

@[simp] theorem synthesis_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (z : EuclideanSpace ℂ J) : synthesis v J z = ∑ i : J, z i • v i := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

@[simp] theorem synthesis_adjoint_apply (v : I → EuclideanSpace ℂ K) (J : Finset I)
    (x : EuclideanSpace ℂ K) (i : J) : (synthesis v J).adjoint x i = inner ℂ (v i) x := by
  rw [← EuclideanSpace.basisFun_inner, ContinuousLinearMap.adjoint_inner_right]
  have h : synthesis v J (EuclideanSpace.basisFun J ℂ i) = v i := by
    simp [synthesis_apply, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  rw [h]

/-- The synthesis operator bound on subfamily coordinate spaces,
including the empty subfamily. -/
def FrameBound (v : I → EuclideanSpace ℂ K) (p : ℕ) (b : ℝ) : Prop :=
  ∀ J : Finset I, J.card ≤ p → ‖synthesis v J‖ ≤ b

end FiniteSynthesis
end Dixmier

end

end OAI


