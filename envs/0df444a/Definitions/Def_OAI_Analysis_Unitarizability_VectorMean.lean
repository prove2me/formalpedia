-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_VectorMean
-- name    : OAI_Analysis_Unitarizability_VectorMean
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:53:24.715637+00:00
-- url     : https://prove2.me/theorems/8eaf501c-c373-4d87-b6e7-7f36d2e6461c
-- title:
--   Vector means: bounded functionals on bounded functions induced by $\ell^2$ vectors
-- statement:
--   Let $G$ be a group carrying a topology (in the application the discrete one), let $\ell^2(G)$ be the complex Hilbert space of square-summable functions on $G$, and let $C_b(G)$ be the space of bounded continuous functions $b:G\to\mathbb{C}$ with the supremum norm $\|b\|_\infty$ (for a discrete group, simply all bounded functions).
--
--   For $\xi\in\ell^2(G)$ the **vector mean** of $\xi$ is the functional
--   $$m_\xi(b)=\sum_{x\in G}|\xi(x)|^2\,b(x^{-1}),\qquad b\in C_b(G).$$
--   The file shows that $x\mapsto|\xi(x)|^2$ is summable, that the series defining $m_\xi(b)$ converges absolutely, and that
--   $$|m_\xi(b)|\le\|\xi\|^2\,\|b\|_\infty .$$
--   It then packages $m_\xi$ as a complex-linear map and, by this bound, as a continuous linear functional on $C_b(G)$ of norm at most $\|\xi\|^2$.
--
--   For a unit vector $\xi$, $m_\xi(b)$ is the average of $b(x^{-1})$ against the probability weights $|\xi(x)|^2$, hence a positive normalized mean. Left translation of $b$ corresponds to right translation of $\xi$, so a unit vector that is almost invariant under the right regular representation produces an almost invariant mean. This is how the development proves that if every finite sum of right regular operators $\sum_{t\in S}R_t$ with $1\in S$ has full norm $|S|$, then $G$ is amenable; contrapositively, a non-amenable group has a contracting average, the starting point of the construction.
--
--   **Formalization Note** `vectorMeanValue ξ b` is the `tsum` above; `summable_l2_sq`, `vectorMean_summable` and `vectorMean_norm_le` give summability and the norm bound; `vectorMeanLinear` is the linear map and `vectorMean` is `LinearMap.mkContinuous` with constant `‖ξ‖ ^ 2`, with evaluation lemma `vectorMean_apply`. No discreteness of the topology is assumed in this file.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/VectorMean.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/VectorMean.lean by skeleton subtraction
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

namespace OAI

/-! Vector means and their translation error bounds. -/
noncomputable section
namespace Dixmier
open scoped BoundedContinuousFunction
variable {G : Type*} [Group G] [TopologicalSpace G]

omit [Group G] [TopologicalSpace G] in
theorem summable_l2_sq (ξ : ScalarL2 G) : Summable (fun x => ‖ξ x‖ ^ 2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num)

def vectorMeanValue (ξ : ScalarL2 G) (b : G →ᵇ ℂ) : ℂ :=
  ∑' x, (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)

theorem vectorMean_summable (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    Summable (fun x => (‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹) : G → ℂ) := by
  apply Summable.of_norm_bounded ((summable_l2_sq ξ).mul_right ‖b‖)
  intro x
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
  exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)

theorem vectorMean_norm_le (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    ‖vectorMeanValue ξ b‖ ≤ ‖ξ‖ ^ 2 * ‖b‖ := by
  have hb : ∀ x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ ≤ ‖ξ x‖ ^ 2 * ‖b‖ := by
    intro x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ξ x‖)]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (sq_nonneg _)
  calc
    ‖vectorMeanValue ξ b‖ ≤ ∑' x, ‖(‖ξ x‖ ^ 2 : ℝ) * b (x⁻¹)‖ :=
      norm_tsum_le_tsum_norm (vectorMean_summable ξ b).norm
    _ ≤ ∑' x, ‖ξ x‖ ^ 2 * ‖b‖ :=
      Summable.tsum_le_tsum hb (vectorMean_summable ξ b).norm ((summable_l2_sq ξ).mul_right ‖b‖)
    _ = ‖ξ‖ ^ 2 * ‖b‖ := by rw [tsum_mul_right, ← l2_norm_sq]

def vectorMeanLinear (ξ : ScalarL2 G) : (G →ᵇ ℂ) →ₗ[ℂ] ℂ where
  toFun := vectorMeanValue ξ
  map_add' b c := by
    simp only [vectorMeanValue, BoundedContinuousFunction.add_apply, mul_add]
    exact (vectorMean_summable ξ b).tsum_add (vectorMean_summable ξ c)
  map_smul' z b := by
    simp only [vectorMeanValue, BoundedContinuousFunction.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp_rw [← mul_assoc, mul_comm _ z, mul_assoc]
    exact tsum_mul_left

def vectorMean (ξ : ScalarL2 G) : (G →ᵇ ℂ) →L[ℂ] ℂ :=
  (vectorMeanLinear ξ).mkContinuous (‖ξ‖ ^ 2) (vectorMean_norm_le ξ)

@[simp] theorem vectorMean_apply (ξ : ScalarL2 G) (b : G →ᵇ ℂ) :
    vectorMean ξ b = vectorMeanValue ξ b := rfl

end Dixmier

end

end OAI


