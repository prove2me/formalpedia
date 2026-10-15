-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix
-- name    : OAI_Analysis_Unitarizability_SignMatrix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T00:57:04.832987+00:00
-- url     : https://prove2.me/theorems/c556eacd-4595-4ef2-949b-f06c781e1459
-- title:
--   Normalized sign matrices, synthesis along injective selections and bilinear test coefficients
-- statement:
--   Let $I$, $J$, $K$ be finite sets: $I$ indexes labels (columns) and $K$ indexes coordinates (rows), and the real Euclidean spaces $\mathbb{R}^K$, $\mathbb{R}^J$ carry their standard inner products. A *sign matrix* is a function $\sigma:K\times I\to\{\mathrm{true},\mathrm{false}\}$, and $\varepsilon(\mathrm{true})=1$, $\varepsilon(\mathrm{false})=-1$.
--
--   1. **Zero extension along an embedding.** For an injective map $e:J\to I$ and $z:J\to\mathbb{R}$, the function $\tilde z:I\to\mathbb{R}$ with $\tilde z(e(j))=z_j$ and $\tilde z(i)=0$ for $i$ outside the image of $e$ (the first identity is recorded as a lemma).
--   2. **Normalized columns.** For $i\in I$, the vector $u^\sigma_i\in\mathbb{R}^K$ with
--   $$(u^\sigma_i)_a=\frac{\varepsilon(\sigma(a,i))}{\sqrt{|K|}},\qquad a\in K .$$
--   3. **Synthesis along a selection.** For an injective $e:J\to I$, the linear map $\Phi^\sigma_e:\mathbb{R}^J\to\mathbb{R}^K$, $\Phi^\sigma_e z=\sum_{j\in J}z_j\,u^\sigma_{e(j)}$ (recorded as a lemma).
--   4. **Test coefficients.** For $w\in\mathbb{R}^K$ and $z\in\mathbb{R}^J$, the array
--   $$c_{e,w,z}(a,i)=\frac{w_a\,\tilde z(i)}{\sqrt{|K|}},\qquad (a,i)\in K\times I .$$
--
--   These definitions linearize a random-matrix estimate: $\langle\Phi^\sigma_e z,w\rangle=\sum_{(a,i)}c_{e,w,z}(a,i)\,\varepsilon(\sigma(a,i))$ is a Rademacher sum over the entries of $\sigma$, and for unit vectors $w,z$ (and $K$ nonempty) its coefficients have squared sum $1/|K|$, so finite sign-tail bounds apply. Selections are injective maps rather than subsets, so labels keep their identities. Combined with nets and a union bound, this yields sign matrices whose columns are unit vectors and all of whose selections of $p$ columns have synthesis norm at most $10$.
--
--   **Formalization Note** The definitions are `SignMatrix.extend`, `SignMatrix.vector`, `SignMatrix.synthesis` and `SignMatrix.testCoefficients`, with selections given as embeddings `J ↪ I`. If `K` is empty then $\sqrt{|K|}=0$, and Lean's convention that division by zero gives zero makes all these vectors zero; the module's unit-norm lemmas assume `Nonempty K`. This real `SignMatrix.synthesis` is distinct from the complex `FiniteSynthesis.synthesis`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/SignMatrix.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/SignMatrix.lean by skeleton subtraction
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

namespace OAI

/-! Normalized sign matrices and their finite-dimensional bilinear
tests. The coordinate selections are injective and retain label identities. -/
noncomputable section
namespace Dixmier
namespace SignMatrix
open Finset
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
local instance instDecidableEq_oAI_2 : DecidableEq K := Classical.decEq K

def extend (e : J ↪ I) (z : J → ℝ) : I → ℝ := Function.extend e z (fun _ => 0)

omit [Fintype I] [Fintype J] in
@[simp] theorem extend_apply (e : J ↪ I) (z : J → ℝ) (j : J) : extend e z (e j) = z j :=
  e.injective.extend_apply z _ j

def vector (σ : K × I → Bool) (i : I) : EuclideanSpace ℝ K :=
  WithLp.toLp 2 (fun a => FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K))

omit [Fintype I] in
@[simp] theorem vector_apply (σ : K × I → Bool) (i : I) (a : K) :
    vector σ i a = FiniteSigns.sign (σ (a,i)) / Real.sqrt (Fintype.card K) := rfl

def synthesis (σ : K × I → Bool) (e : J ↪ I) : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ K :=
  ∑ j : J, InnerProductSpace.rankOne ℝ (vector σ (e j)) (EuclideanSpace.basisFun J ℝ j)

omit [Fintype I] in
@[simp] theorem synthesis_apply (σ : K × I → Bool) (e : J ↪ I) (z : EuclideanSpace ℝ J) :
    synthesis σ e z = ∑ j, z j • vector σ (e j) := by
  simp only [synthesis, _root_.sum_apply, InnerProductSpace.rankOne_apply, EuclideanSpace.basisFun_inner]

def testCoefficients (e : J ↪ I) (w : EuclideanSpace ℝ K) (z : EuclideanSpace ℝ J) : K × I → ℝ :=
  fun ai => w ai.1 * extend e z ai.2 / Real.sqrt (Fintype.card K)

end SignMatrix
end Dixmier

end

end OAI


