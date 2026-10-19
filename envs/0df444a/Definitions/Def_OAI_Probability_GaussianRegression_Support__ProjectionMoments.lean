-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Support__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:39:04.985784+00:00
-- url     : https://prove2.me/theorems/9484699b-e394-4f17-aa05-65de927f6b17
-- title:
--   Coordinate balls, row operators and net supports
-- statement:
--   Finite-volume enclosures for Gaussian matrix observations.
--
--   1. **Coordinate norm and balls.** For labels $y\in\mathbb R^m$, the coordinate norm is the Euclidean norm, and the coordinate ball of radius $r$ is $\{y:\|y\|\le r\}$.
--   2. **Row operator.** For rows $A_1,\dots,A_m$, the row operator maps $x$ to $(\langle x,A_j\rangle)_j$ as a continuous linear map into Euclidean space.
--   3. **Net support.** For a finite set $s$ of points, the net projection support is the set of observations whose labels are at most twice the projection of some net point:
--   $$
--   \bigcup_{u\in s}\Bigl\{(A,y):\ \|y\|\le2\,\bigl\|(\langle u,A_j\rangle)_j\bigr\|\Bigr\}.
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Support.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Support.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments

namespace OAI

/-!
Finite-volume enclosures for Gaussian matrix observations.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

open scoped Pointwise

def coordinateNorm {m : ℕ} (y : Fin m → ℝ) : ℝ := ‖WithLp.toLp 2 y‖

@[fun_prop] lemma continuous_coordinateNorm {m : ℕ} :
    Continuous (coordinateNorm (m := m)) := by
  unfold coordinateNorm
  fun_prop

def coordinateBall (m : ℕ) (r : ℝ) : Set (Fin m → ℝ) :=
  {y | coordinateNorm y ≤ r}

section Rows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def rowOperator {m : ℕ} (A : Fin m → E) : E →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun j => innerSL ℝ (A j)))

def netProjectionSupport (s : Finset E) (m : ℕ) :
    Set ((Fin m → E) × (Fin m → ℝ)) :=
  ⋃ u ∈ s, {z | coordinateNorm z.2 ≤ 2 * coordinateNorm (fun j => ⟪u, z.1 j⟫)}

end Rows

section NetNorm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
end NetNorm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end NoiselessRegression

end

end OAI


