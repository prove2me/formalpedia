-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
-- name    : OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T16:36:05.205948+00:00
-- url     : https://prove2.me/theorems/dd7322e6-c75f-498d-811e-1ba8deabb263
-- title:
--   Projection smoothing of a measure
-- statement:
--   For a measure $\nu$ on an inner product space $E$, a nonnegative profile $\varphi$ on $\mathbb R$ and $m$ rows, projection smoothing assigns to a matrix of rows $A=(A_1,\dots,A_m)$ and labels $y\in\mathbb R^m$ the value
--   $$
--   \int\prod_{j=1}^m\varphi\bigl(y_j-\langle t,A_j\rangle\bigr)\,d\nu(t).
--   $$
--
--   It is the density of the projected measure smoothed by the noise profile $\varphi$, and it is used to pass from noisy to noiseless observations by weak limits.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Smoothing.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Smoothing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ProjectionMoments mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments

namespace OAI

/-!
Projection smoothing, Gaussian noise, and bounds under weak limits.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace

noncomputable section

universe u

namespace NoiselessRegression

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def projectionSmoothing (ν : Measure E) (φ : ℝ → ℝ≥0∞) (m : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, ∏ j, φ (z.2 j - ⟪t, z.1 j⟫) ∂ν

end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ProductDensity

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

end NoiselessRegression

end

end OAI


