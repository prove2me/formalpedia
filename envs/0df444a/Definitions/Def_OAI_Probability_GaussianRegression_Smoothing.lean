-- Prove2me | Definitions.Def_OAI_Probability_GaussianRegression_Smoothing
-- name    : OAI_Probability_GaussianRegression_Smoothing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T09:04:42.310123+00:00
-- url     : https://prove2.me/theorems/cf0fdfc6-200c-4788-9782-04b756566c6d
-- title:
--   Noise-smoothed density of linear measurements of a random vector
-- statement:
--   Let $E$ be a finite-dimensional real inner product space with its Borel $\sigma$-algebra, let $\nu$ be a measure on $E$, let $\varphi:\mathbb{R}\to[0,\infty]$, and let $m\in\mathbb{N}$. For a design $A=(A_0,\dots,A_{m-1})\in E^{m}$ and labels $y=(y_0,\dots,y_{m-1})\in\mathbb{R}^{m}$, the projection smoothing is
--   $$\mathcal S_{\nu,\varphi,m}(A,y)=\int_E\ \prod_{j=0}^{m-1}\varphi\big(y_j-\langle t,A_j\rangle\big)\,d\nu(t)\ \in[0,\infty].$$
--
--   If $\nu$ is a probability measure and $\varphi$ is a probability density on $\mathbb{R}$, then for a fixed design $A$ the function $y\mapsto\mathcal S_{\nu,\varphi,m}(A,y)$ is the Lebesgue density of the noisy labels $y_j=\langle t,A_j\rangle+\xi_j$, where $t\sim\nu$ and $\xi_0,\dots,\xi_{m-1}$ are independent with density $\varphi$ and independent of $t$. With $\varphi$ a centered Gaussian density of small variance, it is a smoothed version of the law of the noiseless labels $\langle t,A_j\rangle$. Its moments against the product of Gaussian rows and Lebesgue measure on labels are bounded through inverse Gram–Schmidt moments of $\nu$, and these bounds yield Hölder-type comparisons between the noiseless observation law and the Gaussian reference measure.
--
--   **Formalization Note** The Lean name is `projectionSmoothing ν φ m z`, where `z : (Fin m → E) × (Fin m → ℝ)` is the pair $(A,y)$ and the integral is the lower Lebesgue integral `∫⁻`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Smoothing.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/GaussianRegression/Smoothing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the NoiselessRegression mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments

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


