-- Prove2me | Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
-- name    : OAI_Probability_Subsphere_Regression_Gaussian
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T05:31:51.556739+00:00
-- url     : https://prove2.me/theorems/391baaae-7800-4988-8cc7-a3d654692da7
-- title:
--   Noise-smoothed density of the matrix–label observation law
-- statement:
--   Let $E$ be a real inner product space equipped with a $\sigma$-algebra, let $\nu$ be a measure on $E$, let $\varphi:\mathbb{R}\to[0,\infty]$ be a function (typically a probability density, such as a centred Gaussian density) and let $m\in\mathbb{N}$. An observation is a pair $z=(A,y)$ of $m$ rows $A=(A_0,\dots,A_{m-1})\in E^m$ and $m$ labels $y=(y_0,\dots,y_{m-1})\in\mathbb{R}^m$. The *projection smoothing* of $\nu$ by $\varphi$ is the function on observations
--
--   $$
--   S_{\nu,\varphi,m}(A,y)=\int_E\ \prod_{j=0}^{m-1}\varphi\bigl(y_j-\langle t,A_j\rangle\bigr)\,d\nu(t)\ \in[0,\infty].
--   $$
--
--   If a hidden vector $t$ is drawn from $\nu$ and every label is the noiseless projection $\langle t,A_j\rangle$ perturbed by independent noise with (measurable) density $\varphi$, then for fixed rows $A$ the function $y\mapsto S_{\nu,\varphi,m}(A,y)$ is the density of the label vector with respect to Lebesgue measure on $\mathbb{R}^m$ (of total mass $\nu(E)$). With Gaussian rows, $S_{\nu,\varphi,m}$ is therefore the density of the joint matrix–label law with respect to the product of the Gaussian row law and Lebesgue measure, and its moments are what is controlled when $\nu$ satisfies a local mass bound.
--
--   **Formalization Note** `projectionSmoothing ν φ m z` is a lower Lebesgue integral of an `ℝ≥0∞`-valued integrand; no measurability or normalization of $\varphi$ is assumed in the definition. Only the inner product and the measurable structure of $E$ are used (the finite-dimensionality and Borel assumptions of the surrounding section are not arguments).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gaussian.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Subsphere/Regression/Gaussian.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SubsphereCurrent mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
namespace SubsphereRegression
open scoped Topology
open InnerProductSpace
section GaussianDomination
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianDomination

section ReplicaKernel
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ReplicaKernel

section GaussianKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianKernel

section SmoothingMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Product scalar smoothing of the joint matrix--label observation law. -/
def projectionSmoothing (ν : Measure E) (φ : ℝ → ℝ≥0∞) (m : ℕ)
    (z : (Fin m → E) × (Fin m → ℝ)) : ℝ≥0∞ :=
  ∫⁻ t, ∏ j, φ (z.2 j - ⟪t, z.1 j⟫) ∂ν

end SmoothingMoments

section ProductDensity
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]

end ProductDensity

section GaussianNoise
end GaussianNoise

section HolderSet
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
end HolderSet

section LimitSet
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

end LimitSet

variable {Y : Type*} [MeasurableSpace Y] [TopologicalSpace Y]

end SubsphereRegression

end

end OAI


