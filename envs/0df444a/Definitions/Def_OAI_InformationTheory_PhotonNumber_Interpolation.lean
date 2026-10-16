-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
-- name    : OAI_InformationTheory_PhotonNumber_Interpolation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T23:52:58.080741+00:00
-- url     : https://prove2.me/theorems/9e0a5cb3-4656-4375-97a6-cf834ec56173
-- title:
--   Resolvent functions of a circle measure and an interpolation quadratic form
-- statement:
--   This file defines a few auxiliary functions used to interpolate between weights: two resolvent-type functions built from a finite measure on the circle, an averaged reciprocal, and a five-term quadratic form in two complex variables.
--
--   Notation: $\Theta = [0,2\pi]$; for a finite measure $\mu$ on $\Theta$, $\mathcal K_\mu(s) = \int_\Theta\omega(\theta)/(1+(s-1)t(\theta))\,d\mu(\theta)$, where $t(\theta) = (1-\cos\theta+\max(0,\sin\theta))/(2(1+\max(0,\sin\theta)))$ and $\omega(\theta) = 1/(1+\max(0,\sin\theta))$; and $f(x) = x/\sinh x$ with $f(0) = 1$.
--
--   1. **Resolvent functions.** For $s\in\mathbb{C}$,
--   $$
--   B_\mu(s) = 1-(s-1)\,\mathcal K_\mu(s),\qquad R_\mu(s) = \bigl(s\,\mathcal K_\mu(s)\bigr)^{-1}.
--   $$
--
--   2. **Averaged reciprocal.** For $D:\mathbb{R}\to\mathbb{R}$ and $s,t\in\mathbb{R}$, $\mathcal E_D(s,t) = \bigl(\int_0^1D((1-\theta)s+\theta t)\,d\theta\bigr)^{-1}$.
--
--   3. **Interpolation quadratic form.** For reals $m,x,y,e$ and $\xi,\varphi\in\mathbb{C}$,
--   $$
--   Q = \tfrac14mf(x)e^{x}|\xi-\varphi|^2 + \tfrac14mf(x)e^{-x}|\xi+\varphi|^2 + \tfrac14mf(y)e^{y}|\xi+\varphi|^2 + \tfrac14mf(y)e^{-y}|\xi-\varphi|^2 + m\,e\,|\varphi|^2 .
--   $$
--
--   These are named expressions only; they fix the precise form of the interpolating weights and of the quadratic form compared in later estimates.
--
--   **Formalization Note** Inverses use the convention $0^{-1} = 0$, and the integrals are Bochner integrals (zero for non-integrable integrands); $\int_0^1$ is taken over the subtype $[0,1]$ with its restricted Lebesgue measure.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Interpolation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal

namespace EntropyPhotonNumber
open Herglotz MeasureTheory

end EntropyPhotonNumber

namespace EntropyPhotonNumber.Herglotz

end EntropyPhotonNumber.Herglotz

namespace EntropyPhotonNumber
open MeasureTheory Herglotz

def resolventB (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  1 - (s - 1) * compactIntegral μ s

def resolventR (μ : FiniteMeasure Angle) (s : ℂ) : ℂ :=
  (s * compactIntegral μ s)⁻¹

end EntropyPhotonNumber

end

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology

namespace EntropyPhotonNumber

section
open DiagonalForms.System MeasureTheory Set Filter Topology

def genericAdditionalE (D : ℝ → ℝ) (s t : ℝ) : ℝ :=
  (∫ θ : UnitInterval, D ((1-θ.val)*s+θ.val*t))⁻¹

def interpolationQuadratic (m x y e : ℝ) (ξ φ : ℂ) : ℝ :=
  1/4*(m*f x*Real.exp x*Complex.normSq (ξ-φ)) +
  1/4*(m*f x*Real.exp (-x)*Complex.normSq (ξ+φ)) +
  1/4*(m*f y*Real.exp y*Complex.normSq (ξ+φ)) +
  1/4*(m*f y*Real.exp (-y)*Complex.normSq (ξ-φ)) +
  m*e*Complex.normSq φ

end

open DiagonalForms.System MeasureTheory Set Filter Topology Herglotz

end EntropyPhotonNumber

end

end OAI


