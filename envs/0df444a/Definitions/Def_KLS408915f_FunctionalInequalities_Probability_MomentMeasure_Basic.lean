-- Prove2me | Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
-- name    : KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T12:53:10.920526+00:00
-- url     : https://prove2.me/theorems/57dc3be6-f59f-4b42-b349-c20f3685e3d3
-- title:
--   Exponential potential measures and variational functional
-- statement:
--   For an extended-real potential $\varphi:E\to\overline{\mathbb{R}}$, `density φ` is the $[0,\infty]$-valued density $\exp(-\varphi)$, `weightedMeasure dx φ` is the measure with density `density φ` relative to $dx$, and `mass dx φ` is $\int^*\exp(-\varphi)\,d x$. `PotentialIntegrable φ μ` requires no value $-\infty$, almost-everywhere finiteness, and integrability of $\varphi.toReal$ with respect to $\mu$; `variationalFunctional dx μ φ` is $\log(	ext{mass}(dx,\varphi^*))-\int \varphi.toReal\,d\mu$ using the extended logarithm, with no probability normalization imposed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Basic.lean#L33-L58 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Basic`, definition bundle `KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
namespace FunctionalInequalities
namespace Probability
namespace MomentMeasure
open MeasureTheory
open scoped ENNReal
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The extended exponential handles `+∞` potentials correctly: density zero. -/
def density (φ : E → EReal) (x : E) : ℝ≥0∞ := EReal.exp (-φ x)
section Measurable
variable [MeasurableSpace E]
/-- Integrability in CEK Proposition 12, including a.e. finiteness before using `toReal`. -/
def PotentialIntegrable (φ : E → EReal) (μ : Measure E) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ (∀ᵐ x ∂μ, φ x ≠ ⊤) ∧
    Integrable (fun x => (φ x).toReal) μ
section Haar
variable [BorelSpace E] [FiniteDimensional ℝ E]
/-- The measure `exp(-φ(x)) dx`, without implicit probability normalization. -/
def weightedMeasure (dx : Measure E) (φ : E → EReal) : Measure E :=
  dx.withDensity (density φ)
/-- `Z(φ)`, retaining both zero and infinite mass rather than totalizing a real logarithm. -/
def mass (dx : Measure E) (φ : E → EReal) : ℝ≥0∞ := ∫⁻ x, density φ x ∂dx
/-- CEK's functional `I_μ(f) = log ∫ exp(-f*) - ∫ f dμ`, with extended logarithm. -/
def variationalFunctional (dx μ : Measure E) (φ : E → EReal) : EReal :=
  ENNReal.log (mass dx (legendre φ)) - (∫ x, (φ x).toReal ∂μ : ℝ)
end Haar
end Measurable
end MomentMeasure
end Probability
end FunctionalInequalities


