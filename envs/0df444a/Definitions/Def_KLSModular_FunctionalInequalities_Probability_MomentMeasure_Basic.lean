-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Basic
-- name    : KLSModular_FunctionalInequalities_Probability_MomentMeasure_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:57:24.576846+00:00
-- url     : https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c
-- title:
--   Exponential potential measures and variational functional
-- statement:
--   For an extended-real potential $\varphi:E\to\overline{\mathbb{R}}$, `density φ` is the $[0,\infty]$-valued density $\exp(-\varphi)$, `weightedMeasure dx φ` is the measure with density `density φ` relative to $dx$, and `mass dx φ` is $\int^*\exp(-\varphi)\,d x$. `PotentialIntegrable φ μ` requires no value $-\infty$, almost-everywhere finiteness, and integrability of $\varphi.toReal$ with respect to $\mu$; `variationalFunctional dx μ φ` is $\log(\text{mass}(dx,\varphi^*))-\int \varphi.toReal\,d\mu$ using the extended logarithm, with no probability normalization imposed.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.Convex.Legendre
--   import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
--   import Mathlib.MeasureTheory.Measure.WithDensity
--   import Mathlib.MeasureTheory.Integral.Bochner.Basic
--   import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def density (φ : E → EReal) (x : E) : ℝ≥0∞ := EReal.exp (-φ x)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/Basic.lean) · `FunctionalInequalities.Probability.MomentMeasure.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/Basic.lean#L33-L58 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.Basic`, definition bundle `KLSModular_FunctionalInequalities_Probability_MomentMeasure_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

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


