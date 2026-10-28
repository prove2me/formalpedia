-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
-- name    : KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:29:56.415633+00:00
-- url     : https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f
-- title:
--   Smooth-test Poincaré constant
-- statement:
--   `Poincare.SmoothTest.Admissible μ f` requires a globally C∞ real function f, membership in L²(μ), and integrability of the squared canonical gradient norm. `SmoothTest.energy` is the real integral of ‖∇f‖² with respect to μ, and `SmoothTest.Holds μ C` additionally requires μ to be a probability measure, C to be nonnegative, and the variance inequality to hold for every admissible test. `SmoothTest.constant` is the ENNReal infimum over finite NNReal constants satisfying `Holds`, with ⊤ representing the absence of a finite valid constant.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Calculus.ContDiff.Basic
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import Mathlib.Probability.Moments.Variance
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure Admissible (μ : Measure E) (f : E → ℝ) : Prop where
--     smooth' : ContDiff ℝ ∞ f
--     memLp_two : MemLp f 2 μ
--     energy_integrable : Integrable (fun x ↦ ‖gradient f x‖ ^ 2) μ
--   ```
--
--   **Module navigation**
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/Basic.lean) · `FunctionalInequalities.Poincare.SmoothTest.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Basic.lean#L33-L94 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Basic`, definition bundle `KLSModular_FunctionalInequalities_Poincare_SmoothTest_Basic`; the repository is private at upload time).

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace FunctionalInequalities
namespace Poincare
namespace SmoothTest
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]
  [MeasurableSpace E]
/-- Source: local test-domain encoding of Definition 2.1, linked above.
Global `ContDiff ℝ ∞` and finite canonical-gradient energy are explicit local choices;
the energy field prevents a nonintegrable real integral from being assigned zero. -/
structure Admissible (μ : Measure E) (f : E → ℝ) : Prop where
  smooth' : ContDiff ℝ ∞ f
  memLp_two : MemLp f 2 μ
  energy_integrable : Integrable (fun x ↦ ‖gradient f x‖ ^ 2) μ
/-- Source: the energy formula in Definition 2.1, realized as a real Bochner integral.
Its finite-energy use is controlled by `Admissible.energy_integrable`. -/
def energy (μ : Measure E) (f : E → ℝ) : ℝ :=
  ∫ x, ‖gradient f x‖ ^ 2 ∂μ
/-- Source: the inequality in [Definition 2.1](https://github.com/human-ai-mathematics/kls-conjecture-search/blob/cd4a894a0faf40c0180f80b1a31eec1fdb6cb576/modules/01-definitions.tex#L17-L25),
with the local Hilbert test domain `Admissible`. Probability and finite-constant
nonnegativity are explicit; no source-domain or spectral-gap equivalence is asserted. -/
structure Holds (μ : Measure E) (C : ℝ) : Prop where
  probability : IsProbabilityMeasure μ
  constant_nonneg : 0 ≤ C
  variance_le : ∀ ⦃f : E → ℝ⦄, Admissible μ f →
    variance f μ ≤ C * energy μ f
/-- Source: local extended-infimum encoding of the optimal constant in Definition 2.1.
The infimum ranges over finite `NNReal` constants satisfying the local `Holds`; an empty
set of valid constants gives `⊤`. This definition does not identify a spectral gap. -/
def constant (μ : Measure E) : ENNReal :=
  ⨅ C : {C : NNReal // Holds μ (C : ℝ)}, (C.1 : ENNReal)
end SmoothTest
end Poincare
end FunctionalInequalities


