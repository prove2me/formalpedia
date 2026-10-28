-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_SmoothGradient_Basic
-- name    : KLSModular_FunctionalInequalities_Energy_SmoothGradient_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:28:08.032829+00:00
-- url     : https://prove2.me/theorems/230d76a3-8a28-41f5-a6c8-38e17a1abcdd
-- title:
--   Smooth-gradient tests and their L² relaxation
-- statement:
--   `Energy.SmoothGradient.Test μ` consists of globally C∞ real functions that belong to L²(μ) and whose squared canonical gradient norm is integrable. Its finite energy is the NNReal value represented by the real integral of ‖∇f‖², with no factor of 1/2, and `toL2` is the represented L²(μ) class. `preEnergy` realizes these tests in L²(μ), while `relaxation` is their sequential L² relaxation as an ENNReal-valued functional. The module does not identify this relaxation with Cheeger energy or assert density or closedness beyond what is encoded by the imported relaxation construction.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Relaxation.Basic
--   import Mathlib.Analysis.Calculus.ContDiff.Basic
--   import Mathlib.Analysis.Calculus.Gradient.Basic
--   import Mathlib.MeasureTheory.Function.L2Space
--   import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   structure Test (μ : ProbabilityMeasure E) where
--     /-- The real-valued test function. -/
--     toFun : E → ℝ
--     /-- The test is globally `C∞`.
--
--     In Mathlib's differentiability index, `∞` denotes ordinary infinite differentiability;
--     `⊤` is the stronger analytic regularity and is not required here.
--     -/
--     contDiff : ContDiff ℝ ∞ toFun
--     /-- The test defines an element of real `L²(μ)`. -/
--     memLp_two : MemLp toFun 2 (μ : Measure E)
--     /-- The squared norm of the canonical Hilbert gradient is integrable. -/
--     gradient_sq_integrable :
--       Integrable (fun x ↦ ‖gradient toFun x‖ ^ 2) (μ : Measure E)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Relaxation/Basic`](https://prove2.me/theorems/89c7a615-0c3d-45b2-8b60-f8b981228e0a).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/SmoothGradient/Basic.lean) · `FunctionalInequalities.Energy.SmoothGradient.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/SmoothGradient/Basic.lean#L35-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.SmoothGradient.Basic`, definition bundle `KLSModular_FunctionalInequalities_Energy_SmoothGradient_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Relaxation_Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities
namespace Energy
namespace SmoothGradient
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E]
/-- A globally `C∞` real `L²(μ)` test with finite canonical gradient energy. -/
structure Test (μ : ProbabilityMeasure E) where
  /-- The real-valued test function. -/
  toFun : E → ℝ
  /-- The test is globally `C∞`.

  In Mathlib's differentiability index, `∞` denotes ordinary infinite differentiability;
  `⊤` is the stronger analytic regularity and is not required here.
  -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- The test defines an element of real `L²(μ)`. -/
  memLp_two : MemLp toFun 2 (μ : Measure E)
  /-- The squared norm of the canonical Hilbert gradient is integrable. -/
  gradient_sq_integrable :
    Integrable (fun x ↦ ‖gradient toFun x‖ ^ 2) (μ : Measure E)
namespace Test
variable {μ : ProbabilityMeasure E}
instance : CoeFun (Test μ) (fun _ ↦ E → ℝ) :=
  ⟨toFun⟩
/-- The squared gradient norm is pointwise nonnegative. -/
theorem gradientSq_nonneg (f : Test μ) (x : E) :
    0 ≤ ‖gradient f.toFun x‖ ^ 2 :=
  sq_nonneg _
/-- The finite real integral underlying the smooth-gradient energy is nonnegative. -/
theorem gradientIntegral_nonneg (f : Test μ) :
    0 ≤ ∫ x, ‖gradient f.toFun x‖ ^ 2 ∂(μ : Measure E) :=
  integral_nonneg f.gradientSq_nonneg
/-- The finite canonical gradient integral, valued in `NNReal`. -/
def energy (f : Test μ) : NNReal :=
  ⟨∫ x, ‖gradient f.toFun x‖ ^ 2 ∂(μ : Measure E), f.gradientIntegral_nonneg⟩
/-- Coercing the finite energy to `ℝ` recovers its defining integral. -/
@[simp, norm_cast]
theorem coe_energy (f : Test μ) :
    (f.energy : ℝ) = ∫ x, ‖gradient f.toFun x‖ ^ 2 ∂(μ : Measure E) :=
  rfl
/-- The `L²(μ)` element represented by a smooth-gradient test. -/
def toL2 (f : Test μ) : Lp ℝ 2 (μ : Measure E) :=
  f.memLp_two.toLp f.toFun
end Test
/-- The finite smooth-gradient pre-energy, realized in real `L²(μ)`. -/
def preEnergy (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] :
    PreEnergy (Lp ℝ 2 (μ : Measure E)) where
  Test := Test μ
  toAmbient := Test.toL2
  energy := Test.energy
/-- The ambient realization of the smooth-gradient pre-energy is the test's `L²` class. -/
@[simp]
theorem preEnergy_toAmbient (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E]
    (f : Test μ) :
    (preEnergy μ).toAmbient f = f.toL2 :=
  rfl
/-- The smooth-gradient pre-energy is exactly the finite squared-gradient integral. -/
@[simp]
theorem preEnergy_energy (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E]
    (f : Test μ) :
    (preEnergy μ).energy f = f.energy :=
  rfl
/-- The sequential `L²` relaxation of the smooth-gradient pre-energy.

This is the intended candidate for the standard canonical energy `2 Ch`. The equality with
`2 Ch`, and the required smooth-core density statement, are deliberately left as later
theorems rather than built into this name. -/
def relaxation (μ : ProbabilityMeasure E) [FiniteDimensional ℝ E]
    [BorelSpace E] [SecondCountableTopology E] :
    Functional (Lp ℝ 2 (μ : Measure E)) :=
  (preEnergy μ).sequentialRelaxation
end SmoothGradient
end Energy
end FunctionalInequalities


