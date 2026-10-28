-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Probability_Line_Laplace
-- name    : KLSModular_FunctionalInequalities_Probability_Line_Laplace
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:04:56.301864+00:00
-- url     : https://prove2.me/theorems/cba52f6e-b244-4595-8333-a1bd8a9b0069
-- title:
--   The one-dimensional Laplace measure
-- statement:
--   For a real rate $\beta$, `laplaceDensity β s` is $(\beta/2)e^{-\beta|s|}$ and `laplaceMeasure β` is Lebesgue measure weighted by its `ENNReal.ofReal` density. When $\beta>0$, the bundle proves that the density integrates to $1$, is integrable, and that `laplaceMeasure β` is a probability measure. The private rational moment-generating expressions are $\beta^2/(\beta^2-w^2)$ and its displayed derivative; they are definitions only, without a domain condition in their types.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.MeasureTheory.Measure.WithDensity
--   import Mathlib.Analysis.SpecialFunctions.Exp
--   import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
--   import Mathlib.MeasureTheory.Integral.IntegralEqImproper
--   import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
--   import Mathlib.Probability.Moments.MGFAnalytic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def laplaceDensity (β s : ℝ) : ℝ := β / 2 * Real.exp (-(β * |s|))
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`integral_exp_mul_laplaceDensity`](https://prove2.me/theorems/7b9ed9dc-464c-47c0-b655-8b9cc377d49c)
--   - [`laplaceMeasure_mgf`](https://prove2.me/theorems/e6314ac4-2242-4f95-90fa-1ef8e685bab6)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Line/Laplace.lean) · `FunctionalInequalities.Probability.Line.Laplace` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Line/Laplace.lean#L26-L302 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Line.Laplace`, definition bundle `KLSModular_FunctionalInequalities_Probability_Line_Laplace`; the repository is private at upload time).

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.MGFAnalytic

noncomputable section
open MeasureTheory
namespace FunctionalInequalities
namespace Probability
namespace Line
/-- The Laplace density `(β/2) e^{-β|s|}`. -/
def laplaceDensity (β s : ℝ) : ℝ := β / 2 * Real.exp (-(β * |s|))
/-- The Laplace law with rate `β`: Lebesgue measure with density `(β/2) e^{-β|s|}`. -/
def laplaceMeasure (β : ℝ) : Measure ℝ :=
  volume.withDensity fun s => ENNReal.ofReal (laplaceDensity β s)
/-- The Laplace density has total integral `1`. -/
theorem integral_laplaceDensity {β : ℝ} (hβ : 0 < β) :
    ∫ x : ℝ, laplaceDensity β x = 1 := by
  have habs :
      ∫ x : ℝ, Real.exp (-β * |x|) =
        2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) := by
    simpa using
      (integral_comp_abs (f := fun x : ℝ => Real.exp (-β * x)))
  have hi :
      ∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) = β⁻¹ := by
    simpa using integral_exp_mul_Ioi (a := -β) (by linarith) 0
  have habs' :
      ∫ x : ℝ, Real.exp (-(β * |x|)) =
        2 * ∫ x in Set.Ioi (0 : ℝ), Real.exp (-β * x) := by
    simpa only [neg_mul] using habs
  simp only [laplaceDensity, integral_const_mul]
  rw [habs', hi]
  field_simp
/-- The Laplace density is integrable. -/
theorem integrable_laplaceDensity {β : ℝ} (hβ : 0 < β) :
    Integrable (laplaceDensity β) := by
  have hneg :
      IntegrableOn (fun x : ℝ => Real.exp (-(β * |x|))) (Set.Iic 0) := by
    have h := integrableOn_exp_mul_Iic (a := β) hβ 0
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
    rw [abs_of_nonpos hx]
    ring_nf
  have hpos :
      IntegrableOn (fun x : ℝ => Real.exp (-(β * |x|))) (Set.Ioi 0) := by
    have h := integrableOn_exp_mul_Ioi (a := -β) (by linarith) 0
    refine h.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp [abs_of_pos (show 0 < x from hx), neg_mul]
  have h :
      IntegrableOn (fun x : ℝ => Real.exp (-(β * |x|)))
        (Set.Iic 0 ∪ Set.Ioi 0) :=
    hneg.union hpos
  have h' :
      Integrable (fun x : ℝ => Real.exp (-(β * |x|))) := by
    simpa [Set.Iic_union_Ioi] using h
  have hc := h'.const_mul (β / 2)
  change Integrable (fun x : ℝ => β / 2 * Real.exp (-(β * |x|)))
  exact hc
/-- For `β > 0`, `laplaceMeasure β` has total mass `1`. -/
theorem isProbabilityMeasure_laplaceMeasure {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (laplaceMeasure β) := by
    refine ⟨?_⟩
    simp [laplaceMeasure, withDensity_apply, MeasurableSet.univ,
      Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · rw [integral_laplaceDensity hβ]
      norm_num
    · exact integrable_laplaceDensity hβ
    · exact Filter.Eventually.of_forall (fun x => by
        simp [laplaceDensity]
        positivity)
section Moments
open ProbabilityTheory Filter Set
open scoped Topology
 noncomputable def rationalMgf (β w : ℝ) : ℝ := β ^ 2 / (β ^ 2 - w ^ 2)
 noncomputable def rationalMgfDeriv (β w : ℝ) : ℝ :=
  2 * β ^ 2 * w / (β ^ 2 - w ^ 2) ^ 2
end Moments
end Line
end Probability
end FunctionalInequalities


