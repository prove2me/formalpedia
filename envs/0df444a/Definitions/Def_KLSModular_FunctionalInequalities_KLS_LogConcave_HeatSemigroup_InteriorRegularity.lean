-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:24:09.077985+00:00
-- url     : https://prove2.me/theorems/79e586aa-54d4-4c9a-ac32-31116ce1ca0f
-- title:
--   Mollifier Bumps and Tilted Densities
-- statement:
--   Under the finite-dimensional real inner-product-space assumptions on $V$, `mollifier n` is a smooth compactly supported bump centered at $0$ whose inner and outer radii are respectively $1/(2(n+1))$ and $1/(n+1)$, for $n\in\mathbb{N}$; the Haar-measure assumptions are omitted from this definition. For a measurable space $V$, `tiltedDensity m U` is the real-valued function $x\mapsto \frac{\exp(-U(x))}{\int \exp(-U(y))\,dm(y)}$ associated with a measure $m$ on $V$ and a potential $U:V\to\mathbb{R}$, whenever the displayed denominator is meaningful. These are auxiliary definitions used by the surrounding interior-regularity development.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore
--   import FunctionalInequalities.Analysis.Mollification.Basic
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   private def mollifier (n : ℕ) : ContDiffBump (0 : V) where
--     rIn := 1 / (2 * ((n : ℝ) + 1))
--     rOut := 1 / ((n : ℝ) + 1)
--     rIn_pos := by positivity
--     rIn_lt_rOut := by
--       have ha : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
--       rw [show (1 : ℝ) / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 by field_simp]
--       exact half_lt_self ha
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/OperatorCore`](https://prove2.me/theorems/49f2d187-0409-49fa-a861-f4dcb4534ed2), [`Analysis/Mollification/Basic`](https://prove2.me/theorems/b351487c-eaef-4d4f-b656-728d01c5702d).
--
--   Theorems in source order:
--
--   - [`norm_toLp_smul_gradient_le`](https://prove2.me/theorems/498d247b-5ee4-41ec-a4b1-bd5e9cc8d247)
--   - [`integral_laplacian_mul_convolution_eq`](https://prove2.me/theorems/4e49d784-08a5-433a-989e-30d5dbb063cf)
--   - [`integral_laplacian_mul_tiltedDensity_mul`](https://prove2.me/theorems/f41686bf-c848-414b-978b-8c5c05a45d74)
--   - [`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`](https://prove2.me/theorems/44e63681-21ce-4775-a563-130ebf063881)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean) · `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/InteriorRegularity.lean#L116-L345 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.InteriorRegularity`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_InteriorRegularity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Mollification_Basic

noncomputable section
open MeasureTheory Filter Topology Metric InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace Convolution ENNReal
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
open Energy Energy.WeightedGradient
section Haar
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (m : Measure V) [m.IsAddHaarMeasure]
omit [CompleteSpace V] [MeasurableSpace V] [BorelSpace V] [m.IsAddHaarMeasure] in
/-- The standard mollifier sequence: bumps of radii `1/(2(n+1)) < 1/(n+1)`. -/
 def mollifier (n : ℕ) : ContDiffBump (0 : V) where
  rIn := 1 / (2 * ((n : ℝ) + 1))
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have ha : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rw [show (1 : ℝ) / (2 * ((n : ℝ) + 1)) = (1 / ((n : ℝ) + 1)) / 2 by field_simp]
    exact half_lt_self ha
end Haar
section Density
variable {V : Type*} [MeasurableSpace V] {ν : ProbabilityMeasure V} (m : Measure V) {U : V → ℝ}
/-- The normalised density `exp (-U) / ∫ exp (-U) dm` of `m.tilted (-U)`. -/
 def tiltedDensity (m : Measure V) (U : V → ℝ) (x : V) : ℝ :=
  Real.exp ((-U) x) / ∫ y, Real.exp ((-U) y) ∂m
end Density
end LogConcave
end KLS
end FunctionalInequalities


