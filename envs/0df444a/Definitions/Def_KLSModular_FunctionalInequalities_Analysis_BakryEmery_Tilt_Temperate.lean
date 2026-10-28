-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
-- name    : KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:09:24.038988+00:00
-- url     : https://prove2.me/theorems/2dcac3f7-3919-472b-8b13-591e955577ca
-- title:
--   Unit bump and scaled cutoff for tempered-growth tests
-- statement:
--   For a finite-dimensional real inner-product space $E$ with its Borel measurable structure, `unitBump` is a smooth bump centered at $0$ that equals $1$ on the closed unit ball and vanishes outside the ball of radius $2$. `cutoff R x` is the scaled function $\chi_R(x)=\varphi(R^{-1}x)$, where `R` is real and $\varphi$ is `unitBump`; the bundle contains no integrated generator identity.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic
--   import FunctionalInequalities.Analysis.BakryEmery.Gamma
--   import Mathlib.Analysis.Distribution.TemperateGrowth
--   import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def unitBump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`Analysis/BakryEmery/Gamma`](https://prove2.me/theorems/6b6aef00-0f84-4633-a830-e04239f02b6b).
--
--   Theorems in source order:
--
--   - [`hasCompactSupport_cutoff`](https://prove2.me/theorems/d329d169-7e19-4110-aeb8-20df20dddcfb)
--   - [`cutoff_eq_one`](https://prove2.me/theorems/85395b56-b174-481f-86b1-0d68ab4624ec)
--   - [`norm_iteratedFDeriv_cutoff_le`](https://prove2.me/theorems/d1de012f-6a55-4617-aaf5-23eabb181c3e)
--   - [`abs_laplacian_le`](https://prove2.me/theorems/f6e58a8e-3f46-421d-a064-a1f1705fd429)
--   - [`integrable_of_norm_le_pow`](https://prove2.me/theorems/7386231a-1383-4b09-86a5-2387ba9cd6db)
--   - [`integral_weightedLaplacian_eq_zero_of_growth`](https://prove2.me/theorems/43e73809-b964-4849-8ee0-2937a72e6eac)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean) · `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/Tilt/Temperate.lean#L31-L35 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.Tilt.Temperate`, definition bundle `KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Temperate`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

noncomputable section
open MeasureTheory Filter Topology FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff
namespace FunctionalInequalities
namespace Analysis
namespace BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- The bump `φ` on `E`: one on the closed unit ball, zero outside the ball of radius `2`. -/
def unitBump : ContDiffBump (0 : E) := ⟨1, 2, one_pos, one_lt_two⟩
/-- The scaled cutoff `χ_R(x) = φ(x / R)`. -/
def cutoff (R : ℝ) (x : E) : ℝ := (unitBump : ContDiffBump (0 : E)) (R⁻¹ • x)
variable (m : Measure E) [m.IsAddHaarMeasure]
end BakryEmery
end Analysis
end FunctionalInequalities


