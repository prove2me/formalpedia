-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
-- name    : KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:14:04.990278+00:00
-- url     : https://prove2.me/theorems/4d5469da-893c-48b4-9cb5-3ecfda5a30ce
-- title:
--   Local and asymptotic Lipschitz secants
-- statement:
--   `LocalSlope.secant` is the $[0,\infty]$-valued one-moving-point secant supremum over points in the open ball of radius $r$ around $x$. `AsymptoticLipschitz.secant` is the corresponding two-moving-point supremum, using pairs of points in that ball. These definitions are the local building blocks for the respective slope and asymptotic-Lipschitz quantities.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.Energy.Cheeger.Basic
--   import FunctionalInequalities.Energy.Euclidean.LipschitzApproximation.Kernel
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def secant (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
--     ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`Energy/Cheeger/Basic`](https://prove2.me/theorems/dc67c94c-a471-46e0-bd49-64593ddca49c), [`Energy/Euclidean/LipschitzApproximation/Kernel`](https://prove2.me/theorems/d8350731-5ebe-4c22-a05d-d6b04921850a).
--
--   Theorems in source order:
--
--   - [`locallyLipschitz_mul`](https://prove2.me/theorems/0d72763a-6b0b-466f-9759-3b5ebd4e877f)
--   - [`exists_lipschitzWith_of_eq_zero_outside_ball`](https://prove2.me/theorems/edf2acd8-cdce-45dd-bafd-8681d2aeaf30)
--   - [`apply_mul_le`](https://prove2.me/theorems/bf9de844-4401-433d-8497-f00f6238df47)
--   - [`lipschitzOnWith_mollify_ball`](https://prove2.me/theorems/f6c8681b-1ff6-4044-8f83-791d558075e3)
--   - [`limsup_enorm_gradient_mollify_le`](https://prove2.me/theorems/b7115fba-b7b4-4e77-ad68-d8e10c4a65ff)
--   - [`relaxation_le_asymptoticLipschitz_of_lipschitzWith`](https://prove2.me/theorems/0c999886-ba48-46f7-9658-d121570cc5c9)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean) · `FunctionalInequalities.Energy.Euclidean.Slope.Recovery` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/Euclidean/Slope/Recovery.lean#L55-L126 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.Euclidean.Slope.Recovery`, definition bundle `KLSModular_FunctionalInequalities_Energy_Euclidean_Slope_Recovery`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Cheeger_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Energy_Euclidean_LipschitzApproximation_Kernel

noncomputable section
open MeasureTheory Filter Topology Set
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation
open scoped ENNReal NNReal ContDiff
namespace FunctionalInequalities
namespace Energy
universe u
namespace LocalSlope
section Metric
variable {X : Type*} [MetricSpace X]
/-- The one-moving-point secant supremum on the open ball of radius `r` around `x`.  The local
slope is its infimum over positive radii. -/
def secant (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < r), ENNReal.ofReal (dist (f y) (f x) / dist y x)
end Metric
end LocalSlope
namespace AsymptoticLipschitz
section Metric
variable {X : Type*} [MetricSpace X]
/-- The two-moving-point secant supremum on the open ball of radius `r` around `x`.  The
asymptotic Lipschitz constant is its infimum over positive radii. -/
def secant (f : X → ℝ) (r : ℝ) (x : X) : ℝ≥0∞ :=
  ⨆ (y : X) (_ : dist y x < r) (z : X) (_ : dist z x < r),
    ENNReal.ofReal (dist (f y) (f z) / dist y z)
end Metric
end AsymptoticLipschitz
end Energy
end FunctionalInequalities


