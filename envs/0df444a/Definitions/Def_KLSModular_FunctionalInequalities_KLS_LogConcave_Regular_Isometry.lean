-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isometry
-- name    : KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isometry
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:53:40.830081+00:00
-- url     : https://prove2.me/theorems/844bb102-d20e-4faf-9d4a-a819ecee9415
-- title:
--   Regular potentials under linear isometries
-- statement:
--   If `V` is a `RegularPotential` on a finite-dimensional inner-product space $E$ and $L:E\simeq F$ is a real linear isometry, `RegularPotential.comp_isometry` states that $y\mapsto V(L^{-1}y)$ is a regular potential on $F$ with the same constants $a,b$. The conclusion preserves the temperate-growth and pointwise Hessian bounds exactly under the isometry.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.Regular.Basic
--   import FunctionalInequalities.Probability.Transport
--   import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
--   import FunctionalInequalities.KLS.Isotropic
--   import FunctionalInequalities.Poincare.SmoothTest.Transport
--   import FunctionalInequalities.KLS.LogConcave.Poincare
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   theorem RegularPotential.comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
--       (L : E ≃ₗᵢ[ℝ] F) :
--       KLS.RegularPotential (fun y => V (L.symm y)) a b
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/Regular/Basic`](https://prove2.me/theorems/2380e904-df18-4ce0-91da-7cc8a4c0e342), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Poincare/SmoothTest/Transport`](https://prove2.me/theorems/f97165f6-9a6a-4e3a-aff4-a4bd22cfc6b6), [`KLS/LogConcave/Poincare`](https://prove2.me/theorems/22f55d8a-6675-4b7a-ac3b-ac21c6c833d3).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isometry.lean) · `FunctionalInequalities.KLS.LogConcave.Regular.Isometry` · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), item E12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Regular/Isometry.lean#L31-L47 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Regular.Isometry`, definition bundle `KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Isometry`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Regular_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Transport
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Poincare

open MeasureTheory
open scoped ContDiff
namespace FunctionalInequalities
namespace KLS
universe u v
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- **Regular potentials are preserved by linear isometries** `L : E ≃ F`, with the same constants `a, b`. -/
theorem RegularPotential.comp_isometry {V : E → ℝ} {a b : ℝ} (hV : KLS.RegularPotential V a b)
    (L : E ≃ₗᵢ[ℝ] F) :
    KLS.RegularPotential (fun y => V (L.symm y)) a b := by
  have hV2 : ContDiff ℝ 2 V := hV.temperate.1.of_le (WithTop.coe_le_coe.mpr le_top)
  refine ⟨hV.temperate.comp L.symm.toContinuousLinearEquiv.hasTemperateGrowth, hV.pos, ?_, ?_⟩
  · intro y w
    have hh := Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_clm hV2 (L.symm : F →L[ℝ] E) y w w
    simp only [LinearIsometryEquiv.coe_coe''] at hh
    rw [hh]
    simpa only [LinearIsometryEquiv.norm_map] using hV.lower (L.symm y) (L.symm w)
  · intro y w
    have hh := Analysis.BakryEmery.bilinearIteratedFDerivTwo_comp_clm hV2 (L.symm : F →L[ℝ] E) y w w
    simp only [LinearIsometryEquiv.coe_coe''] at hh
    rw [hh]
    simpa only [LinearIsometryEquiv.norm_map] using hV.upper (L.symm y) (L.symm w)
end KLS
end FunctionalInequalities


