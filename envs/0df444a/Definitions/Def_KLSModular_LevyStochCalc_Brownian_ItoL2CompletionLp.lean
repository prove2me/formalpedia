-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoL2CompletionLp
-- name    : KLSModular_LevyStochCalc_Brownian_ItoL2CompletionLp
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:02:34.466031+00:00
-- url     : https://prove2.me/theorems/4aa3ab04-3958-47e7-870f-6b1a325ace99
-- title:
--   Finite L² energy of simple Brownian integrals
-- statement:
--   Vendored from the LevyStochCalc library (https://github.com/cgarryZA/LevyStochCalc), commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. For an adapted `SimplePredictable` integrand $H$ on a positive horizon $T$, `simpleIntegral_lintegral_sq_finite_brownian` states that the squared $\operatorname{ENNReal}$ norm of `simpleIntegral W H T` has finite integral under the probability measure $P$. Thus the simple Brownian integral has finite $L^2(P)$ energy, as required for its representation in `Lp ℝ 2 P`; the statement itself is a finiteness result rather than the construction of the completed integral.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.SimplePredictableRefine
--   import LevyStochCalc.Brownian.ItoSimple
--   import LevyStochCalc.Brownian.ItoDensity
--   import LevyStochCalc.Brownian.ItoMartingale
--   import LevyStochCalc.Martingale.RightCont
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context. Body omitted.
--
--   ```lean
--   lemma simpleIntegral_lintegral_sq_finite_brownian
--       {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
--       (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
--       {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
--       (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (H.partition i.castSucc)) (H.ξ i)) :
--       ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/SimplePredictableRefine`](https://prove2.me/theorems/df771526-b015-4850-8804-524a0e6f5ac6), [`LevyStochCalc/Brownian/ItoSimple`](https://prove2.me/theorems/795b2ad2-44ee-43f5-a5ba-483135ae893d), [`LevyStochCalc/Brownian/ItoDensity`](https://prove2.me/theorems/bfa7a398-2539-4893-bbe5-a70374f778e6), [`LevyStochCalc/Brownian/ItoMartingale`](https://prove2.me/theorems/f0202799-20af-43f1-8b7b-67dc31dc1c8a), [`LevyStochCalc/Martingale/RightCont`](https://prove2.me/theorems/1a3effa5-63bb-4538-8241-62c61dd09b94).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoL2CompletionLp.lean) · `LevyStochCalc.Brownian.ItoL2CompletionLp` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoL2CompletionLp.lean#L30-L69 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoL2CompletionLp`, definition bundle `KLSModular_LevyStochCalc_Brownian_ItoL2CompletionLp`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_SimplePredictableRefine
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoSimple
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoDensity
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoMartingale
import Definitions.Def_KLSModular_LevyStochCalc_Martingale_RightCont

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoL2CompletionLp.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
namespace LevyStochCalc
namespace Brownian
namespace Ito
open MeasureTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- **C0b.10-pre1: `simpleIntegral` has finite `L²(P)` norm.** For any
adapted `SimplePredictable`, the squared `lintegral` of the integral
against `P` is finite. Direct from `simpleIntegral_isometry` (giving
`= ∫⁻ ω ∫⁻ s ‖H.eval s ω‖²`) plus `lintegral_eval_sq_outer` (giving
`= ∑_i Δt_i · ∫⁻ ω ‖H.ξ i ω‖²`), each summand bounded by
`Δt_i · M_i² ≤ T · M_i² < ∞` via `ξ_bounded`.

This is the boundedness fact needed to lift `simpleIntegral W H T` to
an element of `Lp ℝ 2 P` for the `L²` extension in `C0b.10`. -/
lemma simpleIntegral_lintegral_sq_finite_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [simpleIntegral_isometry W ℱ hℱ hT H h_adapt]
  rw [lintegral_eval_sq_outer H]
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_M_nn : 0 ≤ max M 0 := le_max_right _ _
  have h_bound : ∀ ω, |H.ξ i ω| ≤ max M 0 :=
    fun ω => le_trans (hM ω) (le_max_left _ _)
  have h_norm_le : ∀ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (max M 0) := by
    intro ω
    rw [show (‖H.ξ i ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.ξ i ω‖
          from (ofReal_norm _).symm]
    exact ENNReal.ofReal_le_ofReal
      (Real.norm_eq_abs _ ▸ h_bound ω)
  calc ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ _ω, (ENNReal.ofReal (max M 0)) ^ 2 ∂P := by
        refine MeasureTheory.lintegral_mono (fun ω => ?_)
        exact pow_le_pow_left' (h_norm_le ω) 2
    _ = (ENNReal.ofReal (max M 0)) ^ 2 * P Set.univ := by
        rw [MeasureTheory.lintegral_const]
    _ < ⊤ := by
        rw [MeasureTheory.measure_univ, mul_one]
        exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
end Ito
end Brownian
end LevyStochCalc


