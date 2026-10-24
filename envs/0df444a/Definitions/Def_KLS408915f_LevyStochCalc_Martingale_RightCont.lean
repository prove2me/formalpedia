-- Prove2me | Definitions.Def_KLS408915f_LevyStochCalc_Martingale_RightCont
-- name    : KLS408915f_LevyStochCalc_Martingale_RightCont
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-23T08:16:08.313034+00:00
-- url     : https://prove2.me/theorems/fbd10fc3-dc52-4887-93a0-49db63f9a669
-- title:
--   Martingales under right-continuous filtration augmentation
-- statement:
--   Vendored from LevyStochCalc, repository https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. The theorem `martingale_rightCont_of_tendsto_eLpNorm_one` states that if F is a real-valued `Martingale F ℱ P` and, for every s ∈ ℝ, the eLpNorm with exponent 1 of F r − F s tends to 0 as r approaches s from the right, then F is a martingale for the right-continuous filtration `ℱ.rightCont`. The probability measure P and the filtration ℱ are part of the hypotheses.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Martingale/RightCont.lean#L25-L56 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Martingale.RightCont`, definition bundle `KLS408915f_LevyStochCalc_Martingale_RightCont`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.Probability.Martingale.Basic

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Martingale/RightCont.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory Filter Topology
namespace LevyStochCalc
namespace Martingale
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {F : ℝ → Ω → ℝ}
/-- An `ℱ`-martingale on `ℝ` whose time slices are right-continuous in `L¹` is a martingale
on the right-continuous augmentation of `ℱ`. -/
lemma martingale_rightCont_of_tendsto_eLpNorm_one (hmart : Martingale F ℱ P)
    (hrc : ∀ s : ℝ, Tendsto (fun r => eLpNorm (F r - F s) 1 P) (𝓝[>] s) (𝓝 0)) :
    Martingale F ℱ.rightCont P := by
  refine ⟨fun i => (hmart.stronglyAdapted i).mono (ℱ.le_rightCont i), ?_⟩
  intro s t hst
  have hm : ℱ.rightCont s ≤ mΩ := (ℱ.rightCont).le s
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm
    (hmart.integrable t) (fun A _ _ => (hmart.integrable s).integrableOn)
    ?_ ((hmart.stronglyAdapted s).mono (ℱ.le_rightCont s)).aestronglyMeasurable).symm
  intro A hA _
  -- `s = t` is trivial; for `s < t` use the constant-near-`s`/limit argument.
  rcases eq_or_lt_of_le hst with rfl | hst'
  · rfl
  -- `r ↦ ∫_A F r → ∫_A F s` from right-`L¹`-continuity.
  have htend_s : Tendsto (fun r => ∫ x in A, F r x ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds (∫ x in A, F s x ∂P)) :=
    tendsto_setIntegral_of_L1' (F s) (hmart.integrable s).aestronglyMeasurable
      (Eventually.of_forall (fun r => hmart.integrable r)) (hrc s) A
  -- `r ↦ ∫_A F r` is constantly `∫_A F t` on `(s, t)`.
  have heq_ev : ∀ᶠ r in nhdsWithin s (Set.Ioi s),
      (∫ x in A, F t x ∂P) = ∫ x in A, F r x ∂P := by
    refine eventually_of_mem (Ioo_mem_nhdsGT hst') (fun r hr => ?_)
    have h_le : ℱ.rightCont s ≤ ℱ r := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le r hr.1
    exact (hmart.setIntegral_eq (le_of_lt hr.2) (h_le A hA)).symm
  have htend_const : Tendsto (fun r => ∫ x in A, F r x ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds (∫ x in A, F t x ∂P)) :=
    tendsto_const_nhds.congr' heq_ev
  exact tendsto_nhds_unique htend_s htend_const
end Martingale
end LevyStochCalc


