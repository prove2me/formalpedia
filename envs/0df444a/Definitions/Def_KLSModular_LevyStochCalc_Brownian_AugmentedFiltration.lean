-- Prove2me | Definitions.Def_KLSModular_LevyStochCalc_Brownian_AugmentedFiltration
-- name    : KLSModular_LevyStochCalc_Brownian_AugmentedFiltration
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T15:53:17.784432+00:00
-- url     : https://prove2.me/theorems/3cbf8b32-8c2c-4826-b624-2939bc0b44c4
-- title:
--   Null-set augmentation of a filtration
-- statement:
--   Vendored from the LevyStochCalc library at https://github.com/cgarryZA/LevyStochCalc, commit 984dbf0b790031eac05d56fe5a84b65e15e1e932. `augFiltration ℱ μ` is the filtration whose time-$t$ σ-algebra is `aug (ℱ (max t 0))` by the null sets of $\mu$, so times $t\le0$ use the time-zero σ-algebra. The embedded results identify its value at nonpositive times and show that augmenting a right-continuous filtration remains right-continuous.
--
--   **Original module imports**
--
--   ```lean
--   import LevyStochCalc.Brownian.Filtered
--   import LevyStochCalc.Probability.Augmentation
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
--       Filtration ℝ ‹MeasurableSpace Ω› where
--     seq t := aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ
--     mono' _ _ hst := aug_mono (ℱ.mono (max_le_max hst le_rfl))
--     le' _ := aug_le
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`LevyStochCalc/Brownian/Filtered`](https://prove2.me/theorems/52335393-0988-4f82-9dce-2d10225f9c3e), [`LevyStochCalc/Probability/Augmentation`](https://prove2.me/theorems/c62ac37e-942b-4c1f-b5ab-3e6e09a343ad).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/AugmentedFiltration.lean) · `LevyStochCalc.Brownian.AugmentedFiltration` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/AugmentedFiltration.lean#L51-L139 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.AugmentedFiltration`, definition bundle `KLSModular_LevyStochCalc_Brownian_AugmentedFiltration`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Filtered
import Definitions.Def_KLSModular_LevyStochCalc_Probability_Augmentation

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/AugmentedFiltration.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
namespace LevyStochCalc
namespace Brownian
open LevyStochCalc.Probability
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
/-- The filtration obtained by freezing `ℱ` before time `0` and augmenting each σ-algebra by
the `μ`-null sets. -/
def augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration ℝ ‹MeasurableSpace Ω› where
  seq t := aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ
  mono' _ _ hst := aug_mono (ℱ.mono (max_le_max hst le_rfl))
  le' _ := aug_le
theorem augFiltration_of_nonpos (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω)
    {t : ℝ} (ht : t ≤ 0) : augFiltration ℱ μ t = augFiltration ℱ μ 0 := by
  change aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ = aug (ℱ (max 0 0)) ‹MeasurableSpace Ω› μ
  rw [max_eq_right ht, max_self]
/-- Augmenting a right-continuous filtration keeps it right-continuous. -/
theorem rightCont_augFiltration_le (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    (augFiltration ℱ.rightCont μ).rightCont ≤ augFiltration ℱ.rightCont μ := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hs : t < t / 2 := by linarith
    have h1 : (augFiltration ℱ.rightCont μ).rightCont t
        ≤ augFiltration ℱ.rightCont μ (t / 2) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ hs
    rw [augFiltration_of_nonpos _ _ (by linarith : t / 2 ≤ 0)] at h1
    rw [augFiltration_of_nonpos _ _ ht.le]
    exact h1
  · have hseq : ∀ n : ℕ, t < t + ((n : ℝ) + 1)⁻¹ := by
      intro n
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    have hanti : Antitone fun n : ℕ => ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹) := by
      intro a b hab
      refine ℱ.rightCont.mono ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by gcongr
      linarith
    have h1 : (augFiltration ℱ.rightCont μ).rightCont t
        ≤ ⨅ n : ℕ, aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
      refine le_iInf fun n => ?_
      have h2 : (augFiltration ℱ.rightCont μ).rightCont t
          ≤ augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹) := by
        rw [Filtration.rightCont_eq]
        exact iInf₂_le _ (hseq n)
      have h3 : augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹)
          = aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
        change aug (ℱ.rightCont (max (t + ((n : ℝ) + 1)⁻¹) 0)) ‹MeasurableSpace Ω› μ = _
        rw [max_eq_left (by linarith [hseq n])]
      rwa [h3] at h2
    rw [aug_iInf_of_antitone hanti] at h1
    have h4 : (⨅ n : ℕ, ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ≤ ℱ.rightCont t := by
      rw [Filtration.rightCont_eq]
      refine le_iInf₂ fun u hu => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u - t by linarith)
      refine le_trans (iInf_le _ n) ?_
      rw [Filtration.rightCont_eq]
      refine iInf₂_le u ?_
      rw [one_div] at hn
      linarith
    have h5 : augFiltration ℱ.rightCont μ t = aug (ℱ.rightCont t) ‹MeasurableSpace Ω› μ := by
      change aug (ℱ.rightCont (max t 0)) ‹MeasurableSpace Ω› μ = _
      rw [max_eq_left ht]
    rw [h5]
    exact le_trans h1 (aug_mono h4)
instance isRightContinuous_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration.IsRightContinuous (augFiltration ℱ.rightCont μ) :=
  ⟨rightCont_augFiltration_le ℱ μ⟩
end Brownian
end LevyStochCalc


