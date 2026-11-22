-- Prove2me | Definitions.Def_LevyStochCalc_Ito_CutoffPathAgreement_F000
-- name    : LevyStochCalc_Ito_CutoffPathAgreement_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T09:46:43.636985+00:00
-- url     : https://prove2.me/theorems/d868ecaa-ec7b-4658-b46c-9fa81e028a0a
-- title:
--   Source declarations: LevyStochCalc.Ito.CutoffPathAgreement
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.CutoffPathAgreement. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_AtomJumpRelation_F001
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaCutoffLocalise_F001
import Definitions.Def_LevyStochCalc_Probability_OpenExitTime_F000
import Definitions.Def_SourceProof_1a4af5ffbf7aaf4aaa194358

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Agreement of the continuous integrands with their cut-off, along a confined path

`JumpFormulaCutoff.integrands_cutoffFun₂_eq_of_mem` compares all five integrands of a state
function with those of its cut-off, and for the two jump integrands it needs the jump coefficient
itself bounded over the window, for every mark. That hypothesis is not available in general: the
jump coefficient is only square integrable against the intensity, so `x + γ(s, x, e)` leaves
every ball however large the cut-off radius.

The three *continuous* integrands need no such hypothesis. They are read at path values only, so
a path confined to a ball is enough. `integrands_cutoffFun₂_eq_of_boundedPath` records that,
adding the gradient, which the pathwise form of the jump part also reads at path values.

For the Brownian transfer the confinement has to come from a stopping time rather than an event,
so the same agreement is restated below `min (openExitTime …) T`: strictly below the exit time
the path is in the ball, and strictly below `T` the time cut-off is inactive. That is exactly the
hypothesis shape of `stochasticIntegralBrownian_congr_of_lt`.

## Main statements

* `integrands_cutoffFun₂_eq_of_boundedPath` — drift, diffusion, path value and gradient agree
  with their cut-off along a path confined to the ball, with no hypothesis on the jumps.
* `boundedPathSet_subset_le_openExitTime` — a path confined to the ball over the window has not
  exited by the end of it.
* `diffusionIntegrand_cutoffFun₂_eq_of_lt` — the agreement in the form the strict locality
  transfer consumes.
* `stochasticIntegralBrownian_cutoffFun₂_eq_of_le`, `multidimIntegral_cutoffFun₂_eq_of_mem` —
  the Brownian term of the cut-off and of the function itself agree almost surely on the event
  that the path has not left the ball, componentwise and in the vector form.
* `ae_continuousSide_cutoffFun₂_eq` — the whole continuous side, endpoints and drift integral
  included, agrees on that event.
* `norm_leftLimPathAt_le_of_boundedPath`,
  `gradient_cutoffFun₂_leftLim_eq_of_boundedPath` — a confined path has its left limits in the
  ball, where the gradient of the cut-off is that of the function.
* `cutoffFun₂_leftLim_eq_of_boundedPath`,
  `jumpIncrement_sub_eq_compensatorDrift_sub_of_boundedPath` — the cut-off changes the jump
  increment and the compensator-drift integrand by the same amount at the left limits.
* `jumpIncrement_cutoffFun₂_eq_of_boundedPath`,
  `ae_setIntegral_jumpIncrement_cutoffFun₂_eq`, `ae_setIntegral_jumpIncrement_sub_eq_zero` — the
  jump increment agrees with its cut-off at every atom of a window of finite intensity, because
  the state reached by the jump is a value of the path; hence the two integrals against the
  random measure agree and their difference integrates to zero.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Ito.JumpFormulaCutoff

universe u v

variable {Ω : Type u} {n d : ℕ} {E : Type v}

/-- **The continuous integrands agree with their cut-off along a path confined to the ball**, with
no hypothesis on the jump coefficient. The gradient is included: the pathwise form of the jump
part reads it at path values too. -/
theorem integrands_cutoffFun₂_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    JumpFormula.driftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs s (Xp s ω)
          = JumpFormula.driftIntegrand u coeffs s (Xp s ω)
      ∧ JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
          = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω)
      ∧ cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω) = u s (Xp s ω)
      ∧ JumpFormula.gradient (cutoffFun₂ u (2 * (m : ℝ))) s (Xp s ω)
          = JumpFormula.gradient u s (Xp s ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  have hsabs : |s| < 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hTm
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) := hb s hs
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  exact ⟨driftIntegrand_cutoffFun₂ u coeffs hR hsabs hx,
    diffusionIntegrand_cutoffFun₂ u coeffs.σ hR (le_of_lt hsabs) hx,
    cutoffFun₂_eq hR (le_of_lt hsabs) (le_of_lt hx),
    gradient_cutoffFun₂ u hR (le_of_lt hsabs) hx⟩
/-- **A path confined to the ball over the window has not exited by the end of it.** -/
theorem boundedPathSet_subset_le_openExitTime (Xp : ℝ → Ω → Fin n → ℝ) (T : ℝ) (m : ℕ) :
    Brownian.Ito.boundedPathSet Xp T m
      ⊆ {ω : Ω | ((T : ℝ) : WithTop ℝ)
          ≤ Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω} := by
  intro ω hω
  exact Probability.le_openExitTime_of_forall_norm_le fun s hs0 hsT => hω s ⟨hs0, hsT⟩
/-- **The diffusion integrand agrees with its cut-off strictly below the exit time**, in the
shape the strict locality transfer consumes. Strictly below the exit time the path is in the
ball; strictly below `T` the time cut-off is inactive. -/
theorem diffusionIntegrand_cutoffFun₂_eq_of_lt {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) (ω : Ω) (s : ℝ) (hs : 0 < s)
    (hlt : ((s : ℝ) : WithTop ℝ)
      < min (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω) ((T : ℝ) : WithTop ℝ)) :
    JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
      = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  obtain ⟨hltτ, hltT⟩ := lt_min_iff.mp hlt
  have hsT : s < T := by exact_mod_cast hltT
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) :=
    Probability.norm_le_of_lt_openExitTime hs.le hltτ
  have hsabs : |s| ≤ 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.le]
    exact le_of_lt (lt_trans hsT hTm)
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  exact diffusionIntegrand_cutoffFun₂ u coeffs.σ hR hsabs hx
section BrownianTransfer

open MeasureTheory
open LevyStochCalc.Ito.JumpFormula (diffusionIntegrand)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {E : Type v}

/-- **The Brownian term transfers between a state function and its cut-off** on the event that
the path has not left the ball. The two integrands agree strictly below the minimum of the exit
time and the horizon, and strict locality of the Itô integral turns that into almost sure
equality where the stopping time has not been reached. -/
theorem stochasticIntegralBrownian_cutoffFun₂_eq_of_le
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {Xp : ℝ → Ω → Fin n → ℝ} {coeffs : Setting.JumpDiffusionCoeffs n d E}
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) (hT : 0 < T)
    (hadapt : Adapted ℱ Xp)
    (hright : ∀ (ω : Ω) (s : ℝ),
      Filter.Tendsto (fun r => Xp r ω) (nhdsWithin s (Set.Ioi s)) (nhds (Xp s ω)))
    (j : Fin d)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j)
    (hq₁ : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j)
    (hq₂ : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ)
        ≤ Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω →
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j)
          hm₁ hp₁ hq₁ T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
            (fun ω s => diffusionIntegrand u coeffs.σ s (Xp s ω) j) hm₂ hp₂ hq₂ T ω := by
  classical
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hstopτ : IsStoppingTime ℱ
      (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ)) := by
    have h := Probability.isStoppingTime_openExitTime (ℱ := ℱ) (X := fun ω' s' => Xp s' ω')
      hadapt hright (m : ℝ)
    rwa [hrc] at h
  have hstop : IsStoppingTime ℱ
      (fun ω => min (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω)
        ((T : ℝ) : WithTop ℝ)) := hstopτ.min_const _
  have hagree : ∀ (ω : Ω) (s : ℝ), 0 < s →
      ((s : ℝ) : WithTop ℝ) < min (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω)
        ((T : ℝ) : WithTop ℝ) →
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j
        = diffusionIntegrand u coeffs.σ s (Xp s ω) j := by
    intro ω s hs hlt
    exact congrFun (diffusionIntegrand_cutoffFun₂_eq_of_lt u hm hTm ω s hs hlt) j
  have hmain := _root_.Prove2MeSourceProof.h_1a4af5ffbf7aaf4aaa194358 W ℱ hℱ
    hstop hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hagree hT
  filter_upwards [hmain] with ω hω hle
  exact hω (le_min hle le_rfl)
/-- **The multidimensional Brownian term transfers between a state function and its cut-off** on
the event that the path stays in the ball over the window. -/
theorem multidimIntegral_cutoffFun₂_eq_of_mem
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    {Xp : ℝ → Ω → Fin n → ℝ} {coeffs : Setting.JumpDiffusionCoeffs n d E}
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) (hT : 0 < T)
    (hadapt : Adapted ℱ Xp)
    (hright : ∀ (ω : Ω) (s : ℝ),
      Filter.Tendsto (fun r => Xp r ω) (nhdsWithin s (Set.Ioi s)) (nhds (Xp s ω)))
    (hm₁ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j))
    (hp₁ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j)
    (hq₁ : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : ∀ j : Fin d, Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j))
    (hp₂ : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j)
    (hq₂ : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
          (fun s ω => diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω))
          hm₁ hp₁ hq₁ T ω
        = LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => diffusionIntegrand u coeffs.σ s (Xp s ω)) hm₂ hp₂ hq₂ T ω := by
  have hcomp : ∀ j : Fin d, ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱW j)
          (fun ω s => diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j)
          (hm₁ j) (hp₁ j) (hq₁ j) T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W j) ℱ (hℱW j)
            (fun ω s => diffusionIntegrand u coeffs.σ s (Xp s ω) j)
            (hm₂ j) (hp₂ j) (hq₂ j) T ω := by
    intro j
    filter_upwards [stochasticIntegralBrownian_cutoffFun₂_eq_of_le (W.W j) ℱ (hℱW j) u hm hTm hT
      hadapt hright j (hm₁ j) (hp₁ j) (hq₁ j) (hm₂ j) (hp₂ j) (hq₂ j)] with ω hω hb
    exact hω (boundedPathSet_subset_le_openExitTime Xp T m hb)
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω hb
  simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral]
  exact Finset.sum_congr rfl fun j _ => hω j hb
end BrownianTransfer

open LevyStochCalc.Ito.JumpSplitting (leftLimPathAt tendsto_nhdsLT_leftLimPathAt jumpSumLeftAt
  ae_exists_atomEnum_jump_eq_gamma)

section JumpTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

end JumpTransfer

end LevyStochCalc.Ito.CutoffPath


