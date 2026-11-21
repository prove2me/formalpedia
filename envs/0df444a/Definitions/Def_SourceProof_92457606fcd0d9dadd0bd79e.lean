-- Prove2me | Definitions.Def_SourceProof_92457606fcd0d9dadd0bd79e
-- name    : SourceProof_92457606fcd0d9dadd0bd79e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:16:59.987761+00:00
-- url     : https://prove2.me/theorems/3f4e2503-780c-45a3-ba53-24e14ca3a8cf
-- title:
--   LevyStochCalc source module: SourceProof_92457606fcd0d9dadd0bd79e
-- statement:
--   The original source theorem `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd` comes from the `LevyStochCalc.Ito.ItoFormulaShift` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoLocality_F001
import Definitions.Def_LevyStochCalc_Ito_ItoFormulaStopped_F000
import Definitions.Def_SourceProof_2631a3786acbcf68272d1d52
import Definitions.Def_SourceProof_92bec27d240f0e5702c6d539
import Definitions.Def_SourceProof_c9f8d91666f468ff1aabe966

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Itô's formula for a translated function

Translating the argument of a twice continuously differentiable function by a fixed vector
translates its Fréchet derivatives and its partial derivatives by the same vector, so Itô's
formula along a stopped path holds for the translate with every derivative read at the
translated path.

A weight that is known at a deterministic time and vanishes off the event that a stopping time
equals that time passes inside the Itô integral of an integrand that vanishes up to that
stopping time: the integrand is then carried by the window between that time and the horizon,
and the increment removed by the window is invisible on the event.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_shift` — Itô's formula along a stopped path for
  a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd` — a bounded weight known at
  a deterministic time, cut to the event that a stopping time equals it, passes inside the Itô
  integral of an integrand vanishing up to that stopping time.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd_stopped_sub` — the same for
  the increment of an integrand between two stopping times.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Translate

variable {n : ℕ}

end Translate

section ShiftedFormula

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

end ShiftedFormula

section StoppedIncrement

variable {Ω : Type u}

end StoppedIncrement

section HitIndPullOut

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in

theorem _root_.Prove2MeSourceProof.h_92457606fcd0d9dadd0bd79e
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    {D : Ω → ℝ → ℝ} (hmD : Measurable (Function.uncurry D))
    (hpD : Probability.ProgressivelyMeasurable ℱ D)
    (hqD : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hD0 : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ σ ω → D ω s = 0)
    (hwm : Measurable (Function.uncurry fun ω s => hitInd σ a ω * V ω * D ω s))
    (hwp : Probability.ProgressivelyMeasurable ℱ fun ω s => hitInd σ a ω * V ω * D ω s)
    (hwq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖hitInd σ a ω * V ω * D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    (fun ω => hitInd σ a ω * V ω
        * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD T ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω * D ω s) hwm hwp hwq T := by
  classical
  have hT : (0 : ℝ) < T := lt_of_le_of_lt ha haT
  obtain ⟨M, hM⟩ := hVb
  have hwbdd : ∀ ω, |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω| ≤ M := by
    intro ω
    calc |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω| = |LevyStochCalc.Brownian.Ito.hitInd σ a ω| * |V ω| := abs_mul _ _
      _ ≤ 1 * |V ω| := mul_le_mul_of_nonneg_right (LevyStochCalc.Brownian.Ito.abs_hitInd_le_one σ a ω) (abs_nonneg _)
      _ = |V ω| := one_mul _
      _ ≤ M := hM ω
  have hwmeas : Measurable fun ω => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω := (LevyStochCalc.Brownian.Ito.measurable_hitInd σ hσ a).mul hVm
  have hwsm : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) fun ω => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω :=
    (LevyStochCalc.Brownian.Ito.stronglyMeasurable_hitInd σ hσ a).mul hVa
  -- where the weight does not vanish the integrand is carried by the window `(a, T]`
  have hkeypt : ∀ (ω : Ω) (s : ℝ),
      LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s
        = LevyStochCalc.Brownian.Ito.indIoc Ω 0 T ω s * (LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) := by
    intro ω s
    by_cases hev : σ ω = ((a : ℝ) : WithTop ℝ)
    · by_cases hsa : a < s
      · have hIeq : LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s = LevyStochCalc.Brownian.Ito.indIoc Ω 0 T ω s := by
          by_cases hsT : s ≤ T
          · have h1 : s ∈ Set.Ioc a T := ⟨hsa, hsT⟩
            have h2 : s ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_lt ha hsa, hsT⟩
            simp only [LevyStochCalc.Brownian.Ito.indIoc, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          · have h1 : s ∉ Set.Ioc a T := fun hm => hsT hm.2
            have h2 : s ∉ Set.Ioc (0 : ℝ) T := fun hm => hsT hm.2
            simp only [LevyStochCalc.Brownian.Ito.indIoc, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
        rw [hIeq]; ring
      · rw [not_lt] at hsa
        have hind : LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s = 0 := by
          have hm : s ∉ Set.Ioc a T := fun hm => absurd hm.1 (not_lt.mpr hsa)
          simp only [LevyStochCalc.Brownian.Ito.indIoc, Set.indicator_of_notMem hm]
        by_cases hs0 : 0 < s
        · have hD : D ω s = 0 := by
            refine hD0 ω s hs0 ?_
            rw [hev]
            exact_mod_cast hsa
          rw [hind, hD]; ring
        · rw [not_lt] at hs0
          have hind0 : LevyStochCalc.Brownian.Ito.indIoc Ω 0 T ω s = 0 := by
            have hm : s ∉ Set.Ioc (0 : ℝ) T := fun hm => absurd hm.1 (not_lt.mpr hs0)
            simp only [LevyStochCalc.Brownian.Ito.indIoc, Set.indicator_of_notMem hm]
          rw [hind, hind0]; ring
    · have hh : LevyStochCalc.Brownian.Ito.hitInd σ a ω = 0 := by
        simp [LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_notMem
          (show ω ∉ {ω | σ ω = ((a : ℝ) : WithTop ℝ)} from hev)]
      rw [hh]; ring
  have hkey : (fun (ω : Ω) (s : ℝ) => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s)
      = LevyStochCalc.Brownian.Ito.indTerm (fun ω s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) 0 T := by
    funext ω s
    exact hkeypt ω s
  have habs : ∀ (ω : Ω) (s : ℝ),
      |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s| ≤ |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s| := by
    intro ω s
    calc |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s|
        = |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω| * |LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s| * |D ω s| := by rw [abs_mul, abs_mul]
      _ ≤ |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω| * 1 * |D ω s| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (LevyStochCalc.Brownian.Ito.indIoc_le_one a T ω s) (abs_nonneg _)) (abs_nonneg _)
      _ = |LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s| := by rw [mul_one, ← abs_mul]
  have hindm : Measurable fun p : Ω × ℝ => LevyStochCalc.Brownian.Ito.indIoc Ω a T p.1 p.2 := by
    simp only [LevyStochCalc.Brownian.Ito.indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  have hiM : Measurable (Function.uncurry fun (ω : Ω) s => LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s) :=
    LevyStochCalc.Brownian.Ito.measurable_indTerm hmD a T
  have hiP : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (fun (ω : Ω) s => LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s) :=
    LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hpD ha haT
  have hiQ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := D) a T ω s) hqD
  have hcm : Measurable (Function.uncurry
      fun (ω : Ω) s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s) :=
    ((hwmeas.comp measurable_fst).mul hindm).mul hmD
  have hcp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (fun (ω : Ω) s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s) :=
    (_root_.Prove2MeSourceProof.h_a85377d9ae43b1c0795fd7b5 ℱ ha haT ⟨M, hwbdd⟩ hwmeas hwsm).mul hpD
  have hcq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P) habs hwq
  have hzm : Measurable (Function.uncurry
      (LevyStochCalc.Brownian.Ito.indTerm (fun (ω : Ω) s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) 0 T)) :=
    LevyStochCalc.Brownian.Ito.measurable_indTerm hwm 0 T
  have hzp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      (LevyStochCalc.Brownian.Ito.indTerm (fun (ω : Ω) s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) 0 T) :=
    LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indTerm ℱ hwp (le_refl (0 : ℝ)) hT
  have hzq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖LevyStochCalc.Brownian.Ito.indTerm (fun (ω : Ω) s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) 0 T ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.energy_lt_top_of_abs_le (P := P)
      (fun ω s => LevyStochCalc.Brownian.Ito.abs_indTerm_le (H := fun ω s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) 0 T ω s) hwq
  have hpull := _root_.Prove2MeSourceProof.h_92bec27d240f0e5702c6d539 W ℱ hℱ ha haT
    (V := fun ω => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω) ⟨M, hwbdd⟩ hwmeas hwsm D hmD hpD hqD
    hiM hiP hiQ hcm hcp hcq hT
  have hloc := _root_.Prove2MeSourceProof.h_371bbffaec7b2a5d68568212 W ℱ hℱ D hmD hpD hqD ha haT
    hiM hiP hiQ hT
  have hstep := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indTerm_zero W ℱ hℱ hT hwm hwp hwq hzm hzp hzq
  have hcongr := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun W ℱ hℱ hkey hcm hcp hcq hzm hzp hzq T
  -- the increment removed by the window is invisible where the stopping time equals `a`
  have hzero : ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.hitInd σ a ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω = 0 := by
    rcases eq_or_lt_of_le ha with hA | hA
    · have hz := _root_.Prove2MeSourceProof.h_39285c9e8cb91346b858af97 W ℱ hℱ D hmD hpD hqD
        (le_of_eq hA.symm)
      filter_upwards [hz] with ω hω
      have hval : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω = 0 := hω
      rw [hval, mul_zero]
    · have hz0m : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) :=
        measurable_const
      have hz0p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) :=
        LevyStochCalc.Probability.progressivelyMeasurable_zero ℱ
      have hz0q : ∀ t, 0 < t → ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) t,
          (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
        intro t _
        simp
      have hcl := _root_.Prove2MeSourceProof.h_c9f8d91666f468ff1aabe966 σ W ℱ hℱ hσ hmD hpD hqD
        hz0m hz0p hz0q (fun ω s hs hsσ => hD0 ω s hs hsσ) hA
      have hzz := _root_.Prove2MeSourceProof.h_2631a3786acbcf68272d1d52 W ℱ hℱ hz0m hz0p hz0q a
      filter_upwards [hcl, hzz] with ω h1 h2
      by_cases hev : σ ω = ((a : ℝ) : WithTop ℝ)
      · have hle : ((a : ℝ) : WithTop ℝ) ≤ σ ω := le_of_eq hev.symm
        have hval : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
            (fun _ _ => (0 : ℝ)) hz0m hz0p hz0q a ω = 0 := h2
        rw [h1 hle, hval, mul_zero]
      · have hh : LevyStochCalc.Brownian.Ito.hitInd σ a ω = 0 := by
          simp [LevyStochCalc.Brownian.Ito.hitInd, Set.indicator_of_notMem
            (show ω ∉ {ω | σ ω = ((a : ℝ) : WithTop ℝ)} from hev)]
        rw [hh, zero_mul]
  filter_upwards [hpull, hloc, hstep, hzero] with ω h1 h2 h3 h4
  show LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD T ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) hwm hwp hwq T ω
  have h1' : LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s) hiM hiP hiQ T ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s) hcm hcp hcq T ω := h1
  have h2' : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => LevyStochCalc.Brownian.Ito.indIoc Ω a T ω s * D ω s) hiM hiP hiQ T ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD (min T T) ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD (min a T) ω := h2
  have h3' : LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
      (LevyStochCalc.Brownian.Ito.indTerm (fun ω s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) 0 T) hzm hzp hzq T ω
      = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * D ω s) hwm hwp hwq T ω := h3
  have hprod : LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω
      * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω = 0 := by
    calc LevyStochCalc.Brownian.Ito.hitInd σ a ω * V ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω
        = V ω * (LevyStochCalc.Brownian.Ito.hitInd σ a ω * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω) := by
          ring
      _ = 0 := by rw [h4, mul_zero]
  rw [← h3', ← congrFun hcongr ω, ← h1', h2', min_self, min_eq_left haT.le]
  linear_combination hprod
end HitIndPullOut

end LevyStochCalc.Brownian.Ito


