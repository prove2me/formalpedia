-- Prove2me | Definitions.Def_SourceProof_8dd2bd144165bcf825664aac
-- name    : SourceProof_8dd2bd144165bcf825664aac
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:12.561844+00:00
-- url     : https://prove2.me/theorems/b43e4a5c-e765-4354-9c96-ca80edcdc071
-- title:
--   LevyStochCalc source module: SourceProof_8dd2bd144165bcf825664aac
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.ae_two_mul_integral_mul_sub_le` comes from the `LevyStochCalc.BSDEJ.PicardContractionBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F002
import Definitions.Def_SourceProof_1ef3cd2b70d61f5d3e313bb1

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Energy and pointwise bounds behind the Picard contraction

The energy of a process on a horizon is at most the length of the horizon times its `S²`
seminorm, the energy of a difference of two processes is finite when both energies are, and
freezing a process at the horizon leaves its energy there unchanged. At almost every time of the
horizon, twice the pairing of a process against the difference of two evaluations of a Lipschitz
generator is at most `β / 2` times the second moment of the process plus `6 L² / β` times the
sample energy density of the differenced arguments, and the real-variable core turns a weighted
energy dominated by such a pairing into a contraction by the factor `6 L² / β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}

end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}


theorem _root_.Prove2MeSourceProof.h_8dd2bd144165bcf825664aac
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hβ : 0 < β) {X : ℝ → Ω → ℝ} {b₁ b₂ : Ω → ℝ → ℝ}
    {Y'₁ Y'₂ : ℝ → Ω → ℝ} {Z'₁ Z'₂ : ℝ → Ω → (Fin d → ℝ)} {U'₁ U'₂ : ℝ → Ω → E → ℝ}
    {ΔY : ℝ → Ω → ℝ} {ΔZ : ℝ → Ω → (Fin d → ℝ)} {ΔU : ℝ → Ω → E → ℝ}
    (hΔY : ∀ s ω, ΔY s ω = Y'₁ s ω - Y'₂ s ω)
    (hΔZ : ∀ s ω j, ΔZ s ω j = Z'₁ s ω j - Z'₂ s ω j)
    (hΔU : ∀ s ω e, ΔU s ω e = U'₁ s ω e - U'₂ s ω e)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁m : Measurable (Function.uncurry b₁)) (hb₂m : Measurable (Function.uncurry b₂))
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ ω s - b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    (hΔYm : Measurable (Function.uncurry fun ω s => ΔY s ω))
    (hΔZm : ∀ j, Measurable (Function.uncurry fun ω s => ΔZ s ω j))
    (hΔUm : Measurable fun p : Ω × ℝ × E => ΔU p.2.1 p.1 p.2.2)
    (hin : wNorm P ν β T ΔY ΔZ ΔU ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      2 * ∫ ω, X s ω * (b₁ ω s - b₂ ω s) ∂P
        ≤ β / 2 * (∫ ω, X s ω * X s ω ∂P)
          + 6 * L ^ 2 / β * (∫⁻ ω, density ν ΔY ΔZ ΔU ω s ∂P).toReal := by
  classical
  have hg₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      b₁ ω s = f s (Y'₁ s ω) (Z'₁ s ω) (U'₁ s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc (0 : ℝ) T))
        (ν := P)).quasiMeasurePreserving.ae hb₁)
  have hg₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      b₂ ω s = f s (Y'₂ s ω) (Z'₂ s ω) (U'₂ s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc (0 : ℝ) T))
        (ν := P)).quasiMeasurePreserving.ae hb₂)
  have hdens := LevyStochCalc.BSDEJ.Solves.ae_lintegral_density_ne_top hβ.le hΔYm hΔZm hΔUm hin
  have hX2 := LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => X s ω) hXm hXq
  have hb2 := LevyStochCalc.Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b₁ ω s - b₂ ω s)
    (hb₁m.sub hb₂m) hbq
  filter_upwards [hg₁, hg₂, hdens, hX2, hb2] with s hs₁ hs₂ hdf hXs hbs
  have hdm := LevyStochCalc.BSDEJ.Solves.measurable_density_slice (ν := ν) hΔYm hΔZm hΔUm s
  have hdω := ae_lt_top hdm hdf
  have hJ : ∀ᵐ ω ∂P, (∫⁻ e, (‖ΔU s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ≠ ⊤ := by
    filter_upwards [hdω] with ω hω
    simp only [LevyStochCalc.BSDEJ.Solves.density] at hω
    exact (ENNReal.add_ne_top.mp hω.ne).2
  have hptw : ∀ᵐ ω ∂P, 2 * (X s ω * (b₁ ω s - b₂ ω s))
      ≤ β / 2 * (X s ω * X s ω) + 6 * L ^ 2 / β * (LevyStochCalc.BSDEJ.Solves.density ν ΔY ΔZ ΔU ω s).toReal := by
    filter_upwards [hs₁, hs₂, hJ] with ω h1 h2 hJω
    have hueq : (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        = ∫⁻ e, (‖ΔU s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
      lintegral_congr fun e => by rw [hΔU s ω e]
    have hu : (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ≠ ⊤ := by
      rw [hueq]; exact hJω
    have key := _root_.Prove2MeSourceProof.h_8af671222c86fdea87a26691 hβ hL hlip s (Y'₁ s ω) (Y'₂ s ω)
      (Z'₁ s ω) (Z'₂ s ω) (U'₁ s ω) (U'₂ s ω) hu (X s ω)
    have hsq2 : X s ω ^ 2 = X s ω * X s ω := pow_two _
    have hdens_eq : (LevyStochCalc.BSDEJ.Solves.density ν ΔY ΔZ ΔU ω s).toReal
        = (Y'₁ s ω - Y'₂ s ω) ^ 2 + (∑ j, (Z'₁ s ω j - Z'₂ s ω j) ^ 2)
          + (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal := by
      rw [_root_.Prove2MeSourceProof.h_1ef3cd2b70d61f5d3e313bb1 hJω]
      simp only [hΔY, hΔZ, hΔU]
    rw [h1, h2, hdens_eq]
    linarith [key]
  have hint1 : Integrable (fun ω => 2 * (X s ω * (b₁ ω s - b₂ ω s))) P :=
    (hXs.integrable_mul hbs).const_mul 2
  have hintA : Integrable (fun ω => β / 2 * (X s ω * X s ω)) P :=
    (hXs.integrable_mul hXs).const_mul _
  have hintB : Integrable
      (fun ω => 6 * L ^ 2 / β * (LevyStochCalc.BSDEJ.Solves.density ν ΔY ΔZ ΔU ω s).toReal) P :=
    (integrable_toReal_of_lintegral_ne_top hdm.aemeasurable hdf).const_mul _
  have hmono := integral_mono_ae hint1 (hintA.add hintB) hptw
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul, integral_add hintA hintB, integral_const_mul, integral_const_mul,
    integral_toReal hdm.aemeasurable hdω] at hmono
  exact hmono
end Pointwise

section RealCore

end RealCore

end LevyStochCalc.BSDEJ.Solves


