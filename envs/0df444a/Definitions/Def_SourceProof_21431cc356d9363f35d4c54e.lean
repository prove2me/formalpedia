-- Prove2me | Definitions.Def_SourceProof_21431cc356d9363f35d4c54e
-- name    : SourceProof_21431cc356d9363f35d4c54e
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:29:14.048821+00:00
-- url     : https://prove2.me/theorems/0420981a-6a85-4c28-a278-02343480dc1c
-- title:
--   LevyStochCalc source module: SourceProof_21431cc356d9363f35d4c54e
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.energy_sub_ne_top` comes from the `LevyStochCalc.BSDEJ.PicardContractionBounds` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionNorm_F001
import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F000
import Definitions.Def_LevyStochCalc_BSDEJ_YoungLipschitz_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F001
import Definitions.Def_LevyStochCalc_Ito_StabilityEstimate_F002

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


theorem _root_.Prove2MeSourceProof.h_21431cc356d9363f35d4c54e {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂)) (h₁ : Brownian.Ito.energy P T H₁ ≠ ⊤)
    (h₂ : Brownian.Ito.energy P T H₂ ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) ≠ ⊤ := by
  have hA : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    hm₁.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hB : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    hm₂.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hA' : ∀ ω : Ω, Measurable fun s : ℝ => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    hA.comp (measurable_const.prodMk measurable_id)
  have hstep : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s)
      ≤ 2 * (LevyStochCalc.Brownian.Ito.energy P T H₁ + LevyStochCalc.Brownian.Ito.energy P T H₂) := by
    have hpt : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
      lintegral_mono fun ω => lintegral_mono fun s =>
        LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _
    refine hpt.trans (le_of_eq ?_)
    have hin : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume
        = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
      intro ω
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hA' ω)]
    have hoA : Measurable fun ω : Ω =>
        ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := hA.lintegral_prod_right'
    rw [lintegral_congr hin, lintegral_const_mul' _ _ (by norm_num),
      lintegral_add_left hoA]
    rfl
  exact ne_top_of_le_ne_top (by finiteness) hstep
end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

end Pointwise

section RealCore

end RealCore

end LevyStochCalc.BSDEJ.Solves


