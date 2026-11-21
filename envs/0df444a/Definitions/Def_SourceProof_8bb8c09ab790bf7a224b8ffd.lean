-- Prove2me | Definitions.Def_SourceProof_8bb8c09ab790bf7a224b8ffd
-- name    : SourceProof_8bb8c09ab790bf7a224b8ffd
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:54.062448+00:00
-- url     : https://prove2.me/theorems/82bbc885-e17e-4742-8ae6-c8ef6bd56136
-- title:
--   LevyStochCalc source module: SourceProof_8bb8c09ab790bf7a224b8ffd
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.energy_le_of_biSup` comes from the `LevyStochCalc.BSDEJ.PicardContractionBounds` module. The staged Lean declaration includes its source proof and dependency references.
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


theorem _root_.Prove2MeSourceProof.h_8bb8c09ab790bf7a224b8ffd {Y : ℝ → Ω → ℝ} :
    Brownian.Ito.energy P T (fun ω s => Y s ω)
      ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  have hb : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T,
          (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) s hs
  refine hb.trans ?_
  rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  exact le_of_eq (mul_comm _ _)
end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

end Pointwise

section RealCore

end RealCore

end LevyStochCalc.BSDEJ.Solves


