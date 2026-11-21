-- Prove2me | Definitions.Def_LevyStochCalc_BSDEJ_PicardContractionBounds_F000
-- name    : LevyStochCalc_BSDEJ_PicardContractionBounds_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:27:00.934078+00:00
-- url     : https://prove2.me/theorems/27680d27-2bc5-41a7-be4f-878eb524853d
-- title:
--   Source declarations: LevyStochCalc.BSDEJ.PicardContractionBounds
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.BSDEJ.PicardContractionBounds. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
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

/-- A drift vanishing off a horizon on which it has finite energy is square integrable on every
horizon. -/
theorem drift_sq_int_global {b : Ω → ℝ → ℝ}
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (_root_.Prove2MeSourceProof.h_6afbd3f9a4aa317ea9c9ba3c hbz T') (lt_top_iff_ne_top.mpr hbq)
/-- The negative of a drift vanishing off a horizon of finite energy is square integrable on
every horizon. -/
theorem neg_drift_sq_int_global {b : Ω → ℝ → ℝ}
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖-b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  simpa only [nnnorm_neg] using drift_sq_int_global hbz hbq T'
/-- Freezing a process at the horizon does not change its energy there. -/
theorem energy_clampT {Y : ℝ → Ω → ℝ} :
    Brownian.Ito.energy P T (fun ω s => clampT T Y s ω)
      = Brownian.Ito.energy P T (fun ω s => Y s ω) :=
  lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    simp only [clampT_apply, min_eq_left hs.2]
end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

end Pointwise

section RealCore

end RealCore

end LevyStochCalc.BSDEJ.Solves


