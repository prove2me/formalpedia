-- Prove2me | Definitions.Def_LevyStochCalc_Ito_VectorItoProcessDiff_F000
-- name    : LevyStochCalc_Ito_VectorItoProcessDiff_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T21:58:08.366289+00:00
-- url     : https://prove2.me/theorems/bd7e3bd3-1848-4bb7-894b-3f1bcd1789c0
-- title:
--   Source declarations: LevyStochCalc.Ito.VectorItoProcessDiff
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.VectorItoProcessDiff. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Brownian_ItoTruncate_F000
import Definitions.Def_LevyStochCalc_Brownian_ItoTruncate_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputModification_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputMoments_F003
import Definitions.Def_LevyStochCalc_Ito_PicardOutputStepDiff_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F000
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F001
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F002
import Definitions.Def_LevyStochCalc_Ito_PicardOutputWeighting_F003

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The `L²` distance between two vector Itô processes

Two vector Itô processes with the same initial value differ by the time integral of the difference
of their drifts and the Itô integral of the difference of their diffusion matrices. Cauchy–Schwarz
bounds the first in `L²` by the energy of the drift difference and the Itô isometry identifies the
second with the energy of the diffusion difference.

The file sits in the `Ito` layer only because the Cauchy–Schwarz bound
`LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le` lives there; nothing here depends on the
Picard construction itself.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_norm_vectorItoProcess_sub_le` — the bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Diff

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

omit [IsProbabilityMeasure P] in
/-- A path with finite energy on a window is integrable there, almost surely. -/
theorem ae_integrableOn_of_energy_lt_top {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) {t : ℝ}
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn (b ω) (Set.Icc (0 : ℝ) t) volume := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity hbm t) hbq.ne] with ω hω
  exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
    (Measurable.of_uncurry_left hbm) hω).integrable (by norm_num)
end Diff

end LevyStochCalc.Brownian.Ito


