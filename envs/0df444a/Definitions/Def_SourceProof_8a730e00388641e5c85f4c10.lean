-- Prove2me | Definitions.Def_SourceProof_8a730e00388641e5c85f4c10
-- name    : SourceProof_8a730e00388641e5c85f4c10
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T08:22:49.253178+00:00
-- url     : https://prove2.me/theorems/6b08cf5c-0a44-4b79-a56e-f96e8f82871f
-- title:
--   LevyStochCalc source module: SourceProof_8a730e00388641e5c85f4c10
-- statement:
--   The original source theorem `LevyStochCalc.BSDEJ.Solves.driftLeg_sub_ae` comes from the `LevyStochCalc.BSDEJ.DriftLeg` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_BSDEJ_DriftLeg_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The drift leg of a Picard iterate

For a drift `b : Ω → ℝ → ℝ` of finite energy on the horizon `[0, T]` and vanishing off it, the
drift leg is the primitive `t ↦ ∫_{[0, t]} b ω s ds`, restricted to the sample points on which
`b ω` is integrable over `[0, T]` and set to `0` elsewhere. That restriction is a `P`-conull set,
so the drift leg is a version of the raw primitive, and on it every path is the primitive of a
globally integrable function, hence continuous.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.integrablePaths` — the sample points whose drift path is integrable
  over the horizon.
* `LevyStochCalc.BSDEJ.Solves.driftLeg` — the primitive of the drift, cut to those sample points.

## Main statements

* `driftLeg_ae_eq` — the drift leg is a version of the raw primitive.
* `setIntegral_Icc_eq_intervalIntegral` — the integral over `[0, t]` is the interval integral
  from `0` to `t`, for every real `t`.
* `continuous_driftLeg` — every path of the drift leg is continuous.
* `stronglyAdapted_driftLeg`, `adapted_driftLeg` — the drift leg is adapted to the filtration of
  the drift.
* `adapted_driftLeg_of_rightCont` — the drift leg is adapted to the filtration already when the
  drift is progressive for the right-continuous filtration.
* `measurable_uncurry_driftLeg` — the drift leg is jointly measurable in time and sample point.
* `driftLeg_sub_ae` — the drift leg at the horizon splits at an intermediate time.
* `lintegral_biSup_sq_driftLeg_lt_top` — the drift leg has finite `S²` seminorm.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### The paths on which the drift is integrable -/

/-! ### The drift leg -/


theorem _root_.Prove2MeSourceProof.h_8a730e00388641e5c85f4c10 (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    driftLeg b T T =ᵐ[P] fun ω => driftLeg b T t ω + ∫ s in Set.Icc t T, b ω s := by
  filter_upwards [LevyStochCalc.BSDEJ.Solves.ae_mem_integrablePaths hbm hbq] with ω hω
  have hI : IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume := hω
  have h1 : IntegrableOn (b ω) (Set.Icc (0 : ℝ) t) volume :=
    hI.mono_set (Set.Icc_subset_Icc le_rfl htT)
  have h2 : IntegrableOn (b ω) (Set.Ioc t T) volume :=
    hI.mono_set fun s hs => ⟨ht.trans hs.1.le, hs.2⟩
  have hdisj : Disjoint (Set.Icc (0 : ℝ) t) (Set.Ioc t T) :=
    (Set.Iic_disjoint_Ioi le_rfl).mono Set.Icc_subset_Iic_self Set.Ioc_subset_Ioi_self
  have hsplit : ∫ s in Set.Icc t T, b ω s = ∫ s in Set.Ioc t T, b ω s :=
    integral_Icc_eq_integral_Ioc
  rw [LevyStochCalc.BSDEJ.Solves.driftLeg_of_mem hω T, LevyStochCalc.BSDEJ.Solves.driftLeg_of_mem hω t, hsplit,
    ← Set.Icc_union_Ioc_eq_Icc ht htT, setIntegral_union hdisj measurableSet_Ioc h1 h2]
end LevyStochCalc.BSDEJ.Solves


