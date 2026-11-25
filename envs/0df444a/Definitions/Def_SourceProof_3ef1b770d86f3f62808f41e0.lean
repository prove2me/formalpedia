-- Prove2me | Definitions.Def_SourceProof_3ef1b770d86f3f62808f41e0
-- name    : SourceProof_3ef1b770d86f3f62808f41e0
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:17:49.290858+00:00
-- url     : https://prove2.me/theorems/eb9ae697-7dc2-4a18-8adb-6626f30c3af5
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.memLp_finiteStoppingTime_min

import Definitions.Def_SourceProof_29d33b95cf42be6716ddb60d

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Terminal Lp control on finite, unbounded stopping partitions

Stopping the integrator at `T` gives a conditional expectation of `X_T` in the sigma-field
at the original endpoint. The endpoint need not have a deterministic bound.
-/

@[expose] public section

open ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_3ef1b770d86f3f62808f41e0 (hX : Martingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    (τ : FiniteStoppingTime F) (T : ℝ≥0) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hXT : MemLp (X T) p P) : MemLp (fun ω ↦ X (min (τ ω) T) ω) p P :=
  (hXT.condExp (m := τ.measurableSpace) hp).ae_eq
    ((_root_.Prove2MeSourceProof.h_29d33b95cf42be6716ddb60d hX) hF hr τ T).symm
end MeasureTheory.Martingale


