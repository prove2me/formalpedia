-- Prove2me | Definitions.Def_SourceProof_aa372c8273bcd3cd6307f406
-- name    : SourceProof_aa372c8273bcd3cd6307f406
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:12:14.869952+00:00
-- url     : https://prove2.me/theorems/75aa0b80-8c1f-5850-99ac-93a8b092962c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsUIMartingale.stoppedProcess_of_usual

import Definitions.Def_SourceProof_3b6770fe33c80a2ec52a585f
import Definitions.Def_SourceProof_7f8e52d19eb1692a5e402d1f

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Uniform integrability under continuous-time stopping

Every bounded stopping value of a closed martingale is a conditional
expectation of its closing variable. Their union over all finite bounds is
therefore UI. Taking AE limits gives the same result for arbitrary families
of AE-finite stopping times. In particular Protter I.18 follows without
assigning an artificial terminal value on the event that a stopping time is
infinite: all coordinates of a stopped process are evaluated at finite times.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

end MeasureTheory.Martingale

namespace ProbabilityTheory.IsUIMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]


theorem _root_.Prove2MeSourceProof.h_aa372c8273bcd3cd6307f406 (hX : IsUIMartingale X F P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    IsUIMartingale (MeasureTheory.stoppedProcess X τ) F P :=
  ⟨(_root_.Prove2MeSourceProof.h_3b6770fe33c80a2ec52a585f hX.1) hF hr hτ,
    (_root_.Prove2MeSourceProof.h_7f8e52d19eb1692a5e402d1f hX.1) hX.2 hF hr
      (fun t : ℝ≥0 ↦ (isStoppingTime_const F t).min hτ)
      (fun t ↦ ⟨t, fun _ ↦ min_le_left _ _⟩)⟩
end ProbabilityTheory.IsUIMartingale


