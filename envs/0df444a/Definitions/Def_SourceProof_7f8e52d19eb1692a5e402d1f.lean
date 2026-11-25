-- Prove2me | Definitions.Def_SourceProof_7f8e52d19eb1692a5e402d1f
-- name    : SourceProof_7f8e52d19eb1692a5e402d1f
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:56:57.468825+00:00
-- url     : https://prove2.me/theorems/d397ffd5-8c9b-5105-b431-6ccd29a2e6b1
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.uniformIntegrable_bounded_stoppedValue_of_usual

import Definitions.Def_SourceProof_0f93b663621787fcc9aa0ad4
import Definitions.Def_SourceProof_4a9b239e53ad8f8a45b491f1
import Definitions.Def_SourceProof_dd5d93162907f5e6520ec487
import Definitions.Def_SourceProof_e2b6e4c8b89a0b17690a85de

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

theorem _root_.Prove2MeSourceProof.h_7f8e52d19eb1692a5e402d1f {ι : Type*}
    (hX : Martingale X F P) (hu : UniformIntegrable X 1 P)
    (hF : F.IsUsual P) (hr : HasRightContinuousPaths X P)
    {τ : ι → Ω → WithTop ℝ≥0} (hτ : ∀ i, IsStoppingTime F (τ i))
    (hb : ∀ i, ∃ T : ℝ≥0, ∀ ω, τ i ω ≤ T) :
    UniformIntegrable (fun i ↦ stoppedValue X (τ i)) 1 P := by
  obtain ⟨Y, heq, hprog, hreg⟩ :=
    (_root_.Prove2MeSourceProof.h_dd5d93162907f5e6520ec487 hX.stronglyAdapted) hF hr
  exact ((_root_.Prove2MeSourceProof.h_e2b6e4c8b89a0b17690a85de (hX.congr hprog.stronglyAdapted (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq)))
    (hu.ae_eq (_root_.Prove2MeSourceProof.h_4a9b239e53ad8f8a45b491f1 heq)) hprog (ae_of_all _ hreg) hτ hb).ae_eq
      (fun i ↦ ((_root_.Prove2MeSourceProof.h_0f93b663621787fcc9aa0ad4 heq) (τ i)).symm)
end MeasureTheory.Martingale

namespace ProbabilityTheory.IsUIMartingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P]

end ProbabilityTheory.IsUIMartingale


