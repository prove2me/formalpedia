-- Prove2me | Definitions.Def_SourceProof_272f7aebecefebc962a5704d
-- name    : SourceProof_272f7aebecefebc962a5704d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:02:22.927291+00:00
-- url     : https://prove2.me/theorems/fa41cd07-5c68-56ab-b996-0d38e8daefe9
-- title:
--   StochLean source theorem: MeasureTheory.Martingale.stoppedProcess_of_rightContinuous

import Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb
import Definitions.Def_SourceProof_bc31d4fc386dd41a31123691

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-!
# Stopping continuous-time martingales

The bounded optional-sampling theorem is transported to Mathlib's canonical
`WithTop`-valued stopping times. Splitting on the ordering of two stopping times
then gives the minimum formula. In particular a stopped martingale is a
martingale for the original filtration, not merely the stopped filtration.

Source: Protter I.17 and the corollary of I.18. The unrestricted UI conclusion
of I.18 additionally needs the unbounded optional-sampling theorem.
-/

@[expose] public section

open ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MeasureTheory.Martingale

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ} [IsFiniteMeasure P] [SigmaFiniteFiltration P F]

theorem _root_.Prove2MeSourceProof.h_272f7aebecefebc962a5704d (hX : Martingale X F P)
    (hr : ∀ ω, IsRightContinuousPath (X · ω))
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime F τ) :
    Martingale (stoppedProcess X τ) F P :=
  (_root_.Prove2MeSourceProof.h_bc31d4fc386dd41a31123691 hX)
    ((_root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb hX.stronglyAdapted) hr) (ae_of_all _ hr) hτ
end MeasureTheory.Martingale


