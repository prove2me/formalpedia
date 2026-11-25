-- Prove2me | Definitions.Def_SourceProof_f1d6b3dcfada66cafb4e9e50
-- name    : SourceProof_f1d6b3dcfada66cafb4e9e50
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:14:49.685108+00:00
-- url     : https://prove2.me/theorems/d154006a-7afa-5bb7-b808-e8f4e5c0c66e
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.memLp_stochasticIntegral_of_bounded

import Definitions.Def_SourceProof_1d0048e633cc05b9ad20d527
import Definitions.Def_SourceProof_a306c42680d425170aa442b0

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The bounded-integrand step of Protter II.20

Bounded simple approximation, the source second-moment estimate and actual
uniform-integrability limits give the finite-time L2 martingale result. Neither
the integrator nor the integral is centered by discarding its initial value.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} [SigmaFiniteFiltration P F] {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_f1d6b3dcfada66cafb4e9e50
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hM : Martingale X F P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) (C : ℝ≥0)
    (hb : ∀ᵐ ω ∂P, ∀ t, ‖H t ω‖ ≤ C) (t : ℝ≥0) (hXt : MemLp (X t) 2 P) :
    MemLp (hX.stochasticIntegral hF ha hr t) 2 P :=
  ⟨(((_root_.Prove2MeSourceProof.h_a306c42680d425170aa442b0 hX) hF ha hr t).mono (F.le t) le_rfl).aestronglyMeasurable,
    ((_root_.Prove2MeSourceProof.h_1d0048e633cc05b9ad20d527 hX) hF hM ha hr C hb t hXt).trans_lt
      (ENNReal.mul_lt_top (by simp) hXt.eLpNorm_lt_top)⟩
end IsSemimartingale

end ProbabilityTheory


