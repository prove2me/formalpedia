-- Prove2me | Definitions.Def_SourceProof_47f4915fac265caea9ceaccb
-- name    : SourceProof_47f4915fac265caea9ceaccb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:27:47.366866+00:00
-- url     : https://prove2.me/theorems/378abc8e-2ec8-5c5d-b091-18fc2dd9c317
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.stochasticIntegral_zero_integrand

import Definitions.Def_SourceProof_7ca5a4a340ad9cc180bba716
import Definitions.Def_SourceProof_a0cc4ed706abedad0ad223c1
import Definitions.Def_SourceProof_c1502d54d2b7490012bf0be0
import Definitions.Def_SourceProof_c665a2779da0472ba911a85d
import Definitions.Def_SourceProof_d0ba14a65d084d5914c41424
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Protter II.19: stochastic integration preserves semimartingales

Uniformly vanishing simple test processes multiplied by the fixed caglad
integrand vanish in UCP. Continuity of the already constructed integral and
simple-outer associativity prove the good-integrator property at each finite
horizon. No classical decomposition or operator-closure assumption is used.
-/

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_47f4915fac265caea9ceaccb
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) :
    Indistinguishable (hX.stochasticIntegral hF (_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F))
      ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F)) P)) 0 P := by
  have heq : (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F).elementaryIntegralProcess X = 0 := by
    funext t
    exact _root_.Prove2MeSourceProof.h_c665a2779da0472ba911a85d F _
  simpa only [heq] using (_root_.Prove2MeSourceProof.h_a0cc4ed706abedad0ad223c1 hX) hF
    (_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F)) ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F)) P)
    (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F)
end IsSemimartingale

end ProbabilityTheory


