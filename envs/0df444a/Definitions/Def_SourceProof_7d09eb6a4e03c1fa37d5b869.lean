-- Prove2me | Definitions.Def_SourceProof_7d09eb6a4e03c1fa37d5b869
-- name    : SourceProof_7d09eb6a4e03c1fa37d5b869
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:36:44.624129+00:00
-- url     : https://prove2.me/theorems/ed3102e3-077e-49d1-a587-19d0f9c97d88
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.isSemimartingale_stochasticIntegral

import Definitions.Def_SourceProof_0144d989fffae649e78e1206
import Definitions.Def_SourceProof_13d74fe230d87debed607218
import Definitions.Def_SourceProof_1557efb7e848f4cf57c0170c
import Definitions.Def_SourceProof_3ad31bfe6f0351b15e1222d2
import Definitions.Def_SourceProof_470edda0db5866af621dc0b9
import Definitions.Def_SourceProof_47f4915fac265caea9ceaccb
import Definitions.Def_SourceProof_523d7cde826eec51d63a0e17
import Definitions.Def_SourceProof_615a61300ee6a9f8d8759333
import Definitions.Def_SourceProof_7ca5a4a340ad9cc180bba716
import Definitions.Def_SourceProof_87f0a7a067d30089e512c6db
import Definitions.Def_SourceProof_9c5e30e37c7ae3d824080fb0
import Definitions.Def_SourceProof_a306c42680d425170aa442b0
import Definitions.Def_SourceProof_b9794289e5911ccd8b7b2b92
import Definitions.Def_SourceProof_c1502d54d2b7490012bf0be0
import Definitions.Def_SourceProof_d0a4533c9dc122ef1fd7f577
import Definitions.Def_SourceProof_d0ba14a65d084d5914c41424

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
theorem _root_.Prove2MeSourceProof.h_7d09eb6a4e03c1fa37d5b869
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (ha : Adapted F H) (hr : HasCagladPaths H P) :
    IsSemimartingale (hX.stochasticIntegral hF ha hr) F P := by
  let Y := hX.stochasticIntegral hF ha hr
  have haY : Adapted F Y := (_root_.Prove2MeSourceProof.h_a306c42680d425170aa442b0 hX) hF ha hr
  have hrY : ProbabilityTheory.HasCadlagPaths Y P := (_root_.Prove2MeSourceProof.h_470edda0db5866af621dc0b9 hX) hF ha hr
  intro T
  refine ⟨?_, (_root_.Prove2MeSourceProof.h_1557efb7e848f4cf57c0170c hrY) (fun _ ↦ (T : WithTop ℝ≥0)), ?_⟩
  · intro t
    change Measurable[F t] (Y (min t T))
    exact (haY _).mono (F.mono (min_le_left t T)) le_rfl
  · intro G hG huG
    have hu0 : ProbabilityTheory.TendstoUCP P G atTop 0 := _root_.Prove2MeSourceProof.h_b9794289e5911ccd8b7b2b92 huG
    have huGH := (_root_.Prove2MeSourceProof.h_615a61300ee6a9f8d8759333 hu0)
      (fun n t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (hG n)) t).mono (F.le t) le_rfl)
      (fun _ ↦ measurable_const) (fun t ↦ (ha t).mono (F.le t) le_rfl)
      (fun n ↦ (_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (hG n)) P) ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F)) P) hr
    rw [zero_mul] at huGH
    have huJ := (_root_.Prove2MeSourceProof.h_3ad31bfe6f0351b15e1222d2 hX) hF (_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F))
      ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (_root_.Prove2MeSourceProof.h_c1502d54d2b7490012bf0be0 F)) P)
      (fun n t ↦ ((_root_.Prove2MeSourceProof.h_d0ba14a65d084d5914c41424 (hG n)) t).mul (ha t))
      (fun n ↦ (_root_.Prove2MeSourceProof.h_523d7cde826eec51d63a0e17 ((_root_.Prove2MeSourceProof.h_7ca5a4a340ad9cc180bba716 (hG n)) P)) hr) huGH
    have huJ0 := (_root_.Prove2MeSourceProof.h_9c5e30e37c7ae3d824080fb0 huJ) ((_root_.Prove2MeSourceProof.h_47f4915fac265caea9ceaccb hX) hF)
    have huY : ProbabilityTheory.TendstoUCP P (fun n ↦ (hG n).elementaryIntegralProcess Y) atTop 0 :=
      (_root_.Prove2MeSourceProof.h_87f0a7a067d30089e512c6db huJ0) (fun n ↦
        (_root_.Prove2MeSourceProof.h_13d74fe230d87debed607218 ((_root_.Prove2MeSourceProof.h_0144d989fffae649e78e1206 hX) hF (hG n) ha hr)))
    exact (_root_.Prove2MeSourceProof.h_d0a4533c9dc122ef1fd7f577 huY) T
end IsSemimartingale

end ProbabilityTheory


