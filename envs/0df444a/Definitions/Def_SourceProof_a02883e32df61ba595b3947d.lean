-- Prove2me | Definitions.Def_SourceProof_a02883e32df61ba595b3947d
-- name    : SourceProof_a02883e32df61ba595b3947d
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T19:27:01.971079+00:00
-- url     : https://prove2.me/theorems/750884eb-b305-4d01-ab3d-43c4424742a8
-- title:
--   StochLean source theorem: ProbabilityTheory.IsLocalMartingale.congr

import Definitions.Def_SourceProof_5a4916e2e6cda9f70d628fae
import Definitions.Def_SourceProof_7e41a7708f0759111a0ce622
import Definitions.Def_SourceProof_96331e337c0a0b8560074745
import Definitions.Def_SourceProof_9f2f3563711c68b81e63664c
import Definitions.Def_SourceProof_a239f509638bc9274841d0b5
import Definitions.Def_SourceProof_bdb573aab3428152bd91f0a3
import Definitions.Def_SourceProof_d758c5fe1bf7eec6f7a3ad7f
import Definitions.Def_SourceProof_d93b464447ac66fa122a70c4
import Definitions.Def_SourceProof_de3c03ff359f630b7abb9271
import Definitions.Def_SourceProof_e79cc5d7fc8aa48d10e205ad

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Indistinguishable versions of the existing local-martingale predicates

The actual fundamental sequence is retained, including its initial masks.
Adaptedness of the target is explicit; no measurability of arbitrary versions
is silently assumed.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsLocalMartingale
theorem _root_.Prove2MeSourceProof.h_a02883e32df61ba595b3947d (hX : IsLocalMartingale X F P)
    (hF : F.IsUsual P) (ha : Adapted F Y) (he : Indistinguishable X Y P) :
    IsLocalMartingale Y F P := by
  have hc := (fun p2mMethodArg0 => _root_.Prove2MeSourceProof.h_5a4916e2e6cda9f70d628fae p2mMethodArg0 hX.2.1) he
  obtain ⟨τ, hτ⟩ := hX.2.2
  refine ⟨ha, hc, τ, hτ.1, hτ.2.1, fun n ↦ ?_⟩
  have hs : MeasurableSet[F 0] {ω | 0 < τ n ω} :=
    (hτ.1.isStoppingTime n).measurableSet_gt 0
  have hmask := (_root_.Prove2MeSourceProof.h_96331e337c0a0b8560074745 ha) hs
  exact (_root_.Prove2MeSourceProof.h_bdb573aab3428152bd91f0a3 (hτ.2.2 n))
    ((_root_.Prove2MeSourceProof.h_d758c5fe1bf7eec6f7a3ad7f hmask.stronglyAdapted) hF
      (_root_.Prove2MeSourceProof.h_9f2f3563711c68b81e63664c ((_root_.Prove2MeSourceProof.h_7e41a7708f0759111a0ce622 hc) {ω | 0 < τ n ω})) (hτ.1.isStoppingTime n)).adapted
    ((_root_.Prove2MeSourceProof.h_a239f509638bc9274841d0b5 ((_root_.Prove2MeSourceProof.h_de3c03ff359f630b7abb9271 he) {ω | 0 < τ n ω})) (τ n))
end IsLocalMartingale

end ProbabilityTheory


