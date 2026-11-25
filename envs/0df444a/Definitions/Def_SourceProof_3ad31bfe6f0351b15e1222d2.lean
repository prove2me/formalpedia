-- Prove2me | Definitions.Def_SourceProof_3ad31bfe6f0351b15e1222d2
-- name    : SourceProof_3ad31bfe6f0351b15e1222d2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T20:08:28.721701+00:00
-- url     : https://prove2.me/theorems/6d32cf98-9575-45f6-8bc8-5f09561e5d6c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.tendstoUCP_stochasticIntegral

import Definitions.Def_StochLean_Probability_Process_Semimartingale_StochasticIntegral_F000
import Definitions.Def_SourceProof_4dc1343e0d58f394f7cafe01
import Definitions.Def_SourceProof_67abbf0ff32d832502948a1b
import Definitions.Def_SourceProof_abb8e2f5680049693694a2fd
import Definitions.Def_SourceProof_c55d17120c217e6f4e472165
import Definitions.Def_SourceProof_e327ffe5c9d18f0324a2ad4e

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP continuity of the constructed Chapter II integral

Each integrand is approximated by actual simple processes. A simultaneous
diagonal controls both input and integral errors, proving continuity on the
whole adapted-caglad domain, not just on the dense simple subclass.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X H : ℝ≥0 → Ω → ℝ} {K : ℕ → ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_3ad31bfe6f0351b15e1222d2
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P)
    (haH : Adapted F H) (hrH : HasCagladPaths H P)
    (haK : ∀ n, Adapted F (K n)) (hrK : ∀ n, HasCagladPaths (K n) P)
    (hu : TendstoUCP P K atTop H) :
    TendstoUCP P (fun n ↦ hX.stochasticIntegral hF (haK n) (hrK n)) atTop
      (hX.stochasticIntegral hF haH hrH) := by
  choose A hA huA using fun n ↦ _root_.Prove2MeSourceProof.h_abb8e2f5680049693694a2fd (haK n) hF (hrK n)
  have hJA : ∀ n, ProbabilityTheory.TendstoUCP P (fun k ↦ (hA n k).elementaryIntegralProcess X) atTop
      (hX.stochasticIntegral hF (haK n) (hrK n)) := fun n ↦
    (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF (haK n) (hrK n) (hA n) (huA n)
  obtain ⟨k, hdiA, hdiJ⟩ := _root_.Prove2MeSourceProof.h_67abbf0ff32d832502948a1b huA hJA
  have hinput : ProbabilityTheory.TendstoUCP P (fun n ↦ A n (k n)) atTop H := by
    simpa only [sub_add_cancel, zero_add] using (_root_.Prove2MeSourceProof.h_c55d17120c217e6f4e472165 hdiA) hu
  have houtput := (_root_.Prove2MeSourceProof.h_e327ffe5c9d18f0324a2ad4e hX) hF haH hrH
    (fun n ↦ hA n (k n)) hinput
  simpa only [neg_sub, sub_add_cancel, neg_zero, zero_add] using (_root_.Prove2MeSourceProof.h_c55d17120c217e6f4e472165 (_root_.Prove2MeSourceProof.h_4dc1343e0d58f394f7cafe01 hdiJ)) houtput
end IsSemimartingale

end ProbabilityTheory


