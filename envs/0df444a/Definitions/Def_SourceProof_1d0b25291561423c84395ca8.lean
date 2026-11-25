-- Prove2me | Definitions.Def_SourceProof_1d0b25291561423c84395ca8
-- name    : SourceProof_1d0b25291561423c84395ca8
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T21:29:48.286222+00:00
-- url     : https://prove2.me/theorems/e71b49f7-013c-4614-a0cf-8ae75dc830ad
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.quadraticCovariation_continuous_jump_decomposition

import Definitions.Def_StochLean_Probability_Process_Semimartingale_QuadraticCovariation_ContinuousPart_F000
import Definitions.Def_SourceProof_31d0de13ef1656df97c05a7d
import Definitions.Def_SourceProof_5a35c10e8d17dd593b89b4ce
import Definitions.Def_SourceProof_60b183cce884b1ffa7a599f8
import Definitions.Def_SourceProof_7a2cd734cad19a873789e942
import Definitions.Def_SourceProof_c207270dc0d962c8e8bb99f9
import Definitions.Def_SourceProof_e0591ffe772e5ca30a6f7079

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # The continuous component of mixed quadratic covariation

Polarization is applied to the continuous components of the same raw square
brackets. The actual mixed-jump series is absolutely summable, and the raw
covariation decomposes into its initial product, continuous part and that series.
Mixed continuous covariation is not asserted to be increasing.
-/

@[expose] public section

open MeasureTheory StochLean Set Filter
open scoped NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_1d0b25291561423c84395ca8
    (hX : IsSemimartingale X F P) (hY : IsSemimartingale Y F P) (hF : F.IsUsual P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Summable (fun s : Ioc 0 t ↦ |jumpProcess X s ω * jumpProcess Y s ω|) ∧
      hX.quadraticCovariation hY hF t ω = X 0 ω * Y 0 ω +
        hX.continuousQuadraticCovariation hY hF t ω +
          ∑' s : Ioc 0 t, jumpProcess X s ω * jumpProcess Y s ω := by
  filter_upwards [(_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 hX) hF,
    (_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 hY) hF,
    (_root_.Prove2MeSourceProof.h_7a2cd734cad19a873789e942 ((_root_.Prove2MeSourceProof.h_31d0de13ef1656df97c05a7d hX) hY)) hF,
    (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hX), (_root_.Prove2MeSourceProof.h_60b183cce884b1ffa7a599f8 hY)] with ω hx hy hz hcx hcy t
  have hsum : (∑' s : Ioc 0 t, (ProbabilityTheory.jumpProcess (X + Y) s ω) ^ 2) =
      (∑' s : Ioc 0 t, (ProbabilityTheory.jumpProcess X s ω) ^ 2) +
        2 * (∑' s : Ioc 0 t, ProbabilityTheory.jumpProcess X s ω * ProbabilityTheory.jumpProcess Y s ω) +
          (∑' s : Ioc 0 t, (ProbabilityTheory.jumpProcess Y s ω) ^ 2) := by
    calc
      _ = ∑' s : Ioc 0 t, (ProbabilityTheory.jumpProcess X s ω + ProbabilityTheory.jumpProcess Y s ω) ^ 2 := by
        apply tsum_congr
        intro s
        rw [(_root_.Prove2MeSourceProof.h_e0591ffe772e5ca30a6f7079 hcx) hcy s]
      _ = _ := _root_.Prove2MeSourceProof.h_c207270dc0d962c8e8bb99f9 (hx t).1 (hy t).1
  refine ⟨_root_.Prove2MeSourceProof.h_5a35c10e8d17dd593b89b4ce (hx t).1 (hy t).1, ?_⟩
  rw [ProbabilityTheory.IsSemimartingale.quadraticCovariation, (hz t).2, (hx t).2, (hy t).2, hsum]
  simp only [ProbabilityTheory.IsSemimartingale.continuousQuadraticCovariation, Pi.add_apply]
  ring
end IsSemimartingale

end ProbabilityTheory


