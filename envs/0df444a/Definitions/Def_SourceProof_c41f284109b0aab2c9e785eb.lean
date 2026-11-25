-- Prove2me | Definitions.Def_SourceProof_c41f284109b0aab2c9e785eb
-- name    : SourceProof_c41f284109b0aab2c9e785eb
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T18:17:33.892979+00:00
-- url     : https://prove2.me/theorems/52e435bc-48c4-495d-8a2e-a62674a60d3c
-- title:
--   StochLean source theorem: ProbabilityTheory.IsSemimartingale.congr_of_usual

import Definitions.Def_SourceProof_2805187910815ebae4f90f84
import Definitions.Def_SourceProof_2cbb2ed1687ae3057f41e0d2
import Definitions.Def_SourceProof_46e00cd1de49de31920230f6
import Definitions.Def_SourceProof_59b26859132e89360b279698
import Mathlib.Topology.Algebra.Monoid

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Indistinguishable versions under usual conditions

Relative completeness supplies adaptedness of the target version, even
when its exceptional null path set was not initially measurable.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

namespace IsSemimartingale
theorem _root_.Prove2MeSourceProof.h_c41f284109b0aab2c9e785eb
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {X Y : ℝ≥0 → Ω → ℝ}
    (hX : IsSemimartingale X F P) (hF : F.IsUsual P) (hXY : Indistinguishable X Y P) :
    IsSemimartingale Y F P := by
  apply (_root_.Prove2MeSourceProof.h_2805187910815ebae4f90f84 hX) hXY
  intro t
  have hc : MeasureTheory.IsCompleteSubMeasurableSpace P (F t) :=
    fun s hs ↦ F.mono bot_le s ((_root_.Prove2MeSourceProof.h_59b26859132e89360b279698 hF) s hs)
  exact (_root_.Prove2MeSourceProof.h_46e00cd1de49de31920230f6 hc) ((_root_.Prove2MeSourceProof.h_2cbb2ed1687ae3057f41e0d2 hX) t) (hXY.mono (fun _ h ↦ h t))
end IsSemimartingale

end ProbabilityTheory


