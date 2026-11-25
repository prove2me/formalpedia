-- Prove2me | Definitions.Def_SourceProof_2b2fa01d52a365fcbed78a43
-- name    : SourceProof_2b2fa01d52a365fcbed78a43
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-25T17:10:15.204268+00:00
-- url     : https://prove2.me/theorems/6c782219-dda4-454c-b1ca-477bf920e482
-- title:
--   StochLean source theorem: MeasureTheory.Adapted.measurable_capped_jumpProcess_of_cadlag

import Definitions.Def_SourceProof_6a141fa6412d14db4fc15aeb
import Definitions.Def_SourceProof_6fe8e798f5fa5227db6c7521
import Definitions.Def_SourceProof_8bf3de97f19c795595f124e8
import Definitions.Def_SourceProof_f006d78a6e9979cf18230f20

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Joint jump measurability using only a fixed finite horizon

The capped jump uses the original adapted cadlag process and its source
left limit. Both progressive restrictions are measurable in the horizon
sigma-algebra. No measurability from future coordinates is used.
-/

@[expose] public section

open ProbabilityTheory MeasureTheory Set
open scoped NNReal

namespace MeasureTheory

namespace Adapted
theorem _root_.Prove2MeSourceProof.h_2b2fa01d52a365fcbed78a43
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
    {X : ℝ≥0 → Ω → ℝ} (ha : Adapted F X)
    (hc : ∀ ω, IsCadlagPath (fun t ↦ X t ω)) (T : ℝ≥0) :
    @Measurable (Ω × ℝ≥0) ℝ ((F T).prod inferInstance) inferInstance
      (fun p ↦ jumpProcess X (min p.2 T) p.1) := by
  have hx := ((_root_.Prove2MeSourceProof.h_6a141fa6412d14db4fc15aeb ha.stronglyAdapted)
    (fun ω ↦ (hc ω).1)) T
  have hla := ((_root_.Prove2MeSourceProof.h_6fe8e798f5fa5227db6c7521 ha) hc).stronglyAdapted
  have hl := ((_root_.Prove2MeSourceProof.h_8bf3de97f19c795595f124e8 hla)
    (fun ω ↦ (_root_.Prove2MeSourceProof.h_f006d78a6e9979cf18230f20 (hc ω)).1)) T
  have hj := (hx.sub hl).measurable
  let : MeasurableSpace Ω := F T
  have hm : Measurable (fun p : Ω × ℝ≥0 ↦
      ((⟨min p.2 T, Set.mem_Iic.mpr (min_le_right _ _)⟩ : Iic T), p.1)) :=
    ((measurable_snd.min measurable_const).subtype_mk).prodMk measurable_fst
  exact hj.comp hm
end Adapted

end MeasureTheory


