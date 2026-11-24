-- Prove2me | Definitions.Def_SourceProof_260006becf8053b16cb2c165
-- name    : SourceProof_260006becf8053b16cb2c165
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:21:37.874173+00:00
-- url     : https://prove2.me/theorems/02c4fa21-9e11-4a77-a908-5f0c81095585
-- title:
--   StochLean source theorem: ProbabilityTheory.TendstoUCP.cauchyUCP

import Definitions.Def_StochLean_Probability_Process_UCP_Cauchy_F000
import Definitions.Def_StochLean_Probability_Process_UCP_F001
import Definitions.Def_SourceProof_87a77990b75276f36eedefb4
import Definitions.Def_SourceProof_c85f5070e7769bac711d7f66

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # UCP-Cauchy sequences and a common-event uniform Cauchy subsequence

The criterion uses the existing UCP strict-deviation events. The subsequence is
constructed by a summable-probability diagonal, without assuming measurable paths
or continuity of an outer measure on arbitrary decreasing sets.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {X : ℕ → ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω → ℝ}

namespace TendstoUCP
theorem _root_.Prove2MeSourceProof.h_260006becf8053b16cb2c165 (h : TendstoUCP P X atTop Y) : CauchyUCP P X := by
  intro T ε hε η hη
  obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp h T (ε / 2) (half_pos hε))
    (η / 2) (ENNReal.half_pos hη.ne')
  refine ⟨N, fun m n hm hn ↦ ?_⟩
  have htri := _root_.Prove2MeSourceProof.h_87a77990b75276f36eedefb4 (P := P) (X m) Y (X n) T ε
  simp only [norm_sub_rev (Y _ _) (X n _ _)] at htri
  exact htri.trans ((add_le_add (hN m hm) (hN n hn)).trans (ENNReal.add_halves η).le)
end TendstoUCP

end ProbabilityTheory


