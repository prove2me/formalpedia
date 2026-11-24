-- Prove2me | Definitions.Def_SourceProof_884540530c27c62e87bbaba4
-- name    : SourceProof_884540530c27c62e87bbaba4
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T23:46:05.322375+00:00
-- url     : https://prove2.me/theorems/be280114-e91b-4be9-8383-3228c53fe692
-- title:
--   StochLean source theorem: ProbabilityTheory.CauchyUCP.tendstoUCP_of_subseq

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

namespace CauchyUCP
theorem _root_.Prove2MeSourceProof.h_884540530c27c62e87bbaba4 (hc : CauchyUCP P X) {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hs : TendstoUCP P (X ∘ k) atTop Y) :
    TendstoUCP P X atTop Y := by
  apply _root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mpr
  intro T ε hε
  apply ENNReal.tendsto_atTop_zero.mpr
  intro η hη
  obtain ⟨N, hN⟩ := hc T (ε / 2) (half_pos hε) (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨K, hK⟩ := ENNReal.tendsto_atTop_zero.mp
    (_root_.Prove2MeSourceProof.h_c85f5070e7769bac711d7f66.mp hs T (ε / 2) (half_pos hε))
    (η / 2) (ENNReal.half_pos hη.ne')
  obtain ⟨j, hjN, hjK⟩ := ((hk.eventually (eventually_ge_atTop N)).and
    (eventually_ge_atTop K)).exists
  refine ⟨N, fun n hn ↦ ?_⟩
  exact (_root_.Prove2MeSourceProof.h_87a77990b75276f36eedefb4 (X n) (X (k j)) Y T ε).trans
    ((add_le_add (hN n (k j) hn hjN) (hK j hjK)).trans (ENNReal.add_halves η).le)
end CauchyUCP

end ProbabilityTheory


