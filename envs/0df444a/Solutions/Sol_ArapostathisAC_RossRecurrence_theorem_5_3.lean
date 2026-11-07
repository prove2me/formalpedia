-- Prove2me | solution 1 for ArapostathisAC.RossRecurrence.theorem_5_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:21:25.311199+00:00
-- url     : https://prove2.me/submissions/6d2d288a-57c8-41de-bca4-eb8f9df404cd

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
import Theorems.Thm_ArapostathisAC_RossRecurrence_theorem_5_3_explicit
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ArapostathisAC.RossRecurrence

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K) :
    ∃ B : ℝ, ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ B :=
  ⟨M₀ * K, theorem_5_3_explicit M M₀ hc K hK h57⟩
