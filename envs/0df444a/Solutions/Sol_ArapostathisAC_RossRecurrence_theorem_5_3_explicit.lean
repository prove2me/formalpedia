-- Prove2me | solution 1 for ArapostathisAC.RossRecurrence.theorem_5_3_explicit
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:21:25.933837+00:00
-- url     : https://prove2.me/submissions/7e0b66f2-1898-43f1-b92a-e0b8b1c34fe9

import Mathlib
import Definitions.Def_ArapostathisAC_RossRecurrence_CMP
import Definitions.Def_ArapostathisAC_RossRecurrence_ReturnTime
import Theorems.Thm_ArapostathisAC_RossRecurrence_eq_5_9
import Theorems.Thm_ArapostathisAC_RossRecurrence_eq_5_10
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open ArapostathisAC.RossRecurrence

theorem solution {A : Type*} [MetricSpace A] [MeasurableSpace A] [BorelSpace A]
    (M : CMP A) (M₀ : ℝ) (hc : ∀ i, ∀ a ∈ M.U i, M.c i a ≤ M₀)
    (K : ℝ) (hK : 0 < K)
    (h57 : ∀ f : StationaryPolicy M, ∀ i, meanReturnTime M f i < ENNReal.ofReal K) :
    ∀ β ∈ Set.Ioo (0 : ℝ) 1, ∀ i, |hRel M β i| ≤ M₀ * K := by
  intro β hβ i
  have h9 := eq_5_9 M M₀ hc K hK h57 β hβ i
  obtain ⟨h10a, h10b, h10c⟩ := eq_5_10 M M₀ hc K hK h57 β hβ i
  have h0 : 0 ≤ (discValue M β 0).toReal := ENNReal.toReal_nonneg
  have hb1 : β < 1 := hβ.2
  unfold hRel
  rw [abs_le]
  constructor
  · linarith
  · nlinarith
