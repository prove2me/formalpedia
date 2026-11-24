-- Prove2me | Definitions.Def_StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
-- name    : StochLean_Probability_Process_Stopping_PredictableAfterCoefficient_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-24T18:57:16.132441+00:00
-- url     : https://prove2.me/theorems/64452890-5628-4cb3-a8f4-b576a6fd4796
-- title:
--   StochLean: Probability.Process.Stopping.PredictableAfterCoefficient F000

import Definitions.Def_StochLean_Probability_Process_Stopping_Graph_F000

/-
Copyright (c) 2026 StochLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: StochLean contributors
-/

/-! # Revealing predictable stopped information at its lifetime

A predictable lifetime has a predictable closed-future region. The source
announcing convention only gives almost-sure convergence; initial completeness
repairs the exceptional paths without changing the original lifetime or its
finite-time graph. Right continuity of the filtration and finiteness of the
measure are not needed.

A coefficient measurable strictly before this lifetime can be revealed at and
after it to obtain an actual strongly predictable process. The proof uses the
before-field generators on the closed-future region, and does not regard the
coefficient as initial information. At lifetime zero the coefficient is already
initial information. At infinite lifetime every finite-time value is zero,
regardless of the coefficient there; no value of a process at infinity is used.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

private theorem measurableSet_predictable_univ_prod_initial {A : Set Ω}
    (hA : MeasurableSet[F 0] A) :
    MeasurableSet[F.predictable] ((univ : Set ℝ≥0) ×ˢ A) := by
  have he : (univ : Set ℝ≥0) ×ˢ A = ({0} ×ˢ A) ∪ (Ioi 0 ×ˢ A) := by
    ext ⟨t, ω⟩
    simp only [mem_prod, mem_univ, true_and, mem_union, mem_singleton_iff, mem_Ioi]
    exact ⟨fun h ↦ (eq_or_lt_of_le (show 0 ≤ t from bot_le)).elim
      (fun ht ↦ Or.inl ⟨ht.symm, h⟩) (fun ht ↦ Or.inr ⟨ht, h⟩),
      fun h ↦ h.elim And.right And.right⟩
  rw [he]
  exact (measurableSet_predictable_singleton_bot_prod hA).union
    (measurableSet_predictable_Ioi_prod hA)
private theorem measurable_predictable_fst :
    Measurable[F.predictable] (Prod.fst : ℝ≥0 × Ω → ℝ≥0) := by
  apply measurable_of_Ioi
  intro t
  simpa only [prod_univ] using
    measurableSet_predictable_Ioi_prod (𝓕 := F) (i := t) MeasurableSet.univ
private theorem measurable_predictable_snd_initial :
    @Measurable (ℝ≥0 × Ω) Ω F.predictable (F 0) Prod.snd := by
  intro A hA
  simpa only [univ_prod] using measurableSet_predictable_univ_prod_initial hA
end ProbabilityTheory

namespace MeasureTheory

open ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {F : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

end MeasureTheory


