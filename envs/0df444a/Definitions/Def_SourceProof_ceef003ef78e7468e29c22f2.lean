-- Prove2me | Definitions.Def_SourceProof_ceef003ef78e7468e29c22f2
-- name    : SourceProof_ceef003ef78e7468e29c22f2
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-19T19:18:14.965677+00:00
-- url     : https://prove2.me/theorems/b918ceb7-5ccf-4968-9030-ca0afc920a26
-- title:
--   LevyStochCalc source module: SourceProof_ceef003ef78e7468e29c22f2
-- statement:
--   The original source theorem `ProbabilityTheory.edist_modification_holderModification` comes from the `BrownianMotion.Continuity.KolmogorovChentsov` module. The staged Lean declaration includes its source proof and dependency references.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F001

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

section HolderSet

end HolderSet

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

theorem _root_.Prove2MeSourceProof.h_ceef003ef78e7468e29c22f2 (hT : HasBoundedCoveringNumber U c d)
    [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (hX : IsKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q) (hβ_pos : 0 < β) (hβ_lt : β < (q - d) / p)
    (t : T) (htU : t ∈ U) :
    ∀ᵐ ω ∂P, edist (holderModification X β p U t ω) (X t ω) = 0 := by
  -- For each `ω`, `C ω < ∞` is a bound on `edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)`
  let C ω := ⨆ (s : (denseCountable T ∩ U : Set T)) (t : (denseCountable T ∩ U : Set T)),
    edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p)
  -- Let `A` be the event that `C ω < ∞` and `X s ω = X t ω` for `edist s t = 0`.
  -- This is an event of probability 1.
  let A := ProbabilityTheory.holderSet X (denseCountable T) p β U
  have hA_ae : ∀ᵐ ω ∂P, ω ∈ A := ProbabilityTheory.ae_mem_holderSet hT hX hc hd_pos hdq_lt hβ_pos hβ_lt
    countable_denseCountable
  have hPA {s : Set Ω} : P (s ∩ A) = P s := by
    rw [Set.inter_comm, Measure.measure_inter_eq_of_ae hA_ae]
  -- Properties of the modification
  let Y := ProbabilityTheory.holderModification X β p U
  have hY_eq {ω : Ω} (hω : ω ∈ A) (t : denseCountable T) (htU : ↑t ∈ U) :
      edist (Y t ω) (X t ω) = 0 := by
    exact ProbabilityTheory.edist_holderModification_eq_zero hT hU hX hβ_pos t htU hω
  classical
  have hY_unif ω : UniformContinuousOn (fun t ↦ Y t ω) U :=
    ProbabilityTheory.uniformContinuousOn_holderModification hT hU hX hβ_pos ω
  have hY_cont ω : ContinuousOn (fun t ↦ Y t ω) U :=
    ProbabilityTheory.continuousOn_holderModification hT hU hX hβ_pos ω
  -- Main proof
  suffices ∀ᵐ ω ∂P, edist (Y t ω) (X t ω) ≤ 0 by
    filter_upwards [this] with ω h using by simpa using h
  obtain ⟨u, huU, hu⟩ : ∃ u : ℕ → denseCountable T, (∀ n, ↑(u n) ∈ U) ∧
      Tendsto (fun n ↦ (u n : T)) atTop (𝓝 t) := by
    have ht_mem_closure : t ∈ closure (denseCountable T) := by
      simp [dense_denseCountable.closure_eq]
    rw [mem_closure_iff_seq_limit] at ht_mem_closure
    obtain ⟨u', hu'_mem, hu'⟩ := ht_mem_closure
    obtain ⟨t₀, ht₀⟩ : ∃ t' : denseCountable T, ↑t' ∈ U := by
      obtain ⟨t', ht'⟩ := dense_denseCountable.exists_mem_open hU ⟨t, htU⟩
      exact ⟨⟨t', ht'.1⟩, ht'.2⟩
    refine ⟨fun n ↦ if u' n ∈ U then ⟨u' n, hu'_mem n⟩ else t₀, fun n ↦ ?_, ?_⟩
    · simp only
      split_ifs with hmem
      · simp [hmem]
      · simp [ht₀]
    · have h_eventually_mem := Tendsto.eventually_mem hu' (hU.mem_nhds htU)
      refine hu'.congr' ?_
      filter_upwards [h_eventually_mem] with n hmem
      simp [hmem]
  have h_le n {ω} (hω : ω ∈ A) : edist (Y t ω) (X t ω)
      ≤ edist (Y t ω) (Y (u n) ω) + edist (X (u n) ω) (X t ω) := by
    refine (edist_triangle4 (Y t ω) (Y (u n) ω) (X (u n) ω) (X t ω)).trans_eq ?_
    simp [hY_eq hω (u n) (huU n)]
  -- `X (u n)` converges in measure to `X t`
  have h_tendsto_X : TendstoInMeasure P (fun n ↦ X (u n)) atTop (X t) :=
    hX.tendstoInMeasure (hd_pos.trans hdq_lt) hu
  -- `Y (u n)` converges in measure to `Y t`
  have h_tendsto_Y : TendstoInMeasure P (fun n ↦ Y (u n)) atTop (Y t) := by
    have h_ae ω : Tendsto (fun n ↦ Y (u n) ω) atTop (𝓝 (Y t ω)) := by
      refine (hY_cont ω t htU).tendsto.comp ?_
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu (.of_forall huU)
    refine tendstoInMeasure_of_tendsto_ae_of_measurable_edist (fun n ↦ ?_) (ae_of_all _ h_ae)
    exact ProbabilityTheory.measurable_edist_holderModification' hT hU hX hc hd_pos hdq_lt hβ_pos hβ_lt hβ_pos hβ_lt
      (u n) t
  refine (ae_le_const_iff_forall_gt_measure_zero _ _).mpr fun ε hε ↦ ?_
  suffices Tendsto (fun n : ℕ ↦ P {ω | ε ≤ edist (Y t ω) (X t ω)}) atTop (𝓝 0) by
    simpa using this
  have hP_le n : P {ω | ε ≤ edist (Y t ω) (X t ω)}
      ≤ P {ω | ε/2 ≤ edist (Y (u n) ω) (Y t ω)} + P {ω | ε/2 ≤ edist (X (u n) ω) (X t ω)} := by
    calc P {ω | ε ≤ edist (Y t ω) (X t ω)}
    _ = P ({ω | ε ≤ edist (Y t ω) (X t ω)} ∩ A) := by rw [hPA]
    _ ≤ P ({ω | ε ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} ∩ A) := by
      refine measure_mono fun ω ↦ ?_
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, and_imp]
      refine fun hε_le hω ↦ ⟨(hε_le.trans (h_le n hω)).trans_eq ?_, hω⟩
      rw [edist_comm]
    _ = P {ω | ε ≤ edist (Y (u n) ω) (Y t ω) + edist (X (u n) ω) (X t ω)} := by rw [hPA]
    _ ≤ P {ω | ε / 2 ≤ edist (Y (u n) ω) (Y t ω)}
        + P {ω | ε / 2 ≤ edist (X (u n) ω) (X t ω)} := measure_add_ge_le_add_measure_ge_half
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ ↦ zero_le) hP_le
  rw [← add_zero (0 : ℝ≥0∞)]
  exact Tendsto.add (h_tendsto_Y (ε / 2) (ENNReal.half_pos hε.ne'))
    (h_tendsto_X (ε / 2) (ENNReal.half_pos hε.ne'))
end PseudoEMetricSpace

section EMetricSpace

variable [PseudoEMetricSpace T] [EMetricSpace E] [hE : Nonempty E]

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

end EMetricSpace

end ProbabilityTheory


