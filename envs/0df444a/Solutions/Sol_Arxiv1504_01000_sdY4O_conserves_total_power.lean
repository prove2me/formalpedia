-- Prove2me | solution 1 for Arxiv1504_01000.sdY4O_conserves_total_power
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:50:20.690807+00:00
-- url     : https://prove2.me/submissions/c956192d-7608-4b09-9ca3-deb2cbdb9889

import Mathlib
import Definitions.Def_Arxiv1504_01000_Basic

open MeasureTheory Filter Topology
open scoped ComplexOrder
open Arxiv1504_01000

theorem solution (P : Y4OPowers) (δ α β : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hα : 1 / 2 ≤ α ∧ α ≤ 1) (hβ : 0 ≤ β ∧ β ≤ 1 / 2) (hαβ : α + β = 1) :
    (sdY4O P δ α β).ps + (sdY4O P δ α β).pd + (sdY4O P δ α β).pv = P.ps + P.pd + P.pv ∧
    (sdY4O P δ α β).ps + (sdY4O P δ α β).pd + (sdY4O P δ α β).pv + (sdY4O P δ α β).pc =
      P.ps + P.pd + P.pv + P.pc ∧
    (∀ φ ∈ Set.Icc (0 : ℝ) (Real.pi / 4),
      1 / 2 ≤ alphaOfOA φ ∧ alphaOfOA φ ≤ 1 ∧ 0 ≤ 1 - alphaOfOA φ ∧ 1 - alphaOfOA φ ≤ 1 / 2) ∧
    alphaOfOA 0 = 1 / 2 ∧ alphaOfOA (Real.pi / 4) = 1 ∧
    alphaOfOA '' Set.Icc (0 : ℝ) (Real.pi / 4) = Set.Icc (1 / 2 : ℝ) 1 := by
  have hpi := Real.pi_pos
  have h1 : (sdY4O P δ α β).ps + (sdY4O P δ α β).pd + (sdY4O P δ α β).pv = P.ps + P.pd + P.pv := by
    simp only [sdY4O]; linear_combination P.pv * δ * hαβ
  have hb : ∀ φ ∈ Set.Icc (0 : ℝ) (Real.pi / 4), 1 / 2 ≤ alphaOfOA φ ∧ alphaOfOA φ ≤ 1 := by
    rintro φ ⟨h0, h4⟩
    unfold alphaOfOA
    constructor
    · have : 0 ≤ 2 * φ / Real.pi := by positivity
      linarith
    · have : 2 * φ / Real.pi ≤ 1 / 2 := by
        rw [div_le_iff₀ hpi]; linarith
      linarith
  refine ⟨h1, ?_, fun φ hφ => ?_, ?_, ?_, ?_⟩
  · simp only [sdY4O] at h1 ⊢; linarith
  · obtain ⟨a, b⟩ := hb φ hφ
    exact ⟨a, b, by linarith, by linarith⟩
  · simp [alphaOfOA]
  · unfold alphaOfOA; field_simp; norm_num
  · ext y
    constructor
    · rintro ⟨φ, hφ, rfl⟩; exact hb φ hφ
    · rintro ⟨h0, h1⟩
      refine ⟨(y - 1 / 2) * Real.pi / 2, ⟨by nlinarith, by nlinarith⟩, ?_⟩
      unfold alphaOfOA; field_simp; ring

