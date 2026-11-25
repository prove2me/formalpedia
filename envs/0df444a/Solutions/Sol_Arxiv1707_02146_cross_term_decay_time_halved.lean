-- Prove2me | solution 1 for Arxiv1707_02146.cross_term_decay_time_halved
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:38:52.032446+00:00
-- url     : https://prove2.me/submissions/cbc9b51f-755c-43c8-ab80-0809b7fb4301

import Mathlib
import Definitions.Def_Arxiv1707_02146_Basic

open Matrix ComplexConjugate
open Arxiv1707_02146

lemma exp_two (t τm : ℝ) : Real.exp (-t / τm) * Real.exp (-t / τm) = Real.exp (-2 * t / τm) := by
  rw [← Real.exp_add]; congr 1; ring

theorem solution (r s : ℝ → ℝ) (τm : ℝ)
    (hr : HasExpDecay r τm) (hs : HasExpDecay s τm) :
    (∃ C : ℝ, C ≠ 0 ∧ ∀ t : ℝ, 0 ≤ t → r t * s t = C * Real.exp (-2 * t / τm)) ∧
    HasExpDecay (fun t => r t * s t) (τm / 2) ∧
    ∀ τf : ℝ, HasExpDecay (fun t => r t * s t) τf → τf = τm / 2 := by
  obtain ⟨hτ, C1, hC1, h1⟩ := hr
  obtain ⟨-, C2, hC2, h2⟩ := hs
  have key : ∀ t : ℝ, 0 ≤ t → r t * s t = (C1 * C2) * Real.exp (-2 * t / τm) := by
    intro t ht
    rw [h1 t ht, h2 t ht, ← exp_two]; ring
  have hC : C1 * C2 ≠ 0 := mul_ne_zero hC1 hC2
  refine ⟨⟨C1 * C2, hC, key⟩, ⟨by positivity, C1 * C2, hC, fun t ht => ?_⟩, ?_⟩
  · show r t * s t = _
    rw [key t ht]; congr 2; field_simp
  · rintro τf ⟨hτf, D, hD, hDe⟩
    have e0 := (key 0 le_rfl).symm.trans (hDe 0 le_rfl)
    simp at e0
    have e1 := (key 1 zero_le_one).symm.trans (hDe 1 zero_le_one)
    rw [e0] at e1
    have e2 : Real.exp (-2 * 1 / τm) = Real.exp (-1 / τf) := mul_left_cancel₀ hD e1
    have e3 := Real.exp_injective e2
    field_simp at e3
    linarith

