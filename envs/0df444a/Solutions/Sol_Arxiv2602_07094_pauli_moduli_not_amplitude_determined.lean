-- Prove2me | solution 1 for Arxiv2602_07094.pauli_moduli_not_amplitude_determined
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T23:41:23.749202+00:00
-- url     : https://prove2.me/submissions/d8d50a0f-871f-441c-89db-fd632f044b81

import Mathlib
import Definitions.Def_Arxiv2602_07094_Basic

set_option autoImplicit false

namespace S73PM
open Arxiv2602_07094

def S1 : SinclairMatrix := !![1, 0; 0, 1]
def S2 : SinclairMatrix := !![1, 0; 0, -1]

lemma r1 : IsReciprocal S1 := by simp [IsReciprocal, S1]
lemma r2 : IsReciprocal S2 := by simp [IsReciprocal, S2]
lemma amp : channelAmplitudes S1 = channelAmplitudes S2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [channelAmplitudes, S1, S2]
lemma s2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)).ne'

end S73PM

open Arxiv2602_07094 S73PM in
theorem solution :
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliAlpha S‖ = F (channelAmplitudes S)) ∧
    (¬ ∃ F : Matrix (Fin 2) (Fin 2) ℝ → ℝ, ∀ S : SinclairMatrix, IsReciprocal S →
        ‖pauliBeta S‖ = F (channelAmplitudes S)) := by
  constructor
  · rintro ⟨F, hF⟩
    have h1 := hF S1 r1
    have h2 := hF S2 r2
    rw [← amp, ← h1] at h2
    simp [pauliAlpha, S1, S2] at h2
    norm_num at h2
    have : (0:ℝ) < 2 / |Real.sqrt 2| := by positivity
    linarith
  · rintro ⟨F, hF⟩
    have h1 := hF S1 r1
    have h2 := hF S2 r2
    rw [← amp, ← h1] at h2
    simp [pauliBeta, S1, S2] at h2
