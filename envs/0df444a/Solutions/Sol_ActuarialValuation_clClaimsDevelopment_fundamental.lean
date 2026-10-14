-- Prove2me | solution 1 for ActuarialValuation.clClaimsDevelopment_fundamental
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T12:12:28.639843+00:00
-- url     : https://prove2.me/submissions/8baadc77-5eaa-41cf-a672-29c3e4581ad8

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_clLinkNumerator
import Definitions.Def_actuarial_clLinkDenominator
import Definitions.Def_actuarial_clVolumeFactor
import Definitions.Def_actuarial_clUltimate
import Definitions.Def_actuarial_clReserve
import Definitions.Def_actuarial_clPaidFraction
import Definitions.Def_actuarial_clUnpaidFraction
import Definitions.Def_actuarial_clBFReserve
import Definitions.Def_actuarial_clBFUltimate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (paid : ℕ → ℕ → ℝ) (m j : ℕ) (hD : clLinkDenominator paid m j ≠ 0) (latest prior : ℝ) (factor : ℝ) (hF : 1 ≤ factor) (hC : 0 ≤ latest) (hE : 0 ≤ prior) : (clVolumeFactor paid m j * clLinkDenominator paid m j = clLinkNumerator paid m j) ∧ (latest + clReserve latest factor = clUltimate latest factor) ∧ (clBFUltimate latest prior factor = clPaidFraction factor * clUltimate latest factor + clUnpaidFraction factor * prior) ∧ (0 ≤ clReserve latest factor) ∧ (0 ≤ clBFReserve prior factor) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (clLinkNumerator paid m j / clLinkDenominator paid m j) *
      clLinkDenominator paid m j = clLinkNumerator paid m j
    exact (eq_div_iff hD).mp rfl
  · unfold clReserve
    ring
  · have hf : factor ≠ 0 := by linarith
    unfold clBFUltimate clBFReserve clUltimate clPaidFraction clUnpaidFraction
    field_simp [hf] <;> ring
  · change 0 ≤ latest * factor - latest
    calc
      0 ≤ latest * (factor - 1) := mul_nonneg hC (sub_nonneg.mpr hF)
      _ = latest * factor - latest := by ring
  · have hfpos : 0 < factor := by linarith
    have hpaid : (1 : ℝ) / factor ≤ 1 := by
      apply (div_le_iff₀ hfpos).2
      simpa using hF
    have hunpaid : 0 ≤ (1 : ℝ) - 1 / factor :=
      sub_nonneg.mpr hpaid
    change 0 ≤ prior * (1 - 1 / factor)
    exact mul_nonneg hE hunpaid
