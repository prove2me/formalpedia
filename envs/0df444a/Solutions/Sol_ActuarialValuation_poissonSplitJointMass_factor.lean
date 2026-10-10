-- Prove2me | solution 1 for ActuarialValuation.poissonSplitJointMass_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-09T16:37:01.461814+00:00
-- url     : https://prove2.me/submissions/25e66efa-f5da-490d-b610-221135e75b35

import Mathlib
import Definitions.Def_actuarial_poissonSplitJointMass
import Definitions.Def_actuarial_poissonThinnedRate
import Definitions.Def_actuarial_poissonCountMass
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution (rate selection : ℝ) (a b : ℕ) :
    poissonSplitJointMass rate selection a b =
      poissonCountMass (poissonThinnedRate rate selection) a *
        poissonCountMass (poissonThinnedRate rate (1 - selection)) b := by
  have hfactN : (a + b).choose a * Nat.factorial b * Nat.factorial a =
      Nat.factorial (a + b) := by
    simpa [Nat.add_comm b a] using
      (Nat.add_choose_mul_factorial_mul_factorial b a)
  have hfact : (↑((a + b).choose a) : ℝ) * (Nat.factorial b : ℝ) *
      (Nat.factorial a : ℝ) = (Nat.factorial (a + b) : ℝ) := by
    exact_mod_cast hfactN
  have ha : (Nat.factorial a : ℝ) ≠ 0 := by positivity
  have hb : (Nat.factorial b : ℝ) ≠ 0 := by positivity
  have hab : (Nat.factorial (a + b) : ℝ) ≠ 0 := by positivity
  have hexp : Real.exp (-rate) =
      Real.exp (-(rate * selection)) *
        Real.exp (-(rate * (1 - selection))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hratio :
      (Nat.choose (a + b) a : ℝ) / (Nat.factorial (a + b) : ℝ) =
        1 / (Nat.factorial a : ℝ) / (Nat.factorial b : ℝ) := by
    apply (div_eq_iff hab).2
    field_simp [ha, hb]
    nlinarith [hfact]
  calc
    poissonSplitJointMass rate selection a b =
        Real.exp (-rate) * rate ^ a * rate ^ b *
          selection ^ a * (1 - selection) ^ b *
          ((Nat.choose (a + b) a : ℝ) / (Nat.factorial (a + b) : ℝ)) := by
      dsimp [poissonSplitJointMass, poissonCountMass]
      rw [pow_add]
      ring
    _ = Real.exp (-rate) * rate ^ a * rate ^ b *
          selection ^ a * (1 - selection) ^ b *
          (1 / (Nat.factorial a : ℝ) / (Nat.factorial b : ℝ)) := by
      rw [hratio]
    _ = poissonCountMass (poissonThinnedRate rate selection) a *
          poissonCountMass (poissonThinnedRate rate (1 - selection)) b := by
      dsimp [poissonCountMass, poissonThinnedRate]
      rw [hexp, mul_pow, mul_pow]
      ring
