-- Prove2me | solution 1 for ActuarialValuation.finiteHattendorffVariance_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T08:49:14.116228+00:00
-- url     : https://prove2.me/submissions/c681efd9-7157-436a-a637-02d6712a836e

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_actuarial_finiteMortalityVariance

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (X : Ω → ℝ) (c : ℝ) (hsum : (∑ ω : Ω, w ω) = 1) :
    finiteMortalityVariance w (fun ω => c + X ω) =
      finiteMortalityVariance w X := by
  have hmean :
      (∑ ω : Ω, w ω * (c + X ω)) =
        c + (∑ ω : Ω, w ω * X ω) := by
    calc
      (∑ ω : Ω, w ω * (c + X ω)) =
          ∑ ω : Ω, (c * w ω + w ω * X ω) := by
            apply Finset.sum_congr rfl
            intro ω hω
            ring
      _ = c * (∑ ω : Ω, w ω) + (∑ ω : Ω, w ω * X ω) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ = c + (∑ ω : Ω, w ω * X ω) := by
        rw [hsum]
        ring
  unfold finiteMortalityVariance
  rw [hmean]
  apply Finset.sum_congr rfl
  intro ω hω
  ring
