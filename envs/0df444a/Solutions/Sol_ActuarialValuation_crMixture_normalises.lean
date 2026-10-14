-- Prove2me | solution 1 for ActuarialValuation.crMixture_normalises
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-12T14:13:44.996609+00:00
-- url     : https://prove2.me/submissions/d8c8f8a0-ae2e-4eb9-94ad-a273ec439743

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_crMixWeights

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ActuarialValuation

theorem solution {n : ℕ} (p q : Fin n→ℝ) (mix : ℝ) (hp : (∑ i : Fin n,p i)=1) (hq : (∑ i : Fin n,q i)=1) : (∑ i : Fin n, crMixWeights p q mix i)=1 := by
  simp only [crMixWeights, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp, hq]
  ring
