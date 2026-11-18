-- Prove2me | Definitions.Def_Kyprianou_Ch09_RunningSup
-- name    : Kyprianou_Ch09_RunningSup
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:13:28.711353+00:00
-- url     : https://prove2.me/theorems/fde0fce3-aed6-4012-82be-6e00bd5e324a
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner RunningSup
-- statement:
--   Running-maximum, first-passage and extremum-related source foundations. This source Definition module provides the actual declarations: runningSup. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_Pathwise
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- Genuine prefix supremum of the original path, including t=0. -/
noncomputable def runningSup (X : ℝ → ℝ) (t : ℝ) : ℝ :=
  sSup (X '' Set.Icc 0 t)

/-- The reflected-value path obeys the deterministic drift envelope. -/
theorem runningSup_driftMinus_le (d t : ℝ) (S : ℝ → ℝ)
    (hd : 0 ≤ d) (ht : 0 ≤ t)
    (hS : ∀ s, 0 ≤ s → 0 ≤ S s) :
    runningSup (driftMinus d S) t ≤ d * t := by
  unfold runningSup
  apply csSup_le
  · refine ⟨driftMinus d S 0, ?_⟩
    exact ⟨0, ⟨le_refl 0, ht⟩, rfl⟩
  · rintro z ⟨s, hs, rfl⟩
    exact driftMinus_prefix_le d t S hd ht hS s hs

/-- This is the source-faithful pathwise q≥d estimate for the Russian option,
derived directly from the bounded-variation Lévy path representation. -/
theorem russian_discounted_reward_le_initial
    (q d x t : ℝ) (S : ℝ → ℝ)
    (hd : 0 ≤ d) (hq : d ≤ q)
    (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hS : ∀ s, 0 ≤ s → 0 ≤ S s) :
    Real.exp (-q * t + max x (runningSup (driftMinus d S) t)) ≤
      Real.exp x := by
  apply discounted_max_bound q d x t (runningSup (driftMinus d S) t) hq hd hx ht
  exact runningSup_driftMinus_le d t S hd ht hS

end Kyprianou.Ch09.B1


