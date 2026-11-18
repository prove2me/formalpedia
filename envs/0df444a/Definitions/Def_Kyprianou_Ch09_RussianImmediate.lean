-- Prove2me | Definitions.Def_Kyprianou_Ch09_RussianImmediate
-- name    : Kyprianou_Ch09_RussianImmediate
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-17T15:14:15.529208+00:00
-- url     : https://prove2.me/theorems/d25c2322-f5f8-4d8e-8ec2-e7eebadc4a81
-- title:
--   Kyprianou (2006) Chapter 9 canonical source owner RussianImmediate
-- statement:
--   Immediate-exercise and barrier cases for the Russian stopping problem. This source Definition module provides the actual declarations: russianRandomReward. The binding scopes, mathematical hypotheses and exact meaning are given by the complete Lean source included here; no published theorem proof is assumed.
-- source:
--   A. E. Kyprianou (2006), first edition, Chapter 9, printed pp. 239–270, physical PDF pp. 247–278; Chapter 3 completed-natural-filtration provider as cited in source imports.

import Mathlib
import Definitions.Def_Kyprianou_Ch09_RunningSup
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace Kyprianou.Ch09.B1

/-- Discounted original running-maximum reward on a stochastic path.
A finite random time (including any almost-surely finite stopping time)
is a measurable map to nonnegative time; the pathwise bound below even
holds without using its adaptedness. -/
noncomputable def russianRandomReward {Ω : Type*}
    (q d x : ℝ) (S : ℝ → Ω → ℝ) (τ : Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp (-q * τ ω +
    max x (runningSup (driftMinus d (fun s => S s ω)) (τ ω)))

/-- Pathwise original-model reward dominance at every finite random time,
including the time-zero case and finite-activity jump processes. -/
theorem russianRandomReward_le_immediate {Ω : Type*}
    (q d x : ℝ) (S : ℝ → Ω → ℝ) (τ : Ω → ℝ)
    (hd : 0 ≤ d) (hq : d ≤ q) (hx : 0 ≤ x)
    (hτ : ∀ ω, 0 ≤ τ ω)
    (hS : ∀ ω s, 0 ≤ s → 0 ≤ S s ω) :
    ∀ ω, russianRandomReward q d x S τ ω ≤ Real.exp x := by
  intro ω
  unfold russianRandomReward
  exact russian_discounted_reward_le_initial q d x (τ ω)
    (fun s => S s ω) hd hq hx (hτ ω) (hS ω)

/-- Immediate stopping is a witness attaining the undiscounted reward
when X_0=0 and the initial reflected state is x≥0. -/
theorem russianImmediateReward_eq {Ω : Type*}
    (q d x : ℝ) (S : ℝ → Ω → ℝ) (ω : Ω)
    (hx : 0 ≤ x) (hXzero : S 0 ω = 0) :
    russianRandomReward q d x S (fun _ => 0) ω = Real.exp x := by
  unfold russianRandomReward runningSup driftMinus
  simp [Set.Icc_self, hXzero, max_eq_left hx]

end Kyprianou.Ch09.B1


