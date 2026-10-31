-- Prove2me | Definitions.Def_KashUpgrade_IsOptimalThreshold
-- name    : KashUpgrade_IsOptimalThreshold
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:21:11.533436+00:00
-- url     : https://prove2.me/theorems/ba72cac0-21ca-4f49-83c0-b59eb6686472
-- title:
--   An optimal solution of problem (12)
-- statement:
--   A threshold vector is optimal for problem (12) if it is feasible and no feasible vector has a larger objective value.
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), (12), p.14

import Mathlib
import Definitions.Def_KashUpgrade_thresholdObjective
import Definitions.Def_KashUpgrade_ThresholdFeasible

namespace KashUpgrade

/-- **An optimal solution of problem (12).** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), (12), p.14. -/
def IsOptimalThreshold (f : ℝ → ℝ) (ζ : ENNReal) (p c : ℝ) (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ)
    (θ : ℕ → ℝ) : Prop :=
  ThresholdFeasible ζ p j n θ ∧
    ∀ θ', ThresholdFeasible ζ p j n θ' →
      thresholdObjective f c s A j n θ' ≤ thresholdObjective f c s A j n θ

end KashUpgrade


