-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_AllocationSurvival
-- name    : NahmiasPerishable_Inventory_AllocationSurvival
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:00.223342+00:00
-- url     : https://prove2.me/theorems/45349828-864b-4106-8acf-563cfe301507
-- title:
--   Perishable inventory: AllocationSurvival
-- statement:
--   Feasible old/young allocation budgets, bounded expected expiration and extended nonnegative expected shortage for arbitrary nonnegative demand marginals, and the surviving subset of a finite population with given lifetimes.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 696–697, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section

namespace NahmiasPerishable.Inventory
attribute [local instance] Classical.propDecidable

/-- Fixed total budgets of expiring and younger stock. -/
def Allocation {n : ℕ} (A B : ℝ) (a b : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ a i ∧ 0 ≤ b i) ∧ (∑ i, a i) = A ∧ (∑ i, b i) = B

def allocationOutdate {n : ℕ} (μ : Fin n → Measure ℝ) (a : Fin n → ℝ) : ℝ :=
  ∑ i, ∫ d, pos (a i-d) ∂μ i

def allocationShortage {n : ℕ} (μ : Fin n → Measure ℝ) (a b : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ i, ∫⁻ d, ENNReal.ofReal (pos (d-a i-b i)) ∂μ i

/-- The actual population surviving at time t, excluding demand. -/
def survivors {Ω : Type*} {n : ℕ} (T : Fin n → Ω → ℝ) (t : ℝ) (ω : Ω) : Finset (Fin n) :=
  Finset.univ.filter (fun i => t < T i ω)

end NahmiasPerishable.Inventory


