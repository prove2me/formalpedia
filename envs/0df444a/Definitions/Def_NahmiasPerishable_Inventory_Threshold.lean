-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Threshold
-- name    : NahmiasPerishable_Inventory_Threshold
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:25:05.358281+00:00
-- url     : https://prove2.me/theorems/bd6f8a7e-9ed8-44c4-bfec-98414ca7eff5
-- title:
--   Perishable inventory: Threshold
-- statement:
--   Canonical physical states, nonperishable salvage-adjusted costs, the backorder quantile and the lost-sales least minimizing critical level, and the linear-cost fixed-life specialization.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 684–685, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_FIFO

open MeasureTheory Set
noncomputable section

namespace NahmiasPerishable.Inventory

/-- The associated nonperishable transfer. -/
def nonperishable (backorder : Bool) (z d : ℝ) : ℝ :=
  if backorder then z-d else pos (z-d)

/-- One-period cost with terminal salvage for the associated nonperishable problem. -/
def adjustedCost (D : Demand) (backorder : Bool) (c h p alpha z : ℝ) : EReal :=
  (c*z : ℝ) + stockCost D.law h p z +
  (alpha : EReal) * expectation D.law (fun d => (-c * nonperishable backorder z d : ℝ))

/-- Lowest minimizing critical number in the lost-sales associated nonperishable model;
backorders use the review's printed lower generalized quantile. -/
def critical (D : Demand) (backorder : Bool) (c h p alpha : ℝ) : EReal :=
  if backorder then lowerQuantile D.law ((p-(1-alpha)*c)/(p+h))
  else sInf ((fun z : ℝ => (z : EReal)) ''
    {z | 0 ≤ z ∧ ∀ w : ℝ, 0 ≤ w → adjustedCost D false c h p alpha z ≤ adjustedCost D false c h p alpha w})

/-- The linear-cost fixed-life model, retaining all nonnegative cost choices. -/
def linearModel (k : ℕ) (D : Demand) (b : Bool) (a : Accounting) (t : Terminal)
    (c h p theta alpha : ℝ) : FixedLife k :=
  ⟨D,b,a,t,c,theta,alpha,stockCost D.law h p⟩

/-- A physically possible starting state. Existing backlogs have no surviving physical batch. -/
def canonical {k : ℕ} (b : Bool) (x : AgeState k) : Prop :=
  physical x ∧ (x.2 > 0 → ∀ i, x.1 i = 0) ∧ (b = false → x.2 = 0)

end NahmiasPerishable.Inventory


