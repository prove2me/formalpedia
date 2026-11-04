-- Prove2me | Definitions.Def_LostSalesOrderUpTo_Asymptotic_Coupling
-- name    : LostSalesOrderUpTo_Asymptotic_Coupling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:49:07.900866+00:00
-- url     : https://prove2.me/theorems/4fd4b23a-d90f-430e-8cc3-6692e6e88c07
-- title:
--   Coupled lost-sales and backorder trajectories
-- statement:
--   Fix a level $S\ge0$ and one demand sample path. The lost-sales system and the backorder system start with zero inventory and an empty order pipeline, place the same order-up-to-$S$ policy, and see the same demands. Lost-sales inventory $X_t^{\mathcal L,S}$ is measured just after delivery; $\mathrm{LOST}_t^{\mathcal L,S}$ counts current unmet units. Backorder net inventory $X_t^{\mathcal B,S}$ is also measured just after delivery, and $\mathrm{BACK}_t^{\mathcal B,S}$ is the end-of-period shortage.
--
--   $$\mathrm{BACK}_t^{\mathcal B,S}=(D_t-X_t^{\mathcal B,S})^+,\qquad\mathrm{LOST}_t^{\mathcal L,S}=(D_t-X_t^{\mathcal L,S})^+.$$
--
--   The backorder recursion retains unmet demand as negative net inventory. Its order each period fills the gap between the current inventory position and $S$; the order arrives after $\tau$ periods. These paths support the pointwise comparison in Lemma 9.
--
--   **Formalization Note** Lean period zero is the paper's period one, and both paths use the same demand coordinates.
-- source:
--   Huh, Janakiraman, Muckstadt & Rusmevichientong, Asymptotic Optimality of Order-up-to Policies in Lost Sales Inventory Systems, working paper, December 4, 2006 (preprint of Management Science 55(3), 2009, DOI 10.1287/mnsc.1080.0945), p. 13, §5, pp. 13–14

import Definitions.Def_LostSalesOrderUpTo_Asymptotic_Backorder

noncomputable section
open MeasureTheory
open scoped NNReal BigOperators

namespace LostSalesOrderUpTo.Asymptotic

/-- The lost-sales stock after the current delivery, before demand. -/
def lostInventory (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) : ℝ≥0 :=
  let s := CappedBaseStock.cbsRun c S S ω t
  s.1 + CappedBaseStock.arrival c s

/-- Demand lost in the current period. -/
def lostUnits (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) : ℝ≥0 :=
  CappedBaseStock.lostSales c (CappedBaseStock.cbsRun c S S ω t) (ω.1 t)

/-- The backorder system's pre-delivery net inventory and delivery pipeline. -/
abbrev BackorderState (L : ℕ) := ℝ × (Fin L → ℝ≥0)

def backorderInitialState (L : ℕ) : BackorderState L := (0, fun _ => 0)

def backorderArrival (c : CappedBaseStock.Parameters) (s : BackorderState c.L) : ℝ≥0 :=
  s.2 ⟨0, lt_of_lt_of_le Nat.zero_lt_one c.leadTime_pos⟩

/-- Order up to S from the pre-delivery inventory position. -/
def backorderOrder (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (s : BackorderState c.L) : ℝ≥0 :=
  Real.toNNReal ((S : ℝ) - (s.1 + ∑ i : Fin c.L, (s.2 i : ℝ)))

/-- Backordered demand reduces net inventory and remains in the state. -/
def backorderStep (c : CappedBaseStock.Parameters) (s : BackorderState c.L)
    (q d : ℝ≥0) : BackorderState c.L :=
  (s.1 + (backorderArrival c s : ℝ) - (d : ℝ),
    fun i => if hi : i.val + 1 < c.L then s.2 ⟨i.val + 1, hi⟩ else q)

/-- The backorder trajectory driven by the same demand path as lost sales. -/
def backorderRun (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) : ℕ → BackorderState c.L
  | 0 => backorderInitialState c.L
  | t + 1 => backorderStep c (backorderRun c S ω t)
      (backorderOrder c S (backorderRun c S ω t)) (ω.1 t)

/-- Net inventory just after delivery. -/
def backorderInventory (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) : ℝ :=
  (backorderRun c S ω t).1 + (backorderArrival c (backorderRun c S ω t) : ℝ)

/-- Units backordered at the end of a period. -/
def backorderUnits (c : CappedBaseStock.Parameters) (S : ℝ≥0)
    (ω : CappedBaseStock.Sample) (t : ℕ) : ℝ :=
  max ((ω.1 t : ℝ) - backorderInventory c S ω t) 0

end LostSalesOrderUpTo.Asymptotic


