-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Cycles
-- name    : NahmiasPerishable_Inventory_Cycles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:25:48.042013+00:00
-- url     : https://prove2.me/theorems/f370994b-cf8a-4cd7-814e-5150fea047ea
-- title:
--   Perishable inventory: Cycles
-- statement:
--   Exact deterministic fixed-life and exponential-decay cycles, survival-based fluid inventory, one-period lifetime control and newsvendor objectives, and the iid demand-sum convolution.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 682, 684, 690, 698–699, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_Threshold

open MeasureTheory Set Filter Topology
noncomputable section

namespace NahmiasPerishable.Inventory

/-- Fixed-lifetime cycle terminates at depletion or expiration. -/
def cycleDuration (rate life Q : ℝ) : ℝ := min (Q/rate) life

def fixedCycleCost (K h rate life Q : ℝ) : ℝ :=
  K / cycleDuration rate life Q + h*(Q-rate*cycleDuration rate life Q/2)

/-- Exact exponential-decay trajectory ending at zero, pp. 698–699. -/
def decayStock (rate theta T u : ℝ) : ℝ := rate*(Real.exp (theta*(T-u))-1)/theta

def decayProfit (K c h rate theta price T : ℝ) : ℝ :=
  price*rate - (K+c*decayStock rate theta T 0 + h*∫ u in (0 : ℝ)..T, decayStock rate theta T u)/T

/-- Fluid inventory from survival S and constant demand: surviving initial stock less surviving withdrawals. -/
def survivalStock (S : ℝ → ℝ) (Q rate t : ℝ) : ℝ :=
  S t * (Q - ∫ u in (0 : ℝ)..t, rate / S u)

/-- Inventory with one-period lifetime; only backlogged obligations cross a period boundary. -/
def singlePeriodControl (μ : Measure ℝ) (backorder : Bool) (c h p theta alpha : ℝ) : ShockControl ℝ where
  shock := μ
  transfer := fun x q d => if backorder then -pos (d-x-q) else 0
  stage := fun x q => (c*q : ℝ) + stockCost μ (h+theta) p (x+q)
  terminal := fun _ => 0
  discount := alpha

/-- Single-period objective in the inventory-position reformulation. A backlog carried to
another period costs its purchase price at the next epoch. -/
def singlePeriodNews (μ : Measure ℝ) (b : Bool) (c h p theta alpha : ℝ) (more : Bool) (z : ℝ) : EReal :=
  (c*z : ℝ) + stockCost μ (h+theta) (p + if b && more then alpha*c else 0) z

/-- CDF of the sum of m iid demands, without imposing a grid or bounded support. -/
def sumCDF (μ : Measure ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  ((demandPaths μ m) {d | (∑ i, d i) ≤ u}).toReal

def convolutionIntegral (μ : Measure ℝ) (m : ℕ) (z : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..z, sumCDF μ m u

end NahmiasPerishable.Inventory


