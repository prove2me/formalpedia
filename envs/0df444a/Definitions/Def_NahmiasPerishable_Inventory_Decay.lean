-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Decay
-- name    : NahmiasPerishable_Inventory_Decay
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:27:20.135789+00:00
-- url     : https://prove2.me/theorems/3980a3db-0596-4705-8ea1-db1e95e29e1f
-- title:
--   Perishable inventory: Decay
-- statement:
--   Lost-sales and backlog-preserving proportional decay, its concrete Bellman and myopic objectives, measurable history policies and infinite discounted physical costs, and the actual Emmons (s,S) transition and invariant law.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 699–700, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_Cycles

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
noncomputable section

namespace NahmiasPerishable.Inventory

/-- Surviving fraction gamma applies to positive stock only; obligations do not decay. -/
def decayTransfer (b : Bool) (gamma z d : ℝ) : ℝ :=
  gamma*pos (z-d) - if b then pos (d-z) else 0

def decayControl (D : Demand) (b : Bool) (c h p alpha gamma : ℝ) : ShockControl ℝ where
  shock := D.law
  transfer := fun x q d => decayTransfer b gamma (x+q) d
  stage := fun x q => (c*q : ℝ) + stockCost D.law h p (x+q)
  terminal := fun x => (-c*x : ℝ)
  discount := alpha

/-- The immediate, salvage-adjusted myopic objective, independently of dynamic optimality. -/
def decayMyopic (D : Demand) (b : Bool) (c h p alpha gamma z : ℝ) : EReal :=
  (c*z : ℝ) + stockCost D.law h p z +
    (alpha : EReal)*expectation D.law (fun d => (-c*decayTransfer b gamma z d : ℝ))

/-- All nonanticipating measurable order rules, based on the demands already observed. -/
structure HistoryPolicy where
  rule : (t : ℕ) → (Fin t → ℝ) → ℝ
  measurable_rule : ∀ t, Measurable (rule t)
  nonneg : ∀ t h, 0 ≤ rule t h

def hist (d : ℕ → ℝ) (t : ℕ) : Fin t → ℝ := fun i => d i

def controlledStock (b : Bool) (gamma x : ℝ) (π : HistoryPolicy) (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => x
  | t+1 => decayTransfer b gamma (controlledStock b gamma x π d t + π.rule t (hist d t)) (d t)

/-- Infinite discounted operational cost, with no terminal salvage at infinity. -/
def decayPolicyCost (D : Demand) (b : Bool) (c h p alpha gamma x : ℝ) (π : HistoryPolicy) : ℝ≥0∞ :=
  ∫⁻ d, ∑' t : ℕ, ENNReal.ofReal (alpha^t *
    (c*π.rule t (hist d t) + h*pos (controlledStock b gamma x π d t + π.rule t (hist d t)-d t) +
      p*pos (d t-controlledStock b gamma x π d t-π.rule t (hist d t))))
    ∂Measure.infinitePi (fun _ : ℕ => D.law)

/-- (s,S) ordering and then deterministic decay followed by demand, p. 700. -/
def emmonsTransfer (s S theta x d : ℝ) : ℝ :=
  let z := if x ≤ s then S else x
  Real.exp (-theta)*pos z - pos (-z) - d

/-- Invariance of the actual transition, not of a supplied differential equation. -/
def emmonsInvariant (D : Demand) (s S theta : ℝ) (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧
    (ν.prod D.law).map (fun xd => emmonsTransfer s S theta xd.1 xd.2) = ν

end NahmiasPerishable.Inventory


