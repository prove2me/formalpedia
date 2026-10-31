-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_FIFO
-- name    : NahmiasPerishable_Inventory_FIFO
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:24:31.322819+00:00
-- url     : https://prove2.me/theorems/5fc35b10-5eea-4bb7-89ce-f49120e54e52
-- title:
--   Perishable inventory: FIFO
-- statement:
--   Oldest-first physical stock and a separate nonexpiring backlog, FIFO service/aging, actual current and future batch expiration, the printed G recursion, and the two accounting models. Coordinate perturbations clear backlog before evaluating a canonical policy.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 682–686, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_Control

open MeasureTheory Set
open scoped ENNReal
noncomputable section

namespace NahmiasPerishable.Inventory

/-- Stock by remaining lifetime, oldest first, plus a separate nonexpiring backlog. -/
abbrev AgeState (k : ℕ) := (Fin k → ℝ) × ℝ

def physical {k : ℕ} (x : AgeState k) : Prop := (∀ i, 0 ≤ x.1 i) ∧ 0 ≤ x.2

def total {k : ℕ} (x : AgeState k) : ℝ := (∑ i, x.1 i) - x.2

/-- End-of-period unserved oldest stock. Backlogs are served before new demand. -/
def expires {k : ℕ} (x : AgeState k) (d : ℝ) : ℝ :=
  if hk : 0 < k then pos (x.1 ⟨0,hk⟩ - (d+x.2)) else 0

/-- Full FIFO step for lifetime k+1, with shortage treatment supplied by `backorder`. -/
def fifo (backorder : Bool) {k : ℕ} (x : AgeState k) (y d : ℝ) : AgeState k :=
  ((fun i => if hi : i.val+1 < k then
      pos (x.1 ⟨i.val+1,hi⟩ - pos (d+x.2 - ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.val ≤ i.val), x.1 j))
    else pos (y - pos (d - total x))),
   if backorder then pos (d-total x-y) else 0)

/-- Actual stock trajectory under a specified fresh replenishment sequence. -/
def trajectory (backorder : Bool) {k : ℕ} (x : AgeState k) (q d : ℕ → ℝ) : ℕ → AgeState k
  | 0 => x
  | n+1 => fifo backorder (trajectory backorder x q d n) (q n) (d n)

/-- Oldest-first depletion of a list of batches, before their aging step. -/
def consume : List ℝ → ℝ → List ℝ
  | [], _ => []
  | a::xs, d => pos (a-d) :: consume xs (pos (d-a))

/-- A tracked fresh batch after all its lifetime demands and the scheduled expiry of older batches.
Future orders are younger and cannot consume demand ahead of this batch. -/
def batchResidual : List ℝ → List ℝ → ℝ
  | xs, [] => xs.getLastD 0
  | xs, d::ds => batchResidual ((consume xs d).drop 1) ds

/-- Physical expiration of the fresh batch, observed after the last demand and before discarding it. -/
def batchExpiry {k : ℕ} (x : AgeState k) (y : ℝ) (d : Fin (k+1) → ℝ) : ℝ :=
  let ds := List.ofFn (fun i => d i + if i.val = 0 then x.2 else 0)
  let stocks := List.ofFn x.1 ++ [y]
  let depleted := (ds.take k).foldl (fun xs t => (consume xs t).drop 1) stocks
  (consume depleted (d ⟨k, Nat.lt_succ_self k⟩ + if k = 0 then x.2 else 0)).getLastD 0

/-- Recursion on newest-first coordinates in the review's G_n formula. -/
def outdateCDF (D : Demand) : List ℝ → ℝ
  | [] => 0
  | [a] => cdf D.law a
  | a::b::xs => ∫ v in (0 : ℝ)..a,
      outdateCDF D ((v+b)::xs) * (D.density (a-v)).toReal
termination_by xs => xs.length

/-- Future-expiration charge for a fresh order, pp. 684 and 686. -/
def futureCharge (D : Demand) {k : ℕ} (x : AgeState k) (y : ℝ) : ℝ :=
  let older := consume (List.ofFn x.1) x.2
  let fresh := pos (y - pos (x.2 - ∑ i, x.1 i))
  ∫ u in (0 : ℝ)..fresh, outdateCDF D (u :: older.reverse)

inductive Accounting | fries | nahmias deriving DecidableEq
inductive Terminal | zero | salvage deriving DecidableEq

/-- Model data: no desired theorem conclusion is a field. -/
structure FixedLife (k : ℕ) where
  demand : Demand
  backorder : Bool
  accounting : Accounting
  terminalRule : Terminal
  c : ℝ
  theta : ℝ
  alpha : ℝ
  R : ℝ → EReal

/-- The two displayed Bellman models, including their different charge timing. -/
def FixedLife.control {k : ℕ} (M : FixedLife k) : ShockControl (AgeState k) where
  shock := M.demand.law
  transfer := fifo M.backorder
  stage := fun x y => (M.c*y : ℝ) + M.R (total x+y) +
    (M.theta * (match M.accounting with
      | .fries => ∫ d, expires x d ∂M.demand.law
      | .nahmias => futureCharge M.demand x y) : ℝ)
  terminal := fun x => match M.terminalRule with
    | .zero => 0
    | .salvage => (-M.c * total x : ℝ)
  discount := M.alpha

/-- Cancel outstanding demand against physical stock before evaluating a policy.
This gives the same net inventory as the signed-newest-coordinate convention. -/
def clearBacklog {k : ℕ} (x : AgeState k) : AgeState k :=
  ((fun i => pos (x.1 i - pos (x.2 -
    ∑ j ∈ Finset.univ.filter (fun j : Fin k => j < i), x.1 j))),
   pos (x.2 - ∑ i, x.1 i))

/-- Coordinate section of a policy; added stock first clears any outstanding demand.
The policy is evaluated on a canonical stock/backlog state even at negative net inventory. -/
def ageSection {k : ℕ} (q : AgeState k → ℝ) (x : AgeState k) (i : Fin k) (z : ℝ) : ℝ :=
  q (clearBacklog (Function.update x.1 i z, x.2))

end NahmiasPerishable.Inventory


