-- Prove2me | Definitions.Def_NahmiasPerishable_Inventory_Issuance
-- name    : NahmiasPerishable_Inventory_Issuance
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:25:29.667401+00:00
-- url     : https://prove2.me/theorems/1bacc45b-6785-4cce-8a27-a0efa2b96177
-- title:
--   Perishable inventory: Issuance
-- statement:
--   Feasible work-conserving issuing rules, their independently constructed age trajectories and expired units, and FIFO issues for the same replenishment and demand history. Early disposal is not admissible.
-- source:
--   Nahmias (1982), Perishable Inventory Theory: A Review, pp. 681, 689, DOI:10.1287/opre.30.4.680.

import Definitions.Def_NahmiasPerishable_Inventory_FIFO

noncomputable section

namespace NahmiasPerishable.Inventory

/-- Stock before service includes a last, freshly replenished batch. -/
def beforeService {k : ℕ} (x : AgeState k) (q : ℝ) (i : Fin (k+1)) : ℝ :=
  if hi : i.val < k then x.1 ⟨i.val,hi⟩ else q

/-- An issuing rule specifies actual units served from each available age. -/
abbrev IssueRule (k : ℕ) := ℕ → (Fin (k+1) → ℝ) → ℝ → (Fin (k+1) → ℝ)

def FeasibleIssue {k : ℕ} (u : IssueRule k) : Prop :=
  ∀ t a d, (∀ i, 0 ≤ a i) → 0 ≤ d →
    (∀ i, 0 ≤ u t a d i ∧ u t a d i ≤ a i) ∧
      (∑ i, u t a d i) = min d (∑ i, a i)

def issueStep {k : ℕ} (u : IssueRule k) (b : Bool) (t : ℕ)
    (x : AgeState k) (q d : ℝ) : AgeState k :=
  let a := beforeService x q
  let v := u t a (d+x.2)
  ((fun i => a ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩ - v ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩),
    if b then pos (d+x.2-∑ i, a i) else 0)

def issuePath {k : ℕ} (u : IssueRule k) (b : Bool) (x : AgeState k) (q d : ℕ → ℝ) : ℕ → AgeState k
  | 0 => x
  | n+1 => issueStep u b n (issuePath u b x q d n) (q n) (d n)

def issueExpiry {k : ℕ} (u : IssueRule k) (t : ℕ) (x : AgeState k) (q d : ℝ) : ℝ :=
  beforeService x q 0 - u t (beforeService x q) (d+x.2) 0

/-- FIFO's individual issues, determined from older stock already available. -/
def fifoIssue (k : ℕ) : IssueRule k :=
  fun _ a d i => min (a i) (pos (d - ∑ j ∈ Finset.univ.filter (fun j : Fin (k+1) => j < i), a j))

end NahmiasPerishable.Inventory


