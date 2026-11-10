-- Prove2me | Definitions.Def_AssadiSemiStreaming_Greedy_DelayedWalk
-- name    : AssadiSemiStreaming_Greedy_DelayedWalk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:39:38.713829+00:00
-- url     : https://prove2.me/theorems/db038376-658c-4361-aadc-3d1dd1ea8327
-- title:
--   Label-derived delayed reflected walks and buckets
-- statement:
--   Set L=16m³, D=2mL, P=L+D+1 and C=2D times the product of the reduced denominators of μ(1),…,μ(m). Labels are all C^P tuples. Their first coordinate chooses the starting state from consecutive intervals of sizes Cμ(i); their second coordinate chooses a delay uniformly from {1,…,D}. At time t≥d the coordinate t+2 chooses a down step when its one-based symbol is at most C/2, and an up step otherwise. The reflected walk uses the same start and delay and the opposite step rule. Both remain fixed before d, after absorption, and beyond time D+L. Their maximum is over times 1,…,D+L. Maximum time is the first occurrence at or after d, including time d when the start is already the maximum, as in Eq. (9). Bucket (j,t) consists of all labels reaching zero by time d+L, with maximum j and maximum time t. For an absorbed walk this is exactly the conjunction of L-restriction and zero termination. Left buckets use the ordinary walk and right buckets the reflected walk. Default zero values outside meaningful finite minima and coordinates are irrelevant for m≥1 and in-range times.
-- source:
--   Assadi, Jiang and Xiang (2026), Semi-Streaming Matching in a Single Pass II: Greedy is Optimal, supplied STOC 2027 submission manuscript (published basis per source.meta.json; SHA-256 8f66fdf7cb422cdd3accbae4cb24ebc61dd7ddb2e5e2d5422f4de6fc3f99395d), Eq. (9), printed p. 13 / PDF 15; Definition 6.1 and Remark 6.2, printed pp. 16–17 / PDF 18–19

import Definitions.Def_AssadiSemiStreaming_Greedy_Blueprint
import Definitions.Def_AssadiSemiStreaming_Greedy_WalkLaws

namespace AssadiSemiStreaming.Greedy

def lengthBound (m : ℕ) : ℕ := 16 * m ^ 3
def delayBound (m : ℕ) : ℕ := 2 * m * lengthBound m
def labelLength (m : ℕ) : ℕ := lengthBound m + delayBound m + 1

/-- The explicit admissible alphabet size of Remark 6.2. -/
noncomputable def alphabetSize (m : ℕ) : ℕ :=
  2 * delayBound m * ∏ i ∈ Finset.Icc 1 m, (mu m i).den

abbrev WalkLabel (m : ℕ) := Label (labelLength m) (alphabetSize m)

/-- Read a one-based coordinate and symbol; outside the label return zero.
Only in-range coordinates are read before the horizon. -/
def coordinate {P C : ℕ} (x : Label P C) (i : ℕ) : ℕ :=
  if h : i - 1 < P then (x ⟨i - 1, h⟩).val + 1 else 0

noncomputable def startState (m : ℕ) (x : WalkLabel m) : ℕ :=
  (((Finset.Icc 1 m).filter (fun i =>
    (coordinate x 1 : ℚ) ≤ (alphabetSize m : ℚ) * ∑ k ∈ Finset.Icc 1 i, mu m k)).min).getD 0

noncomputable def delay (m : ℕ) (x : WalkLabel m) : ℕ :=
  (coordinate x 2 - 1) / (alphabetSize m / delayBound m) + 1

/-- Time zero is an unused copy of time one. After D+L the finite walk is held fixed. -/
noncomputable def delayedState (m : ℕ) (reflected : Bool) (x : WalkLabel m) : ℕ → ℕ
  | 0 => startState m x
  | t + 1 =>
    let v := delayedState m reflected x t
    if t < delay m x ∨ delayBound m + lengthBound m ≤ t ∨ v = 0 ∨ v = 2 * m then v
    else if (coordinate x (t + 2) ≤ alphabetSize m / 2) ≠ (reflected = true)
      then v - 1 else v + 1

noncomputable def walkMaximum (m : ℕ) (r : Bool) (x : WalkLabel m) : ℕ :=
  (Finset.Icc 1 (delayBound m + lengthBound m)).sup (delayedState m r x)

/-- First occurrence in the inner walk, so an initial maximum has time d. -/
noncomputable def maximumTime (m : ℕ) (r : Bool) (x : WalkLabel m) : ℕ :=
  (((Finset.Icc (delay m x) (delayBound m + lengthBound m)).filter
    (fun t => delayedState m r x t = walkMaximum m r x)).min).getD 0

noncomputable def bucket (m : ℕ) (r : Bool) (j t : ℕ) : Finset (WalkLabel m) := by
  classical
  exact Finset.univ.filter (fun x =>
    delayedState m r x (delay m x + lengthBound m) = 0 ∧
    walkMaximum m r x = j ∧ maximumTime m r x = t)

end AssadiSemiStreaming.Greedy


