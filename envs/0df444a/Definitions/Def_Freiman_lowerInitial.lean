-- Prove2me | Definitions.Def_Freiman_lowerInitial
-- name    : Freiman_lowerInitial
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:47:56.532199+00:00
-- url     : https://prove2.me/theorems/9166c5a8-d6c9-4170-8122-760e8d99846d
-- title:
--   Freiman lower construction: lowerInitial
-- statement:
--   The 23 fixed roots, the four unbounded initial families and raw H intervals, explicit periodic limits, the six actual entry labels, and the marked-root priority.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), Part II; parts/lower_core.tex and the cited continuation sections.

import Definitions.Def_Freiman_lowerCover

namespace Freiman
def lowerPeriod : List ℕ+ := [3,1,3,1,2,1]
def lowerRepeat (w : List ℕ+) (n : ℕ) : List ℕ+ := (List.replicate n w).flatten
def lowerFixedRoots : List LowerPair :=
  [([3],[3]),
   ([3,2,1],[4,3,1]),
   ([3,2,1,1,2],[4,3,2,2]),
   ([3,2,1,1,3],[4,3,2,3]),
   ([3,2,1,1,3],[4,3,2,2]),
   ([3,1,3,1,2],[3,1,2,1,2]),
   ([3,1,3,1,1],[3,1,2,1,2]),
   ([3,1,3,1,1],[3,1,2,1,1]),
   ([3,1,3,1,2],[3,1,2,2]),
   ([3,1,3,1,1],[3,1,2,2]),
   ([3,1,3,1,1],[3,1,2,3]),
   ([3,1,3,2],[3,1,2,2]),
   ([3,1,3,3],[3,1,2,2]),
   ([3,1,3,2],[3,1,2,3]),
   ([3,1,3,3],[3,1,2,3]),
   ([3,1,3,2],[3,1,2,1]),
   ([3,1,3,1,1],[3,1,3,1,2]),
   ([3,1,3,1,1],[3,1,3,1,1]),
   ([3,1,3,2],[3,1,3,1,2]),
   ([3,1,3,2],[3,1,3,1,1]),
   ([3,1,3,3],[3,1,3,1,1]),
   ([3,1,3,2],[3,1,3,2]),
   ([3,1,3,2],[3,1,3,3])]
inductive LowerInitialFamily where
 | A | B | C | auxB
 deriving DecidableEq

def lowerFamilyPair (f : LowerInitialFamily) (n k p : ℕ) : LowerPair :=
  let s := lowerRepeat lowerPeriod n
  let ks := List.replicate (k+1) (3 : ℕ+)
  let ps := List.replicate (p+1) (3 : ℕ+)
  match f with
  | .A => ([3,2,1,1] ++ s ++ [3,1] ++ ks, [4,3,2,2] ++ s ++ ks)
  | .B => ([3,2,1,1] ++ s ++ [3,1,3,1,2] ++ List.replicate k 3,
           [4,3,2,2] ++ s ++ [3,1] ++ ks)
  | .C => ([3,2,1,1] ++ s ++ [3,1,3,1,2] ++ ks ++ [1] ++ ps,
           [4,3,2,2] ++ s ++ [3,1] ++ ks ++ [2,1] ++ ps)
  | .auxB => ([3,2,1,1] ++ lowerRepeat lowerPeriod (n+1) ++ [3,1,2],
              [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1) ++ [3])
noncomputable def lowerFamilyH (f : LowerInitialFamily) (n k p : ℕ) : Set ℝ :=
  let v := lowerNormalize (lowerFamilyPair f n k p)
  let c₁ : List ℕ+ := if f = .auxB ∨ (f = .B ∧ k = 0) then [1,3] else [1,2,1,3]
  let x := 4 + prefixEval (v.1 ++ [3,1,2,1,3]) lowerTau +
                prefixEval (v.2 ++ [2,1,3]) lowerTau
  let y := 4 + prefixEval (v.1 ++ c₁) lowerTau +
                prefixEval (v.2 ++ [1,2,1,3]) lowerTau
  Set.Icc (min x y) (max x y)
def lowerPeriodicStream (w p : List ℕ+) (n : ℕ) : ℕ+ :=
  if n < w.length then w.getD n 1 else p.getD ((n-w.length) % p.length) 1
def lowerBiSequence (l r : ℕ → ℕ+) (i : ℤ) : ℕ+ :=
  if i = 0 then 4 else if i < 0 then l (i.natAbs - 1) else r (i.toNat - 1)
def lowerPeriodicSequence (p : LowerPair) (period : List ℕ+) : ℤ → ℕ+ :=
  lowerBiSequence (lowerPeriodicStream p.1 period) (lowerPeriodicStream p.2 period)
def lowerCFSequence : ℤ → ℕ+ :=
  lowerPeriodicSequence ([3,2,1,1],[4,3,2,2]) lowerPeriod
def lowerFamilyLimitPair (f : LowerInitialFamily) (n k : ℕ) : LowerPair :=
  let s := lowerRepeat lowerPeriod n
  let ks := List.replicate (k+1) (3 : ℕ+)
  match f with
  | .A => ([3,2,1,1] ++ s ++ [3,1], [4,3,2,2] ++ s)
  | .B => ([3,2,1,1] ++ s ++ [3,1,3,1,2], [4,3,2,2] ++ s ++ [3,1])
  | .C => ([3,2,1,1] ++ s ++ [3,1,3,1,2] ++ ks ++ [1],
           [4,3,2,2] ++ s ++ [3,1] ++ ks ++ [2,1])
  | .auxB => ([3,2,1,1] ++ lowerRepeat lowerPeriod (n+1) ++ [3,1,2],
              [4,3,2,2] ++ lowerRepeat lowerPeriod (n+1) ++ [3])
noncomputable def lowerFamilyLimitValue (f : LowerInitialFamily) (n k : ℕ) : ℝ :=
  localValue (lowerPeriodicSequence (lowerFamilyLimitPair f n k) [3]) 0
def lowerExplicitValue (t : ℝ) : Prop := t = cF ∨
  ∃ (f : LowerInitialFamily) (n k : ℕ), f ≠ .auxB ∧ t = lowerFamilyLimitValue f n k
def lowerInitialSet : Set ℝ := {t | lowerExplicitValue t ∨
  (∃ p ∈ lowerFixedRoots, t ∈ lowerCover p) ∨
  ∃ (f : LowerInitialFamily) (n k p : ℕ), t ∈ lowerFamilyH f n k p}
def lowerEntryLabels : List LowerLabel :=
  [([1],[]),([2],[1]),([3],[1]),([2],[2]),([2],[3]),([3],[2])]
def lowerBridgeLabels (f : LowerInitialFamily) (n : ℕ) : List LowerPair :=
  match f with
  | .A => if n = 0 then
     [([1,2,1,3,3],[1,2,1,3,3]),([1,2,1,3,3,3,3],[1,2,1,3,3,3,3]),
      ([1,2,1,3,1,3,1,2,2],[1,2,1,2,1,3,1,3,2]),
      ([1,2,1,3,3,3],[1,2,1,3,3,3]),([1,2,1,3],[1,2,1,3])]
     else [([1,2,1,3,3],[1,2,1,3,3]),
      ([1,2,1,3,1,3,1,2,1],[1,2,1,2,1,3,1,3,2]),
      ([1,2,1,3,3,3],[1,2,1,3,3,3]),([1,2,1,3],[1,2,1,3])]
  | .B => [([1,3],[1,2])]
  | _ => []
noncomputable def lowerPhysicalAdd (p d : LowerPair) : LowerPair := by
  classical
  let q := lowerNormalize p
  exact (q.1 ++ d.1,q.2 ++ d.2)
noncomputable def lowerInitialBaseSelected (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ) : Prop :=
  t ∈ lowerFamilyH f n k p ∧
  (f = .B ∨ ¬ ∃ n' k' p', t ∈ lowerFamilyH .B n' k' p')
noncomputable def lowerInitialSafeBound (t : ℝ) (f : LowerInitialFamily) (n k p : ℕ) : Prop :=
  let v := lowerNormalize (lowerFamilyPair f n k p)
  let e := lowerEndpoint (v.1 ++ [1,2],v.2 ++ [1,2]) (decide (v.1.length % 2 = 0))
  ((f = .C → p = 0 → if v.1.length % 2 = 0 then t ≤ e else e ≤ t) ∧
   (((f = .A ∧ k = 0) ∨ (f = .B ∧ k = 0)) →
      if v.1.length % 2 = 0 then t ≤ e else e ≤ t))
noncomputable def lowerInitialRoot (t : ℝ) (r : LowerPair) : Prop :=
  r ∈ lowerFixedRoots ∨ ∃ (f : LowerInitialFamily) (n k p : ℕ),
    lowerInitialBaseSelected t f n k p ∧
    (let b := lowerFamilyPair f n k p
     (∃ l ∈ lowerEntryLabels, r = lowerChild b l ∧ lowerInitialSafeBound t f n k p) ∨
     (k = 0 ∧ ∃ d ∈ lowerBridgeLabels f n, r = lowerPhysicalAdd b d))
end Freiman


