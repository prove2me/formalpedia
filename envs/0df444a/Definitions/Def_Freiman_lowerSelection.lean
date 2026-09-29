-- Prove2me | Definitions.Def_Freiman_lowerSelection
-- name    : Freiman_lowerSelection
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:48:35.237168+00:00
-- url     : https://prove2.me/theorems/161d8611-3aa0-4752-b5f6-7cb488bbc9e3
-- title:
--   Freiman lower construction: lowerSelection
-- statement:
--   Exact Section 14 and 15 cuts and source-tail dictionary, safe source lists, separate early and late chains, repeated-3 interface, physical-side history, and both target priorities.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), Part II; parts/lower_core.tex and the cited continuation sections.

import Definitions.Def_Freiman_lowerInitial

namespace Freiman
attribute [local instance] Classical.propDecidable
noncomputable def lowerTheta : ℕ → ℝ
  | 1 => prefixEval [] lowerAlpha
  | 2 => prefixEval [3,1,2] lowerBeta
  | 3 => prefixEval [3] lowerTau
  | 4 => prefixEval [3,1,2,3] lowerAlpha
  | 5 => prefixEval [3,1,2,3] lowerTau
  | 6 => prefixEval [3,1,2] lowerAlpha
  | 7 => prefixEval [3,1,1] lowerBeta
  | 8 => prefixEval [3,1,1,1,3] lowerTau
  | 9 => prefixEval [3,1,1,1,3] lowerAlpha
  | 10 => prefixEval [3,1,1] lowerTau
  | 11 => prefixEval [3,1] lowerTau
  | 12 => prefixEval [3,1,1,3] lowerAlpha
  | 13 => prefixEval [3,1,1,3] lowerTau
  | 14 => prefixEval [3,1] lowerBeta
  | 15 => prefixEval [3,2] lowerAlpha
  | 16 => prefixEval [3,2,3] lowerTau
  | 17 => prefixEval [3,2,3] lowerAlpha
  | 18 => prefixEval [3,2] (lowerTau / 2)
  | 19 => prefixEval [3] (lowerTau / 2)
  | 20 => prefixEval [3,2,1,3] lowerTau
  | 21 => prefixEval [3,2] lowerBeta
  | 22 => prefixEval [3,3] lowerAlpha
  | 23 => prefixEval [3,3,3] lowerTau
  | 24 => prefixEval [3,3] (lowerTau / 2)
  | 25 => prefixEval [3,3] lowerTau
  | 26 => prefixEval [3,3,1,2] lowerBeta
  | 27 => prefixEval [3,3,1,3] lowerTau
  | 28 => prefixEval [3] lowerAlpha
  | 29 => prefixEval [2] lowerBeta
  | 30 => prefixEval [2,1,3] lowerTau
  | 31 => prefixEval [2,1,3,3] lowerAlpha
  | 32 => prefixEval [2,1,3,3] lowerTau
  | 33 => prefixEval [2,1,3] lowerAlpha
  | 34 => prefixEval [2,1,2] lowerBeta
  | 35 => prefixEval [2,1,2,1,3] lowerTau
  | 36 => prefixEval [] (lowerTau / 2)
  | 37 => prefixEval [2,1,2,1] lowerBeta
  | 38 => prefixEval [2,1,2,3] lowerTau
  | 39 => prefixEval [2,1,2] lowerAlpha
  | 40 => prefixEval [2,1,1] lowerBeta
  | 41 => prefixEval [2,1,1,1,3] lowerTau
  | 42 => prefixEval [2,1,1,1,3] lowerAlpha
  | 43 => prefixEval [2,1,1] lowerTau
  | 44 => prefixEval [2,1,1,1,1,3] lowerAlpha
  | 45 => prefixEval [2,1,1,1,1,3] lowerTau
  | 46 => prefixEval [2,1,1,1] lowerBeta
  | 47 => prefixEval [2,1,1,2,3] lowerTau
  | 48 => prefixEval [2,1,1,2] lowerAlpha
  | 49 => prefixEval [2,1,1,2,3] lowerAlpha
  | 50 => prefixEval [2,1,1,2] (lowerTau / 2)
  | 51 => prefixEval [2,1] lowerTau
  | 52 => prefixEval [2,1,1,3] lowerAlpha
  | 53 => prefixEval [2,1,1,3] (lowerTau / 2)
  | 54 => prefixEval [2,1,1,3] lowerTau
  | 55 => prefixEval [2,1] lowerBeta
  | 56 => prefixEval [2,2] lowerAlpha
  | 57 => prefixEval [2,2,3] lowerTau
  | 58 => prefixEval [2] (lowerTau / 2)
  | 59 => prefixEval [2,2,1,3] lowerTau
  | 60 => prefixEval [2,2] lowerBeta
  | 61 => prefixEval [2,3] lowerAlpha
  | 62 => prefixEval [2,3,3] lowerTau
  | 63 => prefixEval [2,3] lowerTau
  | 64 => prefixEval [2] lowerAlpha
  | 65 => prefixEval [1] lowerBeta
  | 66 => prefixEval [1,1,3] lowerTau
  | 67 => prefixEval [1,1,3,3] lowerTau
  | 68 => prefixEval [1,1,3] lowerAlpha
  | 69 => prefixEval [1,1,2] lowerBeta
  | 70 => prefixEval [1,1,2,1,3] lowerTau
  | 71 => prefixEval [1] lowerTau
  | 72 => prefixEval [1,1,2,3] lowerTau
  | 73 => prefixEval [1,1,1] lowerBeta
  | 74 => prefixEval [1,1,1,1,3] lowerTau
  | 75 => prefixEval [1,1,1,1,1,3] lowerAlpha
  | 76 => prefixEval [1,1,1,1,1,3] lowerTau
  | 77 => prefixEval [1,1,1,1] lowerBeta
  | 78 => prefixEval [1,1,1,2,3] lowerTau
  | 79 => prefixEval [1,1] lowerTau
  | 80 => prefixEval [1,1,1,3] lowerAlpha
  | 81 => prefixEval [1,1,1,3] lowerTau
  | 82 => prefixEval [1,1] lowerBeta
  | 83 => prefixEval [1,2,3] lowerTau
  | 84 => prefixEval [1,2,2,1,3] lowerTau
  | 85 => prefixEval [1,2,2,3] lowerTau
  | 86 => prefixEval [1,2,2] (lowerTau / 2)
  | 87 => prefixEval [1,2,1,1,3] lowerTau
  | 88 => prefixEval [1,2,1,1,1,3] lowerTau
  | 89 => prefixEval [] lowerTau
  | 90 => prefixEval [1,2,1,3] lowerTau
  | 91 => prefixEval [1,2] lowerBeta
  | 92 => prefixEval [1,3] lowerAlpha
  | 93 => prefixEval [1,3,3] lowerTau
  | 94 => prefixEval [1,3] lowerTau
  | 95 => prefixEval [] lowerBeta
  | _ => 0
noncomputable def lowerThreshold (p : LowerPair) (c : ℝ) (i j k l : ℕ) : ℝ :=
  let v := lowerNormalize p
  let r := lowerRatio v.1
  let s := lowerRatio v.2
  c * ((1+s*lowerTheta j)*(1+s*lowerTheta l)) /
    ((1+r*lowerTheta i)*(1+r*lowerTheta k))
noncomputable def lowerA (p : LowerPair) (i : ℕ) : Prop :=
  let q := lowerScale (lowerNormalize p)
  match i with
  | 3 => q < lowerThreshold p (31/100) 3 63 25 66
  | 9 => q ≤ lowerThreshold p ((3-Real.sqrt 3)/2) 36 63 63 66
  | 16 => q > lowerThreshold p (183/250) 25 36 30 63
  | 20 => q < lowerThreshold p ((-171+76*Real.sqrt 21)/255) 1 65 28 95
  | 27 => q ≥ lowerThreshold p ((1703-884*Real.sqrt 3)/253) 19 10 57 63
  | 34 => q ≥ lowerThreshold p (153/250) 29 25 54 29
  | 40 => q ≥ lowerThreshold p ((109*Real.sqrt 21+14049)/29526) 34 6 34 6
  | 46 => q ≥ lowerThreshold p ((-24300+51497*Real.sqrt 3)/147323) 45 8 47 13
  | _ => False
noncomputable def lowerH (p : LowerPair) (i : ℕ) : Prop :=
  let q := lowerScale (lowerNormalize p)
  match i with
  | 2 => q > lowerThreshold p (37/50) 63 70 66 90
  | 5 => q < lowerThreshold p (279/500) 35 63 63 70
  | 6 => q < lowerThreshold p (69/200) 22 65 28 68
  | 7 => q < lowerThreshold p (161/500) 3 63 25 66
  | 17 => q > lowerThreshold p
      (|(lowerTheta 16-lowerTheta 13)/(lowerTheta 18-lowerTheta 25)|) 13 18 16 25
  | 21 => q < lowerThreshold p
      (|(lowerTheta 63-lowerTheta 3)/(lowerTheta 20-lowerTheta 66)|) 3 20 63 66
  | 23 => q > lowerThreshold p (139/250) 63 70 66 94
  | _ => False
noncomputable def lowerMixed (p : LowerPair) : Prop :=
  p.1.length % 2 ≠ p.2.length % 2
noncomputable def lowerL (p : LowerPair) : Prop := lowerEnds (lowerNormalize p).1 [3,1]
noncomputable def lowerR (p : LowerPair) : Prop := lowerEnds (lowerNormalize p).2 [3,1]
noncomputable def lowerLStar (p : LowerPair) : Prop := lowerEnds (lowerNormalize p).1 [3,1,3,1]
noncomputable def lowerRStar (p : LowerPair) : Prop := lowerEnds (lowerNormalize p).2 [3,1,3,1]
noncomputable def lowerMixedList (p : LowerPair) : List LowerLabel := by
  classical
  let b : List LowerLabel := [([1],[]),([],[1])]
  let x : List LowerLabel := [([1],[]),([2],[2]),([2,3],[3,2]),([2,3],[3,3])]
  let y : List LowerLabel := [([1,1,3],[3,1,1]),([2,1,3],[3,1,2]),([2,1,3],[3,1,1])]
  let z : List LowerLabel := [([1,1,3],[3,2]),([1,1,3],[3,3]),([2,1,3],[3,2]),([2],[1,1]),([2],[1])]
  let w : List LowerLabel := [([1],[]),([2],[2]),([3,3],[2,1,3]),([3,3],[2,1,2]),
    ([2,3],[2,1,3]),([2,3],[2,1,2]),([2,3],[2,1,1]),([2],[1])]
  let extra : List LowerLabel := if lowerL p then [] else [([3],[1])]
  exact if lowerH p 2 then b else
    if lowerH p 5 then
      if lowerL p then [([1],[]),([2],[])] else
        if lowerH p 6 ∧ lowerH p 7 then [([1],[]),([2],[]),([3],[])]
        else [([1],[]),([2],[]),([3],[1])] else
    if lowerRStar p then [] else
    if ¬ lowerH p 21 ∧ ¬ lowerEnds (lowerNormalize p).2 [3] ∧ lowerH p 23 then b else
    if lowerLStar p then [([1],[]),([2],[2])] else
    if lowerH p 21 then x ++ (if lowerH p 17 then [] else y) ++ z ++ extra
    else w ++ extra
noncomputable def lowerEarlyList (p : LowerPair) : List LowerLabel := by
  classical
  exact if lowerA p 27 then [([3],[2]),([2,2],[3,1,1]),([2,2],[3,2]),([2],[2])] else
    if lowerA p 34 then [([3],[2]),([1,1,2],[3,1,1]),([1,1,2],[3,2]),([2,1,1,2],[3,3]),([3,1,1,2],[3,3]),([2,2],[3,1,1]),([2,2],[3,2]),([2],[2])] else
    [([3],[2]),([3,1,2],[3,1,2]),([3,1,2],[3,1,1])] ++
    [(if lowerA p 40 then ([2,1,2],[3,1,2]) else ([1,2,1,2],[3,1,2]))] ++
    [([2,1,2],[3,1,1]),([3,1,2],[3,2]),([3,1,2],[3,3]),([2,1,2],[3,2]),([1,1,1,2],[3,1,1]),([2,1,1,2],[3,1,1]),([1,1,1,2],[3,2]),([1,1,1,2],[3,3]),([2,1,1,2],[3,2]),([3,1,1,2],[3,2]),([2,1,1,2],[3,3]),([3,1,1,2],[3,3]),([2],[2])]
def lowerLateCandidates : List LowerLabel :=
  [([2],[2]),([2],[1]),([2,1,3],[1,2,2]),([1,1,3],[1,2,3]),([1,1,3],[1,2,2]),([1,1,3],[1,2,1,1]),([2,3],[1,1,2]),([1,1,3],[1,1,1,1]),([2,3],[1,1,1,1]),([1,1,3],[1,1,1,2]),([3,3],[1,1,1,1]),([2,3],[1,1,1,2]),([2,3],[1,1,1,3]),([3,3],[1,1,1,2]),([3,3],[1,1,1,3]),([2],[1,1]),([1,2,3],[1,1,1,3]),([1,1,3],[1,2,1])]
noncomputable def lowerLateRouteValid (p : LowerPair) (ls : List LowerLabel) : Prop :=
  (∀ l ∈ ls, l ∈ lowerLateCandidates ∧ lowerGood (lowerChild p l)) ∧
  ls.head? = some ([2],[2]) ∧ ls.getLast? = some ([2],[1]) ∧
  ls.IsChain (fun l m => (lowerCover (lowerChild p l) ∩ lowerCover (lowerChild p m)).Nonempty)
noncomputable def lowerLateList (p : LowerPair) : List LowerLabel := by
  classical
  exact if h : ∃ ls, lowerLateRouteValid p ls then Classical.choose h else []
noncomputable def lowerEqualList (p : LowerPair) : List LowerLabel := by
  classical
  let small : List LowerLabel := [([1],[]),([2],[])]
  let d : LowerLabel := if lowerA p 20 then ([3],[1]) else ([3],[1,1])
  exact if lowerA p 3 then small ++ (if lowerL p then [] else [([3],[])]) else
    if lowerA p 9 then
      if lowerL p then small else
      if ¬ lowerR p ∨ lowerA p 16 then small ++ [([3],[2])] else
      if lowerRStar p then [([1],[]),([2],[2]),([2],[])]
      else [([1],[])] ++ lowerEarlyList p ++ [([2],[])] else
    if lowerLStar p then [([1],[]),([2],[1])] else
    if lowerL p then [([1],[])] ++ lowerLateList p ++ (if lowerRStar p then [] else [([2],[3])]) else
    if lowerRStar p then [([1],[]),([2],[1]),d,([2],[2])]
    else [([1],[]),([2],[1]),d,([2],[2]),([3],[2]),([2],[3])]
noncomputable def lowerRunOffered (p : LowerPair) : Prop :=
  ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerL p ∧ ¬ lowerR p ∧
  (let q := lowerNormalize p
   (7/5 : ℝ)*lowerWidth (q.2 ++ [3]) < lowerWidth (q.1 ++ [3]))
noncomputable def lowerOffered (p : LowerPair) (l : LowerLabel) : Prop :=
  l ∈ (if lowerMixed p then lowerMixedList p else lowerEqualList p) ∨
  (lowerRunOffered p ∧ ∃ k : ℕ, 0 < k ∧ l = (List.replicate k 3,List.replicate k 3))
noncomputable def lowerPriority (t : ℝ) (p : LowerPair) (l : LowerLabel) : Prop :=
  ((¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ ¬ lowerL p ∧ l = ([2],[3])) →
     t ∉ lowerCover (lowerChild p ([3],[2]))) ∧
  ((¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ lowerR p ∧
       ¬ lowerA p 16 ∧ l = ([2],[])) →
     (if lowerRStar p then t ∉ lowerCover (lowerChild p ([2],[2])) else
       ∀ c ∈ lowerEarlyList p, t ∉ lowerCover (lowerChild p c)))
noncomputable def lowerReflects (p : LowerPair) : Bool := by
  classical
  exact decide (lowerWidth p.1 < lowerWidth p.2)
noncomputable def lowerOrientation (h : ℕ → LowerPair) : ℕ → Bool
  | 0 => false
  | n+1 => (lowerOrientation h n).xor (lowerReflects (h n))
noncomputable def lowerPhysicalPath (h : ℕ → LowerPair) (n : ℕ) : LowerPair :=
  if lowerOrientation h n then (h n).swap else h n
def lowerHistory (t : ℝ) (h : ℕ → LowerPair) (n : ℕ) : Prop :=
  lowerInitialRoot t (h 0) ∧
  (∀ j : ℕ, j ≤ n → lowerState t (h j)) ∧
  (∀ j : ℕ, j < n → ∃ l : LowerLabel,
    lowerOffered (h j) l ∧ lowerPriority t (h j) l ∧ h (j+1) = lowerChild (h j) l)
noncomputable def lowerLocalCoordinate (p : LowerPair) (t : ℝ) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then t else -t
noncomputable def lowerLocalLower (p : LowerPair) (l : LowerLabel) : ℝ :=
  if (lowerNormalize p).1.length % 2 = 0 then lowerEndpoint (lowerChild p l) false
  else -lowerEndpoint (lowerChild p l) true
noncomputable def lowerSuffixBounds (p : LowerPair) (t : ℝ) : Prop :=
  (¬ lowerMixed p → ¬ lowerA p 3 → ¬ lowerA p 9 → lowerLStar p →
    lowerLocalLower p ([2],[1]) ≤ lowerLocalCoordinate p t) ∧
  (¬ lowerMixed p → ¬ lowerA p 3 → lowerRStar p →
    lowerLocalLower p ([2],[2]) ≤ lowerLocalCoordinate p t) ∧
  (lowerMixed p → ¬ lowerH p 2 → ¬ lowerH p 5 → lowerLStar p →
    lowerLocalLower p ([2],[2]) ≤ lowerLocalCoordinate p t) ∧
  (lowerMixed p → ¬ lowerH p 2 → ¬ lowerH p 5 → ¬ lowerRStar p)
def lowerPath (t : ℝ) (h : ℕ → LowerPair) : Prop := ∀ n, lowerHistory t h n
end Freiman


