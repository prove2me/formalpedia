-- Prove2me | Definitions.Def_Freiman_lowerCertificates
-- name    : Freiman_lowerCertificates
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:49:14.017358+00:00
-- url     : https://prove2.me/theorems/cd99bddb-fdbf-43c1-92c8-9ca123f02bca
-- title:
--   Freiman lower construction: lowerCertificates
-- statement:
--   Exact contact predicates for the initial arithmetic certificates, the endpoint-limit interfaces, suffix target bounds, late-entry exception, and the numerical cylinder error.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), Part II; parts/lower_core.tex and the cited continuation sections.

import Definitions.Def_Freiman_lowerSelection
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Nat.Fib.Basic

namespace Freiman
noncomputable def lowerContact (p : LowerPair) (u v w z : List ℕ+) : Prop :=
  0 < (-1 : ℝ)^p.1.length *
    (prefixEval (p.1++u) lowerTau - prefixEval (p.1++v) lowerTau +
     prefixEval (p.2++w) lowerTau - prefixEval (p.2++z) lowerTau)
noncomputable def lowerNContact (n : ℕ) (u v w z : List ℕ+) : Prop :=
  prefixEval ([3,2,1,1] ++ lowerRepeat lowerPeriod n ++ w) lowerTau +
  prefixEval ([4,3,2,2] ++ lowerRepeat lowerPeriod n ++ z) lowerTau <
  prefixEval ([3,2,1,1] ++ lowerRepeat lowerPeriod n ++ u) lowerTau +
  prefixEval ([4,3,2,2] ++ lowerRepeat lowerPeriod n ++ v) lowerTau
noncomputable def lowerInitialSeams : Prop :=
  (∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .A n k 0))
    [3,3,1,2,1,3] [3,1,2,1,3] [3,3,1,2,1,3] [2,1,3]) ∧
  (∀ n k p, lowerContact (lowerNormalize (lowerFamilyPair .C n k p))
    [3,3,1,2,1,3] [3,1,2,1,3] [3,3,1,2,1,3] [2,1,3]) ∧
  (∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .B n k 0))
    [3,1,3,3,1,2,1,3] [3,1,2,1,3] [2,1,3,3,1,2,1,3] [2,1,3]) ∧
  (∀ n k, lowerContact (lowerNormalize (lowerFamilyPair .B n k 0))
    [3,3,1,2,1,3] [3,1,3,1,2,1,3] [3,3,1,2,1,3] [2,1,3,1,2,1,3]) ∧
  (∀ n, lowerNContact n [3,1,3,1,2,3,1,2,1,3] [3,1,3,3,1,2,1,3]
    [3,1,3,1,2,1,3] [3,1,2,1,3]) ∧
  (∀ n, lowerNContact n [3,1,3,3,1,2,1,3] [3,3,1,2,1,3]
    [3,1,2,1,3] [3,1,2,1,3]) ∧
  (∀ n, lowerNContact n [3,1,3,1,2,1,3,1,2,3,1,2,1,3] [3,1,3,1,2,1,3,2,1,3]
    [3,1,3,1,2,1,3] [3,1,3,1,2,1,3])
noncomputable def lowerInitialLimits : Prop :=
  (∀ n, Filter.Tendsto (fun k => sInf (lowerFamilyH .A n k 0)) Filter.atTop
      (nhds (lowerFamilyLimitValue .A n 0)) ∧
    Filter.Tendsto (fun k => sSup (lowerFamilyH .A n k 0)) Filter.atTop
      (nhds (lowerFamilyLimitValue .A n 0))) ∧
  (∀ n, Filter.Tendsto (fun k => sInf (lowerFamilyH .B n k 0)) Filter.atTop
      (nhds (lowerFamilyLimitValue .B n 0)) ∧
    Filter.Tendsto (fun k => sSup (lowerFamilyH .B n k 0)) Filter.atTop
      (nhds (lowerFamilyLimitValue .B n 0))) ∧
  (∀ n k, Filter.Tendsto (fun p => sInf (lowerFamilyH .C n k p)) Filter.atTop
      (nhds (lowerFamilyLimitValue .C n k)) ∧
    Filter.Tendsto (fun p => sSup (lowerFamilyH .C n k p)) Filter.atTop
      (nhds (lowerFamilyLimitValue .C n k))) ∧
  (Filter.Tendsto (fun n => sInf (lowerFamilyH .A n 1 0)) Filter.atTop (nhds cF) ∧
   Filter.Tendsto (fun n => sSup (lowerFamilyH .A n 1 0)) Filter.atTop (nhds cF))
noncomputable def lowerNumericSuccessor (t : ℝ) (p : LowerPair) : Prop :=
  lowerHasValue t ∨ ∃ l : LowerLabel,
    lowerOffered p l ∧ lowerGood (lowerChild p l) ∧ t ∈ lowerCover (lowerChild p l)
noncomputable def lowerLateEntryDomain (p : LowerPair) : Prop :=
  (¬ lowerMixed p → ¬ lowerA p 3 → ¬ lowerA p 9 → lowerL p → ¬ lowerLStar p →
    (13/17 : ℝ) ≤ lowerRatio (lowerNormalize p).1 ∨
      lowerNormalize p = ([3,1],[3,1]))
noncomputable def lowerP97Anchor (p : LowerPair) (t : ℝ) : Prop :=
  lowerMixed p → ¬ lowerH p 2 → lowerH p 5 → lowerL p →
    lowerLocalLower p ([2],[]) ≤ lowerLocalCoordinate p t
noncomputable def lowerPrefixSize (p : LowerPair) : ℕ := p.1.length+p.2.length
noncomputable def lowerWithinTwo (h : ℕ → LowerPair) : Prop :=
  ∀ n : ℕ,
    (lowerWidth (h n).2 ≤ lowerWidth (h n).1 → (h n).1.length < (h (n+2)).1.length) ∧
    (lowerWidth (h n).1 < lowerWidth (h n).2 → (h n).2.length < (h (n+2)).2.length)
noncomputable def lowerCylinderError (p : LowerPair) : ℝ :=
  1 / ((Nat.fib (p.1.length+1) : ℝ)^2) + 1 / ((Nat.fib (p.2.length+1) : ℝ)^2)
noncomputable def lowerEarlyGeometry (p : LowerPair) : Prop :=
  (∀ l ∈ lowerEarlyList p, lowerGood (lowerChild p l)) ∧
  IsPreconnected {t : ℝ | ∃ l ∈ lowerEarlyList p, t ∈ lowerCover (lowerChild p l)} ∧
  lowerCover (lowerChild p ([3],[2])) ⊆ {t : ℝ | ∃ l ∈ lowerEarlyList p, t ∈ lowerCover (lowerChild p l)} ∧
  lowerCover (lowerChild p ([2],[2])) ⊆ {t : ℝ | ∃ l ∈ lowerEarlyList p, t ∈ lowerCover (lowerChild p l)}
noncomputable def lowerEarlyDomain (p : LowerPair) : Prop :=
  ¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ lowerR p ∧ ¬ lowerA p 16 ∧ ¬ lowerRStar p
def lowerSide (p : LowerPair) (right : Bool) : List ℕ+ := if right then p.2 else p.1
noncomputable def lowerBoundedHistory (h : ℕ → LowerPair) (n : ℕ) : Prop :=
  ∀ right : Bool, lowerEnds (lowerSide (lowerPhysicalPath h n) right) [3,1,3,1] →
    ∃ m : ℕ, m ≤ n ∧ n-m ≤ 7 ∧
      (m = 0 ∨ (0 < m ∧ h m = lowerChild (h (m-1)) ([2],[3]) ∧
        lowerEnds (lowerSide (lowerPhysicalPath h m) right) [3,1,3])) ∧
      (∀ j : ℕ, m ≤ j → j ≤ n →
        lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3] ∨ lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3,1])
noncomputable def lowerPreferredGood (p : LowerPair) : Prop :=
  ((¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ ¬ lowerA p 9 ∧ ¬ lowerL p ∧
      lowerOffered p ([2],[3])) →
    lowerOffered p ([3],[2]) ∧ lowerGood (lowerChild p ([3],[2]))) ∧
  ((¬ lowerMixed p ∧ ¬ lowerA p 3 ∧ lowerA p 9 ∧ ¬ lowerL p ∧ lowerR p ∧
      ¬ lowerA p 16 ∧ lowerOffered p ([2],[])) →
    (lowerRStar p → lowerOffered p ([2],[2]) ∧ lowerGood (lowerChild p ([2],[2]))) ∧
    (¬ lowerRStar p → ∀ l ∈ lowerEarlyList p, lowerOffered p l ∧ lowerGood (lowerChild p l)))
noncomputable def lowerBridgeInterval (f : LowerInitialFamily) (n k p : ℕ) : Set ℝ :=
  let v := lowerNormalize (lowerFamilyPair f n k p)
  let e := lowerEndpoint (v.1 ++ [1,2],v.2 ++ [1,2]) (decide (v.1.length % 2 = 0))
  if v.1.length % 2 = 0 then Set.Icc e (sSup (lowerFamilyH f n k p))
  else Set.Icc (sInf (lowerFamilyH f n k p)) e
noncomputable def lowerBridgeGood (f : LowerInitialFamily) (n : ℕ) : Prop :=
  ∀ t ∈ lowerBridgeInterval f n 0 0,
    ∃ d ∈ lowerBridgeLabels f n, lowerState t (lowerPhysicalAdd (lowerFamilyPair f n 0 0) d)
noncomputable def lowerInitialMarked (h : ℕ → LowerPair) (n : ℕ) (right : Bool) : Prop :=
  n ≤ 7 ∧ ∀ j : ℕ, j ≤ n →
    lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3] ∨ lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3,1]
noncomputable def lowerGenericMarked (h : ℕ → LowerPair) (n : ℕ) (right : Bool) : Prop :=
  ∃ m : ℕ, 0 < m ∧ m ≤ n ∧ n-m ≤ 7 ∧
    h m = lowerChild (h (m-1)) ([2],[3]) ∧ lowerEnds (lowerSide (lowerPhysicalPath h m) right) [3,1,3] ∧
    ∀ j : ℕ, m ≤ j → j ≤ n →
      lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3] ∨ lowerEnds (lowerSide (lowerPhysicalPath h j) right) [3,1,3,1]
noncomputable def lowerMarkedPhysical (h : ℕ → LowerPair) (n row : ℕ) : Bool := by
  classical
  let localRight := if row = 1 ∨ row = 3 then lowerReflects (h n) else !(lowerReflects (h n))
  exact (lowerOrientation h n).xor localRight
noncomputable def lowerRunPair (p : LowerPair) (k : ℕ) : LowerPair :=
  lowerChild p (List.replicate k 3,List.replicate k 3)
noncomputable def lowerRunValue (p : LowerPair) : ℝ :=
  localValue (lowerPeriodicSequence p [3]) 0
noncomputable def lowerRunSet (p : LowerPair) : Set ℝ :=
  {t | t = lowerRunValue p ∨ ∃ k : ℕ, 0 < k ∧ t ∈ lowerCover (lowerRunPair p k)}
noncomputable def lowerRunParameters (p : LowerPair) : Prop :=
  ∀ k : ℕ, 0 < k →
    let q := lowerNormalize p
    let u := q.1 ++ List.replicate k 3
    let v := q.2 ++ List.replicate k 3
    (1/4 : ℝ) ≤ lowerRatio u ∧ lowerRatio u ≤ (1/3 : ℝ) ∧
    (1/4 : ℝ) ≤ lowerRatio v ∧ lowerRatio v ≤ (1/3 : ℝ) ∧
    (31/100 : ℝ) < lowerScale (u,v) ∧ lowerScale (u,v) < (4/5 : ℝ) ∧
    lowerWidth v ≤ lowerWidth u ∧ lowerWidth u < (19/5 : ℝ)*lowerWidth v
noncomputable def lowerRunFamily (p : LowerPair) : Prop :=
  (∀ k : ℕ, 0 < k → lowerGood (lowerRunPair p k)) ∧
  IsPreconnected (lowerRunSet p) ∧ lowerHasValue (lowerRunValue p)
end Freiman


