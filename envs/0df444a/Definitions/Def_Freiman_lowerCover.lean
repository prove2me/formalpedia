-- Prove2me | Definitions.Def_Freiman_lowerCover
-- name    : Freiman_lowerCover
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T11:47:23.049992+00:00
-- url     : https://prove2.me/theorems/5822ff51-f16a-4a99-be89-2fc7595bb450
-- title:
--   Freiman lower construction: lowerCover
-- statement:
--   Physical outward prefixes, full-width normalization with tie retention, actual shortened and virtual endpoint rules, the seven fixed central cores, goodness, admissibility, and their symbolic cylinders.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), Part II; parts/lower_core.tex and the cited continuation sections.

import Definitions.Def_Freiman_prefixEval
import Definitions.Def_Freiman_wordRealization
import Definitions.Def_Freiman_cF
import Mathlib.Data.List.Infix
import Mathlib.Analysis.Real.Sqrt

namespace Freiman
abbrev LowerPair := List ℕ+ × List ℕ+
abbrev LowerLabel := List ℕ+ × List ℕ+
noncomputable def lowerAlpha : ℝ := (Real.sqrt 21 - 3) / 6
noncomputable def lowerBeta : ℝ := (Real.sqrt 21 - 3) / 2
noncomputable def lowerTau : ℝ := Real.sqrt 3 - 1
noncomputable def lowerWidth (w : List ℕ+) : ℝ :=
  |prefixEval w lowerBeta - prefixEval w lowerAlpha|
def lowerCD (w : List ℕ+) : ℕ × ℕ :=
  w.foldl (fun z a => (z.2, z.1 + (a : ℕ) * z.2)) (0, 1)
noncomputable def lowerRatio (w : List ℕ+) : ℝ :=
  ((lowerCD w).1 : ℝ) / ((lowerCD w).2 : ℝ)
noncomputable def lowerScale (p : LowerPair) : ℝ :=
  ((lowerCD p.1).2 : ℝ)^2 / ((lowerCD p.2).2 : ℝ)^2
noncomputable def lowerNormalize (p : LowerPair) : LowerPair := by
  classical
  exact if lowerWidth p.2 ≤ lowerWidth p.1 then p else (p.2,p.1)
def lowerEnds (w s : List ℕ+) : Prop := s.IsSuffix w
noncomputable def lowerNaturalShort (w : List ℕ+) (upper : Bool) : Bool := by
  classical
  exact if (w.length % 2 = 0) = (!upper) then decide (lowerEnds w [3,1])
    else decide (lowerEnds w [3])
noncomputable def lowerEndpointSuffix (w : List ℕ+) (upper short : Bool) : List ℕ+ :=
  if (w.length % 2 = 0) = (!upper) then (if short then [2,1,3] else [3])
  else (if short then [1,2,1,3] else [1,3])
noncomputable def lowerNaturalWords (p : LowerPair) (upper : Bool) : LowerPair :=
  (p.1 ++ lowerEndpointSuffix p.1 upper (lowerNaturalShort p.1 upper),
   p.2 ++ lowerEndpointSuffix p.2 upper (lowerNaturalShort p.2 upper))
noncomputable def lowerEqualWords (p : LowerPair) (upper : Bool) : LowerPair := by
  classical
  let q := lowerNormalize p
  let s₁ := lowerNaturalShort q.1 upper
  let s₂ := lowerNaturalShort q.2 upper
  let e : List ℕ+ := if (q.1.length % 2 = 0) = (!upper) then [3] else [1,3]
  let shorten := !s₁ && !s₂ && decide
    (lowerWidth (q.1 ++ e) ≤ (7 / 5 : ℝ) * lowerWidth (q.2 ++ e))
  let r := (q.1 ++ lowerEndpointSuffix q.1 upper s₁,
            q.2 ++ lowerEndpointSuffix q.2 upper (s₂ || shorten))
  exact if lowerWidth p.2 ≤ lowerWidth p.1 then r else (r.2,r.1)
noncomputable def lowerEndpointWords (p : LowerPair) (upper : Bool) : LowerPair := by
  classical
  exact if p.1.length % 2 = p.2.length % 2 then lowerEqualWords p upper else
    let leftWide := lowerWidth p.2 ≤ lowerWidth p.1
    let w := if leftWide then p.1 else p.2
    let virtualUpper := decide (w.length % 2 = 0)
    if upper = virtualUpper then
      lowerEqualWords (if leftWide then (p.1 ++ [1],p.2) else (p.1,p.2 ++ [1])) upper
    else lowerNaturalWords p upper
noncomputable def lowerEndpoint (p : LowerPair) (upper : Bool) : ℝ :=
  let w := lowerEndpointWords p upper
  4 + prefixEval w.1 lowerTau + prefixEval w.2 lowerTau
noncomputable def lowerCover (p : LowerPair) : Set ℝ :=
  Set.Icc (lowerEndpoint p false) (lowerEndpoint p true)
noncomputable def lowerChild (p : LowerPair) (l : LowerLabel) : LowerPair := by
  classical
  let q := lowerNormalize p
  exact (q.1 ++ l.1.reverse, q.2 ++ l.2)
def lowerGood (p : LowerPair) : Prop :=
  (lowerCover (lowerChild p ([1],[])) ∩ lowerCover (lowerChild p ([2],[]))).Nonempty
def lowerStrictGood (p : LowerPair) : Prop :=
  max (lowerEndpoint (lowerChild p ([1],[])) false)
      (lowerEndpoint (lowerChild p ([2],[])) false) <
  min (lowerEndpoint (lowerChild p ([1],[])) true)
      (lowerEndpoint (lowerChild p ([2],[])) true)
def lowerBaseCores : List LowerPair :=
  [([3],[3]), ([3,1,3],[3,1,2]), ([3,2,1],[4,3,1]),
   ([3,1,3],[3,1,3]), ([3,2,1,1,2],[4,3,2,2]),
   ([3,2,1,1,3],[4,3,2,3]), ([3,2,1,1,3],[4,3,2,2])]
def lowerCores : List LowerPair := lowerBaseCores ++ lowerBaseCores.map Prod.swap
def lowerExtends (p q : LowerPair) : Prop :=
  ∃ u v : List ℕ+, q = (p.1 ++ u,p.2 ++ v) ∧
    (∀ d ∈ u, (d : ℕ) ≤ 3) ∧ (∀ d ∈ v, (d : ℕ) ≤ 3)
def lowerAdmissible (p : LowerPair) : Prop :=
  (∃ c ∈ lowerCores, lowerExtends c p) ∧
  ¬ ([3,1,3,1,3] : List ℕ+).IsInfix (p.1.reverse ++ [4] ++ p.2)
def lowerCylinder (p : LowerPair) (a : ℤ → ℕ+) : Prop :=
  a 0 = 4 ∧
  (∀ n : ℕ, n < p.1.length → a (-(n : ℤ)-1) = p.1.getD n 1) ∧
  (∀ n : ℕ, n < p.2.length → a ((n : ℤ)+1) = p.2.getD n 1)
def LowerModel (a : ℤ → ℕ+) : Prop :=
  AvoidsBlock a [3,1,3,1,3] ∧ ∃ c ∈ lowerCores,
    lowerCylinder c a ∧
    (∀ n : ℕ, c.1.length ≤ n → (a (-(n : ℤ)-1) : ℕ) ≤ 3) ∧
    (∀ n : ℕ, c.2.length ≤ n → (a ((n : ℤ)+1) : ℕ) ≤ 3)
def lowerHasValue (t : ℝ) : Prop :=
  ∃ a : ℤ → ℕ+, LowerModel a ∧ localValue a 0 = t
noncomputable def lowerParameterBox (p : LowerPair) : Prop :=
  (1/4 : ℝ) ≤ lowerRatio p.1 ∧ lowerRatio p.1 ≤ (4/5 : ℝ) ∧
  (1/4 : ℝ) ≤ lowerRatio p.2 ∧ lowerRatio p.2 ≤ (4/5 : ℝ)
def lowerState (t : ℝ) (p : LowerPair) : Prop :=
  lowerAdmissible p ∧ lowerGood p ∧ t ∈ lowerCover p ∧ lowerParameterBox p
end Freiman


