-- Prove2me | Definitions.Def_DualSepClusterLP_SparseRounder
-- name    : DualSepClusterLP_SparseRounder
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-19T13:31:08.453661+00:00
-- url     : https://prove2.me/theorems/9561eea2-d6d6-4cbc-9eb6-a16e31704d54
-- title:
--   Deterministic sparse-input cluster LP rounder
-- statement:
--   Given a Boolean encoding of a signed graph and explicit rational column weights, compute pair masses from the support, construct a clock partition and a pivot partition, and encode the cheaper one. For a pivot and a column, fix join coins by comparing the two conditional gains.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Appendix F (conditional-expectation rounding), https://arxiv.org/abs/2607.27829.

import Definitions.Def_DualSepClusterLP_SparseInput
import Definitions.Def_DualSepClusterLP_RoundingAnalysis

namespace DualSepClusterLP.SparsePivot

/-- Pair co-membership is obtained by a single scan of the input columns. -/
def mass {n : ℕ} (L : SparseWeights n) (i j : Fin n) : ℚ :=
  (L.map (fun e => if i ∈ e.1 ∧ j ∈ e.1 then e.2 else 0)).sum

end DualSepClusterLP.SparsePivot

namespace DualSepClusterLP.SparsePivot

def budget (s : Bool) (y : ℚ) : ℚ :=
  if s then 2*(2773/1227)*(1-y)^2/(2-y)
  else (2773/1227)*y*(3-2*y)/(2-y)

def rescue (y : ℚ) : ℚ := max 0 (min 1 ((13/6)*(y-1/2)))

def chance (s : Bool) (y : ℚ) (member : Bool) : ℚ :=
  if s then
    let q := rescue y
    y+(1-y)*q + (1-q)*((if member then 1 else 0)-y)
  else min ((3/2)*y) (2*y-y^2)

def initial {n : ℕ} (G : Graph n) (L : SparseWeights n) (u : Fin n) (S : Finset (Fin n))
    (v : Fin n) : ℚ :=
  if v = u then 1 else chance (unorderedSign G u v) (mass L u v) (decide (v∈S))

/-- Expected one-step gain for arbitrary independently sampled join coins. -/
def entry {n : ℕ} (G : Graph n) (L : SparseWeights n) (u v w : Fin n) (x : Fin n → ℚ) : ℚ :=
  if u=v ∨ u=w then 0 else if v=w then
    budget (unorderedSign G u v) (mass L u v) - (if unorderedSign G u v then 1-x v else x v)
  else
    let j := x v*x w
    (budget (unorderedSign G v w) (mass L v w) * (x v+x w-j) -
      (if unorderedSign G v w then x v+x w-2*j else j))/2

def gain {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n)) (u : Fin n)
    (x : Fin n → ℚ) : ℚ := ∑ v ∈ W, ∑ w ∈ W, entry G L u v w x

/-- At most two conditional gain evaluations per coin. -/
def fix {n : ℕ} (f : (Fin n → ℚ) → ℚ) : List (Fin n) → (Fin n → ℚ) → (Fin n → ℚ)
  | [], x => x
  | i::is, x =>
    let bit := if x i=0 then 0 else if x i=1 then 1 else
      if f (Function.update x i 1) ≤ f (Function.update x i 0) then 0 else 1
    fix f is (Function.update x i bit)

def cluster {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n))
    (u : Fin n) (S : Finset (Fin n)) : Finset (Fin n) :=
  let x := fix (gain G L W u) (List.finRange n) (initial G L u S)
  W.filter (fun v => x v=1)

def margin {n : ℕ} (G : Graph n) (L : SparseWeights n) (W K : Finset (Fin n)) : ℚ :=
  ∑ v ∈ W, ∑ w ∈ W, if v<w then
    (if v∈K ∨ w∈K then budget (unorderedSign G v w) (mass L v w) else 0) -
    (if unorderedSign G v w then (if decide (v∈K) != decide (w∈K) then 1 else 0)
      else (if v∈K ∧ w∈K then 1 else 0)) else 0

def candidates {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n)) :
    List (Finset (Fin n)) :=
  (List.finRange n).flatMap (fun u => if u∈W then
    L.filterMap (fun e => if u∈e.1 then some (cluster G L W u e.1) else none) else [])

/-- Enumerate live pivots and listed columns and take the first successful cluster. -/
def step {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n)) : Finset (Fin n) :=
  ((candidates G L W).find? (fun K => decide (K.Nonempty ∧ 0 ≤ margin G L W K))).getD ∅

end DualSepClusterLP.SparsePivot

namespace DualSepClusterLP.SparseClock

def budget (p : Bool) (y : ℚ) : ℚ :=
  if p then 2*(1-y)/(2-y) else y/(2-y)

def pairGain {n : ℕ} (G : Graph n) (L : SparseWeights n) (S : Finset (Fin n))
    (i j : Fin n) : ℚ :=
  (if i ∈ S ∨ j ∈ S then budget (G i j) (SparsePivot.mass L i j) else 0) -
  (if G i j then (if decide (i ∈ S) != decide (j ∈ S) then 1 else 0)
   else (if i ∈ S ∧ j ∈ S then 1 else 0))

def margin {n : ℕ} (G : Graph n) (L : SparseWeights n) (W S : Finset (Fin n)) : ℚ :=
  ∑ i ∈ W, ∑ j ∈ W, if i < j then pairGain G L S i j else 0

/-- Scan the input columns in their given order. A qualifying column must meet W. -/
def step {n : ℕ} (G : Graph n) (L : SparseWeights n) (W : Finset (Fin n)) : Finset (Fin n) :=
  ((L.map Prod.fst).find? (fun S => decide ((W ∩ S).Nonempty ∧ 0 ≤ margin G L W S))).getD ∅

end DualSepClusterLP.SparseClock

namespace DualSepClusterLP.RoundFold

def labelAux {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n)) : ℕ → Finset (Fin n) → Fin n → ℕ
  | 0, _, _ => 0
  | f+1, W, i => if i ∈ pick W then 0 else labelAux pick f (W \ pick W) i + 1

noncomputable def stepEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (K : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if i < j ∧ (i ∈ K ∨ j ∈ K) then B (G i j) (pairMass z i j) -
    (if G i j ≠ decide (i ∈ K ↔ j ∈ K) then 1 else 0) else 0

noncomputable def stepMargin {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (W K : Finset (Fin n)) : ℝ :=
  ∑ i ∈ W, ∑ j ∈ W, stepEntry G z B K i j

noncomputable def labelEntry {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (l : Fin n → ℕ) (r : ℕ) (i j : Fin n) : ℝ :=
  if i < j ∧ min (l i) (l j) = r then B (G i j) (pairMass z i j) -
    (if G i j ≠ decide (l i = l j) then 1 else 0) else 0

noncomputable def labelMargin {n : ℕ} (G : Graph n) (z : Finset (Fin n) → ℝ)
    (B : Bool → ℝ → ℝ) (W : Finset (Fin n)) (l : Fin n → ℕ) (r : ℕ) : ℝ :=
  ∑ i ∈ W, ∑ j ∈ W, labelEntry G z B l r i j

def Progress {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n)) : Prop :=
  ∀ W, W.Nonempty → (W ∩ pick W).Nonempty

/-- The total partition function, executable on arbitrary input and arbitrary selectors. -/
def run {n : ℕ} (pick : Finset (Fin n) → Finset (Fin n)) : Clustering n :=
  fun i => let t := labelAux pick n Finset.univ i
           if h : t < n then ⟨t,h⟩ else i

end DualSepClusterLP.RoundFold

namespace DualSepClusterLP.RoundWire

def unary : List Bool → ℕ × List Bool
  | [] => (0, [])
  | false :: rest => (0, rest)
  | true :: rest => let (k, s) := unary rest; (k+1, s)

def natField (data : List Bool) : ℕ × List Bool :=
  let (len, rest) := unary data
  ((rest.take len).foldr Nat.bit 0, rest.drop len)

def priceField (data : List Bool) : ℚ × List Bool :=
  let (a, r) := natField data.tail
  let (b, s) := natField r
  (mkRat (if data.headD false then -(a:ℤ) else a) b, s)

def readRows (width : ℕ) : ℕ → List Bool → List (List Bool) × List Bool
  | 0, data => ([], data)
  | k+1, data =>
    let (rows, tail) := readRows width k (data.drop width)
    (data.take width :: rows, tail)

def readEntries (n : ℕ) : ℕ → List Bool → SparseWeights n
  | 0, _ => []
  | k+1, data =>
    let (q, s) := priceField (data.drop n)
    (Finset.univ.filter (fun i : Fin n => data.getD i.val false), q) :: readEntries n k s

def upper {n : ℕ} (G : Graph n) : Graph n := fun i j => if i<j then G i j else false

/-- Decode a graph and explicit sparse LP solution. Both iteration bounds are capped by
fields of the input word even when it does not encode an instance. -/
def decodeBody (header : ℕ × List Bool) : (n : ℕ) × (Graph n × SparseWeights n) :=
  let (n, body) := header
  let (rows, tail) := readRows n n body
  let (k, s) := natField tail
  ⟨n, fun i j => (rows.getD i.val []).getD j.val false, readEntries n (min k s.length) s⟩

def decode (data : List Bool) := decodeBody (unary (unary data).2)

end DualSepClusterLP.RoundWire

namespace DualSepClusterLP.RoundWire

/-- Encode the cheaper partition produced by the two rational selectors. -/
def output (data : List Bool) : List Bool :=
  let ⟨_, G, L⟩ := decode data
  let C := RoundFold.run (SparseClock.step G L)
  let P := RoundFold.run (SparsePivot.step G L)
  partitionOutput (if disagreements G C ≤ disagreements G P then C else P)

end DualSepClusterLP.RoundWire


