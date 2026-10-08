-- Prove2me | Definitions.Def_HalvingLines
-- name    : HalvingLines
-- status  : Definition
-- author  : @wurtle
-- created : 2026-10-07T04:32:13.602801+00:00
-- url     : https://prove2.me/theorems/cf51d611-c77f-4c46-a3ba-44f685d455e4
-- statement:
--   For planar point configurations P indexed by Fin n (points in ℝ²), orient(p,q,r) is the signed area determinant (q₁−p₁)(r₂−p₂)−(q₂−p₂)(r₁−p₁). GeneralPosition(P) means P is injective and no three distinct indices give collinear points (orient is nonzero). sideCount(P,i,j) counts the indices l with orient(P i,P j,P l)>0, that is, the points strictly to the left of the directed line from P i to P j. halvingCount(P) counts pairs i<j for which both sideCount(P,i,j) and sideCount(P,j,i) equal (n−2)/2 in natural-number division, so the line through the two points splits the remaining points evenly, the halving lines. slope(p,q) is (q₂−p₂)/(q₁−p₁). Generic(P) strengthens general position by requiring distinct x-coordinates, that distinct pairs i<j span distinct slopes (no two connecting lines are parallel), and a no-triple-crossing condition: for three distinct pairs, no point lies in the open segments of two of them and also in the closed segment of the third. belowCount(P,i,j) counts points lying strictly below the line through P i and P j (comparing y−s·x with s the slope). switchCount(P,k) counts pairs i<j for which 0<k<n and belowCount(P,i,j)=k−1. These are definitions only, with no theorem asserted.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HalvingLines.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HalvingLines.lean; bytes 16..1695
-- Kind: block; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib

namespace OAI

namespace PlanarHalving

abbrev Point := ℝ × ℝ

def orient (p q r : Point) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

def GeneralPosition {n : ℕ} (P : Fin n → Point) : Prop :=
  Function.Injective P ∧ ∀ i j l, i ≠ j → j ≠ l → i ≠ l →
    orient (P i) (P j) (P l) ≠ 0

noncomputable def sideCount {n : ℕ} (P : Fin n → Point) (i j : Fin n) : ℕ :=
  (Finset.univ.filter fun l => 0 < orient (P i) (P j) (P l)).card

noncomputable def halvingCount {n : ℕ} (P : Fin n → Point) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ sideCount P ij.1 ij.2 = (n - 2) / 2 ∧
      sideCount P ij.2 ij.1 = (n - 2) / 2).card

noncomputable def slope (p q : Point) : ℝ := (q.2 - p.2) / (q.1 - p.1)

def Generic {n : ℕ} (P : Fin n → Point) : Prop :=
  GeneralPosition P ∧
  (∀ i j, i ≠ j → (P i).1 ≠ (P j).1) ∧
  (∀ i j a b, i < j → a < b → slope (P i) (P j) = slope (P a) (P b) →
    i = a ∧ j = b) ∧
  (∀ i j a b c d, i < j → a < b → c < d →
    (i, j) ≠ (a, b) → (c, d) ≠ (i, j) → (c, d) ≠ (a, b) →
    ∀ z : Point, z ∈ openSegment ℝ (P i) (P j) →
      z ∈ openSegment ℝ (P a) (P b) → z ∉ segment ℝ (P c) (P d))

noncomputable def belowCount {n : ℕ} (P : Fin n → Point) (i j : Fin n) : ℕ :=
  let s := slope (P i) (P j)
  (Finset.univ.filter fun l => (P l).2 - s * (P l).1 <
    (P i).2 - s * (P i).1).card

noncomputable def switchCount {n : ℕ} (P : Fin n → Point) (k : ℕ) : ℕ :=
  (Finset.univ.filter fun ij : Fin n × Fin n =>
    ij.1 < ij.2 ∧ 0 < k ∧ k < n ∧ belowCount P ij.1 ij.2 = k - 1).card



end PlanarHalving
end OAI


