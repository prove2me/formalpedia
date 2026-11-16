-- Prove2me | Definitions.Def_ConantTerry_Orders_Supplement_covered_proto_ladder
-- name    : ConantTerry_Orders_Supplement_covered_proto_ladder
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:23:49.577241+00:00
-- url     : https://prove2.me/theorems/1ec86aff-8361-4214-9ad7-e351c0b15ff2
-- title:
--   Covered proto-ladders
-- statement:
--   Let $X,Y$ be arbitrary sets, $f:X\times Y\to[0,1]$, $k\ge1$, $\gamma>0$, and $\mathcal I,\mathcal J$ collections of subsets of $[0,1]$. A covered proto-ladder consists of $x_1,\ldots,x_k\in X$, $y_1,\ldots,y_{k+1}\in Y$, thresholds $r_i\in[0,1]$, and sets $I_i\in\mathcal I$, $J_i\in\mathcal J$, such that for each $i$,
--   $$
--   f(x_j,y_i)\in I_i\ (i\le j\le k),\qquad f(x_i,y_j)\in J_i\ (i<j\le k+1),
--   $$
--   and one of the following alternatives holds:
--   $$
--   \big(f(x_i,y_i)>r_i\ \text{and}\ f(x_i,y_j)\le r_i-\gamma\text{ for every }j>i\big)
--   \quad\text{or}\quad
--   \big(f(x_i,y_i)\le r_i\ \text{and}\ f(x_i,y_j)\ge r_i+\gamma\text{ for every }j>i\big).
--   $$
--   The alternative may depend on $i$. Admission means existence of all these witnesses. This is the intermediate configuration used by Lemmas 4.2 and 4.3, without assuming an extracted ladder, uniform orientation, finiteness of the collections, or any interval condition.
--
--   **Formalization Note** `Fin k` and `Fin (k+1)` decrease every source index by one. `castSucc` includes each of the first $k$ columns in the $k+1$ columns. Collections are sets of subsets of the unit interval. Positive domains are stated by consumer theorems.
-- source:
--   C. Terry, G. Conant, STOC 2027 submission #1299 (October 2026), p. 14, Definition 4.1

import Mathlib

namespace ConantTerry.Orders.Supplement

/-- Definition 4.1, p.14. All indices are decreased by one; `castSucc`
includes the first k columns among the k+1 columns. Orientation may vary by row.
The collections need not be finite, covers, or collections of intervals. -/
def IsCoveredProtoLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (γ : ℝ)
    (𝓘 𝓙 : Set (Set (Set.Icc (0 : ℝ) 1)))
    (x : Fin k → X) (y : Fin (k + 1) → Y)
    (r : Fin k → Set.Icc (0 : ℝ) 1) : Prop :=
  ∃ I J : Fin k → Set (Set.Icc (0 : ℝ) 1),
    (∀ i, I i ∈ 𝓘 ∧ J i ∈ 𝓙) ∧
    ∀ i : Fin k,
      (∀ j : Fin k, i ≤ j → f (x j, y i.castSucc) ∈ I i) ∧
      (∀ j : Fin (k + 1), i.val < j.val → f (x i, y j) ∈ J i) ∧
      (((r i : ℝ) < (f (x i, y i.castSucc) : ℝ) ∧
          ∀ j : Fin (k + 1), i.val < j.val →
            (f (x i, y j) : ℝ) ≤ (r i : ℝ) - γ) ∨
       ((f (x i, y i.castSucc) : ℝ) ≤ (r i : ℝ) ∧
          ∀ j : Fin (k + 1), i.val < j.val →
            (r i : ℝ) + γ ≤ (f (x i, y j) : ℝ)))

/-- Existence of the source's three sequences with the covered proto-ladder clauses. -/
def AdmitsCoveredProtoLadder {X : Type*} {Y : Type*}
    (f : X × Y → Set.Icc (0 : ℝ) 1) (k : ℕ) (γ : ℝ)
    (𝓘 𝓙 : Set (Set (Set.Icc (0 : ℝ) 1))) : Prop :=
  ∃ (x : Fin k → X) (y : Fin (k + 1) → Y)
    (r : Fin k → Set.Icc (0 : ℝ) 1), IsCoveredProtoLadder f k γ 𝓘 𝓙 x y r

end ConantTerry.Orders.Supplement


