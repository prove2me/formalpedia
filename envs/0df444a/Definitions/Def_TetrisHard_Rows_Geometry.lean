-- Prove2me | Definitions.Def_TetrisHard_Rows_Geometry
-- name    : TetrisHard_Rows_Geometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:53:26.967523+00:00
-- url     : https://prove2.me/theorems/bb42d8b8-1ee9-4d3b-8884-22d8797e48d5
-- title:
--   Bucket shapes and the eight forbidden configurations
-- statement:
--   Bucket-local integer coordinates describe open notches, balconies with exactly one empty working-column cell, maximal vertical verandas, and empty-cell connected components. A hole is disconnected from the region above the buckets. The eight forbidden patterns retain all floor alternatives 110, 011, 111; the sub-notch depth range 1 to 3; nonmultiples-of-four verandas lying in non-notch rows or rows with both notch cells filled; 2-verandas; and both ceiling-discrepancy cases with α≥1 and 1≤β≤3. Patterns lie in the original bucket height, not the staging area. Exact occupancy templates describe unprepped, overflat, tall-plateau, trigger-happy and unapproachable buckets from Figures 6, 8 and 11. One-shape and two-shape configurations require all other buckets to be unprepped, with distinct exceptional buckets in the latter case. Unfillability means that no finite number of LG, LS, square or I pieces, placed by actual trajectories within the bucket without row deletion, can fill it through its original height. It is not defined by the forbidden-pattern list. Verandas range over all five potentially empty bucket columns. In the tall plateau, the nine-cell first-column gap ends at the filled height h with (h+2) mod 6 = 5: one completely empty working-column row separates that plateau from the next notch, as in Figure 8(d).
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, §§5.2–5.4, pp. 13–17; Appendix B, pp. 31–33; Figure 11, p. 34, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Reduction

namespace TetrisHard.Rows

/-- Bucket-local coordinates: x=0,1,2 are the three working columns. -/
def bucketCell (B : Board) (j : ℕ) (x y : ℤ) : Bool :=
  B.occupied (6 * (j : ℤ) + x, y)

def OpenNotch (B : Board) (j H : ℕ) (y : ℤ) : Prop :=
  0 ≤ y ∧ y < H ∧ (y + 1) % 6 = 5 ∧
    bucketCell B j 3 y = false ∧ bucketCell B j 4 y = false

def Balcony (B : Board) (j H : ℕ) (y : ℤ) (i : Fin 3) : Prop :=
  0 ≤ y ∧ y < H ∧ ∀ x : Fin 3, bucketCell B j x.val y = decide (x ≠ i)

def HasBalconyAbove (B : Board) (j H : ℕ) (y : ℤ) : Prop :=
  ∃ b i, y < b ∧ Balcony B j H b i

def EmptyAdjacent (B : Board) (z z' : Cell) : Prop :=
  B.occupied z = false ∧ B.occupied z' = false ∧
    |z.1 - z'.1| + |z.2 - z'.2| = 1

def HasHole (B : Board) (j H : ℕ) : Prop :=
  ∃ x y : ℤ, 0 ≤ x ∧ x < 5 ∧ 0 ≤ y ∧ y < H ∧ bucketCell B j x y = false ∧
    ¬ ∃ z : Cell, (H : ℤ) ≤ z.2 ∧ B.occupied z = false ∧
      Relation.ReflTransGen (EmptyAdjacent B) (6 * (j : ℤ) + x, y) z

def SpurnedNotch (B : Board) (j H : ℕ) : Prop :=
  ∃ y, OpenNotch B j H y ∧ bucketCell B j 1 y = true

/-- A maximal vertical run, with occupied sentinels allowed at the floor or top. -/
def Veranda (B : Board) (j H : ℕ) (i : Fin 5) (bottom : ℤ) (length : ℕ) : Prop :=
  0 < length ∧ 0 ≤ bottom ∧ bottom + length ≤ H ∧
  (∀ y : ℤ, bottom ≤ y → y < bottom + length → bucketCell B j i.val y = false) ∧
  bucketCell B j i.val (bottom - 1) = true ∧ bucketCell B j i.val (bottom + length) = true

def FlooredNotch (B : Board) (j H : ℕ) : Prop :=
  ∃ y, OpenNotch B j H y ∧ HasBalconyAbove B j H y ∧
    ((bucketCell B j 0 (y-1) = true ∧ bucketCell B j 1 (y-1) = true ∧ bucketCell B j 2 (y-1) = false) ∨
     (bucketCell B j 0 (y-1) = false ∧ bucketCell B j 1 (y-1) = true ∧ bucketCell B j 2 (y-1) = true) ∨
     (bucketCell B j 0 (y-1) = true ∧ bucketCell B j 1 (y-1) = true ∧ bucketCell B j 2 (y-1) = true))

def SubNotchRectangle (B : Board) (j H : ℕ) : Prop :=
  ∃ y i d : ℤ, OpenNotch B j H y ∧ HasBalconyAbove B j H y ∧
    (i = 1 ∨ i = 2) ∧ 1 ≤ d ∧ d ≤ 3 ∧
    (∀ z : ℤ, y-d ≤ z → z ≤ y → bucketCell B j i z = false) ∧
    bucketCell B j i (y-d-1) = true

def BadNonNotchVeranda (B : Board) (j H : ℕ) : Prop :=
  ∃ i bottom length, Veranda B j H i bottom length ∧ length % 4 ≠ 0 ∧
    HasBalconyAbove B j H (bottom + length - 1) ∧
    ∀ y : ℤ, bottom ≤ y → y < bottom + length →
      (y + 1) % 6 ≠ 5 ∨ (bucketCell B j 3 y = true ∧ bucketCell B j 4 y = true)

def TwoVeranda (B : Board) (j H : ℕ) : Prop :=
  ∃ i bottom, Veranda B j H i bottom 2 ∧ HasBalconyAbove B j H bottom

/-- The common ceiling pattern of the two discrepancy cases (p. 15). -/
def CeilingDiscrepancy (B : Board) (j H : ℕ) (h : ℤ) (α β : ℕ) : Prop :=
  1 ≤ α ∧ 1 ≤ β ∧ β ≤ 3 ∧ HasBalconyAbove B j H h ∧
  (∀ y : ℤ, h ≤ y → y ≤ h + α → bucketCell B j 1 y = false ∧ bucketCell B j 2 y = false) ∧
  ∃ i k : ℤ, ((i = 1 ∧ k = 2) ∨ (i = 2 ∧ k = 1)) ∧
    (∀ y : ℤ, h + α + 1 ≤ y → y ≤ h + α + β → bucketCell B j i y = false) ∧
    bucketCell B j i (h + α + β + 1) = true ∧ bucketCell B j k (h + α + 1) = true

def FlatDiscrepancy (B : Board) (j H : ℕ) : Prop :=
  ∃ h α β, CeilingDiscrepancy B j H h α β ∧
    bucketCell B j 1 (h-1) = true ∧ bucketCell B j 2 (h-1) = true

def NotchDiscrepancy (B : Board) (j H : ℕ) : Prop :=
  ∃ h α β, CeilingDiscrepancy B j H h α β ∧
    ∃ y : ℤ, h ≤ y ∧ y ≤ h + α ∧ OpenNotch B j H y

/-- Added cells of an exact bucket pattern, superposed on the fixed side walls.
The initial four filled cells in columns 1 and 2 are not part of the side walls. -/
def BucketPattern (B : Board) (j H : ℕ) (filled : ℕ → ℕ → Bool) : Prop :=
  ∀ x : Fin 6, ∀ y : Fin B.height,
    bucketCell B j x.val y.val =
      ((decide (y.val < H ∧ (x.val = 5 ∨
        (3 ≤ x.val ∧ (y.val + 1) % 6 ≠ 5)))) || filled x.val y.val)

def Unprepped (B : Board) (j H : ℕ) : Prop :=
  ∃ h gap : ℕ, 4 ≤ h ∧ h ≤ B.height ∧ (h + 1) % 6 = 5 ∧ (gap = 0 ∨ gap = 2) ∧
    BucketPattern B j H (fun x y => decide (x < 5 ∧ y < h ∧ ¬ (x = gap ∧ h ≤ y + 4)))

def Overflat (B : Board) (j H : ℕ) : Prop :=
  ∃ h : ℕ, 0 < h ∧ h ≤ B.height ∧ h % 6 = 0 ∧
    BucketPattern B j H (fun x y => decide (x < 5 ∧ y < h))

def TallPlateau (B : Board) (j H : ℕ) : Prop :=
  ∃ h : ℕ, 9 ≤ h ∧ h ≤ B.height ∧ (h + 2) % 6 = 5 ∧
    BucketPattern B j H (fun x y => decide (x < 5 ∧ y < h ∧ ¬ (x = 0 ∧ h ≤ y + 9)))

def TriggerHappy (B : Board) (j H : ℕ) : Prop :=
  ∃ h : ℕ, 2 ≤ h ∧ h ≤ B.height ∧ (h + 1) % 6 = 5 ∧
    BucketPattern B j H (fun x y => decide (x < 5 ∧ y + 1 < h ∧ ¬ (x = 2 ∧ y + 2 = h)))

/-- Figure 6: below the first open notch n, columns 2--3 reach n-2 and
column 1 reaches n-3; above that profile the bucket is empty. -/
def Unapproachable (B : Board) (j H : ℕ) : Prop :=
  ∃ n : ℕ, 3 ≤ n ∧ n ≤ H ∧ n % 6 = 5 ∧
    BucketPattern B j H (fun x y => decide
      (x < 5 ∧ (if x = 0 then y + 3 < n else y + 2 < n)))

def AllUnprepped (B : Board) (s H : ℕ) : Prop :=
  ∀ j : Fin s, Unprepped B j.val H

def One (shape : Board → ℕ → ℕ → Prop) (B : Board) (s H : ℕ) (j : Fin s) : Prop :=
  shape B j.val H ∧ ∀ k : Fin s, k ≠ j → Unprepped B k.val H

def OneEach (shape₁ shape₂ : Board → ℕ → ℕ → Prop) (B : Board) (s H : ℕ)
    (j k : Fin s) : Prop :=
  j ≠ k ∧ shape₁ B j.val H ∧ shape₂ B k.val H ∧
    ∀ l : Fin s, l ≠ j → l ≠ k → Unprepped B l.val H

/-- Arbitrarily many allowed pieces, with actual trajectories and without row deletion. -/
inductive FillPlay (R : Rotation) (j : ℕ) : Board → Board → Prop
  | nil (B) : FillPlay R j B B
  | step {B B' q} : q.kind ∈ ([.LG, .LS, .Sq, .I] : List Piece) →
      InBucket j q → Trajectory R B q.kind q → FillPlay R j (B.insert q) B' →
      FillPlay R j B B'

def Unfillable (R : Rotation) (B : Board) (j H : ℕ) : Prop :=
  ¬ ∃ B', FillPlay R j B B' ∧ BucketFull B' j H

end TetrisHard.Rows


