-- Prove2me | Definitions.Def_TetrisHard_Rows_Reasonable
-- name    : TetrisHard_Rows_Reasonable
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:54:32.600987+00:00
-- url     : https://prove2.me/theorems/1d56af89-aff9-4d59-b81a-bf6734fa0230
-- title:
--   The four reasonable-rotation conditions
-- statement:
--   A reasonable model preserves empty-cell connected regions, does not jump directly between buckets below their walls, prevents an LG from fully entering a spurned notch, restricts non-I pieces below a balcony to the open column in its two top rows, and prevents an I from fully entering a notch whose second and third floor cells are occupied. These are geometric conditions on legal steps and states reachable from the prescribed spawn above the buckets. Bucket frames retain the walls, notch spacing, source height H=6T+22 and at least three staging rows; no completeness, soundness, or hardness assertion is part of reasonability. A fixed staging allowance of 2r+8 for neighborhood radius r chooses the source’s constant staging term; its sufficiency is an obligation of completeness.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, §5.3, p. 16; Appendix A, pp. 26–28; §3, p. 8, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_TetrisHard_Rows_Geometry

namespace TetrisHard.Rows

def Reachable (R : Rotation) (B : Board) (H : ℕ) (t : Piece) (q : PieceState) : Prop :=
  (∀ z ∈ (spawn B t).cells, (H : ℤ) ≤ z.2) ∧
  B.Clear (spawn B t) ∧ Relation.ReflTransGen (Move R B) (spawn B t) q

/-- The four geometric conditions of Section 5.3. No reduction or complexity claim
is part of this predicate. Regions are edge-connected components of empty cells. -/
def Reasonable (R : Rotation) : Prop :=
  (∀ (B : Board) q q', Move R B q q' →
    ∀ z ∈ q.cells, ∀ z' ∈ q'.cells,
      Relation.ReflTransGen (EmptyAdjacent B) z z') ∧
  (∀ (B : Board) s H, BucketFrame B s H →
    ∀ q q', Move R B q q' →
      (∀ z ∈ q.cells, z.2 < H) → (∀ z ∈ q'.cells, z.2 < H) →
      ∀ j : Fin s, InBucket j.val q → InBucket j.val q') ∧
  (∀ (B : Board) s H, BucketFrame B s H → ∀ (j : Fin s) y q,
    OpenNotch B j.val H y → bucketCell B j.val 1 y = true →
    Reachable R B H .LG q →
    ¬ ((6 * (j.val : ℤ) + 3, y) ∈ q.cells ∧ (6 * (j.val : ℤ) + 4, y) ∈ q.cells)) ∧
  (∀ (B : Board) s H, BucketFrame B s H → ∀ (j : Fin s) h i t q,
    Balcony B j.val H h i → h < H → t ≠ .I → Reachable R B H t q →
    ∀ z ∈ q.cells, 6 * (j.val : ℤ) ≤ z.1 → z.1 < 6 * (j.val : ℤ) + 5 → z.2 ≤ h →
      z.1 = 6 * (j.val : ℤ) + i.val ∧ (z.2 = h ∨ z.2 = h-1)) ∧
  (∀ (B : Board) s H, BucketFrame B s H → ∀ (j : Fin s) y q,
    OpenNotch B j.val H y → bucketCell B j.val 1 (y-1) = true →
    bucketCell B j.val 2 (y-1) = true → Reachable R B H .I q →
    ¬ ((6 * (j.val : ℤ) + 3, y) ∈ q.cells ∧ (6 * (j.val : ℤ) + 4, y) ∈ q.cells))

/-- A fixed allowance, independent of the instance. Sufficiency is part of completeness. -/
def stagingAllowance (R : Rotation) : ℕ := 2 * R.radius + 8

end TetrisHard.Rows


