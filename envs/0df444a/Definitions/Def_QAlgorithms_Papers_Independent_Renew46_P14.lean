-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P14
-- name    : QAlgorithms_Papers_Independent_Renew46_P14
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:13:21.067495+00:00
-- url     : https://prove2.me/theorems/aedb111e-16b0-4986-9792-3941484f8ddd
-- title:
--   Definitions for Exceptional Lie Algebras, SU(3) and Jordan Pairs
-- statement:
--   The objects the formalized statements of *Exceptional Lie Algebras, SU(3) and Jordan Pairs* (arXiv:1112.1258) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `V`: The paper's real coordinate ambient space, Table 2, PDF p. 6.
--   - `k`: The fixed orthonormal coordinate vectors; index zero is k_1, PDF p. 5.
--   - `firstThreeSum`: The sum of the first three coordinate vectors.
--   - `rootProjection`: Orthogonal projection to Π = span(k_1-k_2,k_2-k_3), PDF p. 5.
--   - `externalWeight`: The three oriented weights of the external 3, PDF p. 7.
--   - `cycleFirstThree`: Cyclic permutation k_1 → k_2 → k_3 → k_1, with all other axes fixed.
--   - `sign`: Independent signs: true is positive, false is negative.
--   - `plusCount`: Number of plus signs among the first r entries of a sign vector.
--   - `halfSums`: All half-sums in a specified coordinate frame, restricted by a sign predicate.
--   - `signed`: Adjoin the negatives of a finite set; an outer ± negates the whole vector.
--   - `differences`: The A-type differences on a specified set of coordinate axes.
--   - `dRoots`: The D-type coordinate roots ±k_i±k_j for distinct indices.
--   - `external`: External A2 hexagon, PDF pp. 5–7.
--   - `isA2`: A six-root A2 system specified by two simple roots and their squared length.
--   - `rootsG2`: Table 2 G2 roots, PDF p. 6.
--   - `rootsF4`: Table 2 F4 roots, PDF p. 6.
--   - `rootsE6`: Table 2 E6 roots; parity includes all six signs, PDF p. 6.
--   - `rootsE7`: Table 2 E7 roots; even parity on the first SIX signs, k_7 sign free. The scope of the printed parity instruction is fixed by the eta correspondence, pp. 15–16.
--   - `rootsE8`: Table 2 E8 roots; even parity over eight expanded coefficients, PDF p. 6.
--   - `block1`: The six roots (4.2), PDF p. 9.
--   - `center1`: The central six roots (4.3), PDF p. 9.
--   - `block2`: The nine roots (4.4), PDF p. 11.
--   - `center2First`: First central A2 factor, §4.2.2, PDF p. 11.
--   - `center2Second`: Second central A2 factor, §4.2.2, PDF p. 11.
--   - `center2`: The central twelve roots, §4.2.2, PDF p. 11.
--   - `block4`: The fifteen roots (4.5), corrected using eta_3+eta_5 on p. 16. The third half-root family has +k_6, rather than the printed -k_6.
--   - `center4`: The thirty central roots, §4.3.2, PDF p. 15. Inside the outer ±, even parity counts the six coefficients k_1,...,k_6.
--   - `block8`: The twenty-seven roots (4.6), PDF p. 17; parity on the five free signs.
--   - `center8`: The seventy-two roots (4.7), PDF p. 18. With the first three coefficients positive, the five free signs have ODD plus parity. An outer minus negates the entire vector.
--   - `orientedBlock`: A cyclic block and its opposite, with true choosing the positive orientation.
--   - `Piece`: Indices of the external, central, and six pair-root blocks.
--   - `piece`: The eight pieces of the root pattern, PDF Fig. 3.
--   - `rootPartition`: Exact disjoint root partition, including multiplicities and orthogonal projections. This predicate concerns finite root sets, not Jordan products or Lie ideals.
--   - `d6Frame`: The six eta vectors defined in §4.3.2, PDF p. 15.
--   - `etaDifferences`: All ordered eta differences, with distinct indices.
--   - `etaSums`: Distinct unordered eta sums, so no repeated-index junk values occur.
--   - `etaD6`: The D6 root system in the displayed eta frame.
--   - `planeFrame`: The two orthogonal central A2 plane frames, PDF p. 12.
--   - `firstPlaneOffsets`: Offsets u_i, PDF p. 12.
--   - `secondPlaneOffsets`: Offsets v_i, PDF p. 12.
--   - `tableWeights`: The three displayed weights in Table 3, PDF p. 13.
--   - `tableRoot`: The nine Table 3 roots, PDF p. 13. Entry (3,2) is corrected from the duplicated (1,2) entry using u_3,v_2 on p. 12. The printed minus plane headings are corrected to plus, as fixed by those offsets.
--   - `plane`: An affine two-plane with the specified directions.
--   - `rebaseE6`: The E6 change of frame on PDF p. 18.
--   - `rebaseE7`: The E7 change of frame on PDF p. 18.
--   - `zInner`: The inner flavor-axis coordinate sum, PDF p. 21.
--   - `innerBlock`: The nine-root inner block for family f+4, PDF p. 21. Membership in the original even-parity E8 set resolves the compact sign instruction.
--   - `nestedA2`: Four explicit six-root sets on PDF p. 21; labels c,f,g1,g2 are only indices.
--   - `NestedPiece`: Indices for four A2 sets, three outer pairs, and three inner pairs.
--   - `nestedPiece`: The sixteen disjoint pieces of the explicit E8 root list, PDF p. 21.
-- source:
--   Exceptional Lie Algebras, SU(3) and Jordan Pairs, arXiv:1112.1258v2, https://arxiv.org/abs/1112.1258v2

import Mathlib

/-!
Coordinate statements from Truini, arXiv:1112.1258v2. The root coordinates are real,
although the Lie algebras in the paper are complex. Indices in this file are zero-based:
`k 0` is the paper's k_1. No direct sum of root sets is asserted to be a Lie direct sum.
The Lie/Jordan identifications that require further concrete models are deferred in HARD.md.
The scalar product is Mathlib `dotProduct`. Other coordinate definitions are paper-local;
similarly named accepted quantum/acoustic objects have different domains and meanings.
-/

namespace QAlgorithms.Papers.Independent.Renew46.P14

noncomputable section

open scoped BigOperators

/-- The paper's real coordinate ambient space, Table 2, PDF p. 6. -/
abbrev V := Fin 8 → ℝ

local instance : DecidableEq V := Classical.decEq V

attribute [local instance] Classical.propDecidable

/-- The fixed orthonormal coordinate vectors; index zero is k_1, PDF p. 5. -/
def k (i : Fin 8) : V := fun j => if j = i then 1 else 0

/-- The sum of the first three coordinate vectors. -/
def firstThreeSum : V := k 0 + k 1 + k 2

/-- Orthogonal projection to Π = span(k_1-k_2,k_2-k_3), PDF p. 5. -/
def rootProjection (x : V) : V := fun j =>
  if j.val < 3 then x j - (x 0 + x 1 + x 2) / 3 else 0

/-- The three oriented weights of the external 3, PDF p. 7. -/
def externalWeight (i : Fin 3) : V := (1 / 3 : ℝ) • (firstThreeSum - (3 : ℝ) • k ⟨i.val, by omega⟩)

/-- Cyclic permutation k_1 → k_2 → k_3 → k_1, with all other axes fixed. -/
def cycleFirstThree (c : Fin 3) (x : V) : V := fun j =>
  if j.val < 3 then x ⟨(j.val + 3 - c.val) % 3, by omega⟩ else x j

/-- Independent signs: true is positive, false is negative. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

/-- Number of plus signs among the first r entries of a sign vector. -/
def plusCount {m : ℕ} (r : ℕ) (s : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => i.val < r ∧ s i = true).card

/-- All half-sums in a specified coordinate frame, restricted by a sign predicate. -/
def halfSums {m : ℕ} (a : Fin m → V) (p : (Fin m → Bool) → Prop) : Finset V :=
  (Finset.univ.filter p).image fun s => (1 / 2 : ℝ) • ∑ i, sign (s i) • a i

/-- Adjoin the negatives of a finite set; an outer ± negates the whole vector. -/
def signed (S : Finset V) : Finset V := S ∪ S.image (fun x => -x)

/-- The A-type differences on a specified set of coordinate axes. -/
def differences (I : Finset (Fin 8)) : Finset V :=
  I.biUnion fun i => (I.erase i).image fun j => k i - k j

/-- The D-type coordinate roots ±k_i±k_j for distinct indices. -/
def dRoots (I : Finset (Fin 8)) : Finset V :=
  I.biUnion fun i => (I.erase i).biUnion fun j =>
    {k i + k j, k i - k j, -k i + k j, -k i - k j}

/-- External A2 hexagon, PDF pp. 5–7. -/
def external : Finset V := differences {0, 1, 2}

/-- A six-root A2 system specified by two simple roots and their squared length. -/
def isA2 (R : Finset V) (a b : V) (lengthSq : ℝ) : Prop :=
  R = signed {a, b, a + b} ∧ dotProduct a a = lengthSq ∧
    dotProduct b b = lengthSq ∧ dotProduct a b = -lengthSq / 2

/-- Table 2 G2 roots, PDF p. 6. -/
def rootsG2 : Finset V := external ∪ signed (Finset.univ.image externalWeight)

/-- Table 2 F4 roots, PDF p. 6. -/
def rootsF4 : Finset V :=
  signed (({0, 1, 2, 3} : Finset (Fin 8)).image k) ∪ dRoots {0, 1, 2, 3} ∪
    halfSums ![k 0, k 1, k 2, k 3] (fun _ => True)

/-- Table 2 E6 roots; parity includes all six signs, PDF p. 6. -/
def rootsE6 : Finset V := dRoots {0, 1, 2, 3, 4} ∪
  halfSums ![k 0, k 1, k 2, k 3, k 4, Real.sqrt (3 : ℝ) • k 5]
    (fun s => plusCount 6 s % 2 = 1)

/-- Table 2 E7 roots; even parity on the first SIX signs, k_7 sign free.
The scope of the printed parity instruction is fixed by the eta correspondence, pp. 15–16. -/
def rootsE7 : Finset V :=
  signed {Real.sqrt (2 : ℝ) • k 6} ∪ dRoots {0, 1, 2, 3, 4, 5} ∪
    halfSums ![k 0, k 1, k 2, k 3, k 4, k 5, Real.sqrt (2 : ℝ) • k 6]
      (fun s => plusCount 6 s % 2 = 0)

/-- Table 2 E8 roots; even parity over eight expanded coefficients, PDF p. 6. -/
def rootsE8 : Finset V := dRoots Finset.univ ∪
  halfSums k (fun s => plusCount 8 s % 2 = 0)

/-- The six roots (4.2), PDF p. 9. -/
def block1 : Finset V :=
  {-k 0, -k 0 + k 3, -k 0 - k 3,
   (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 + k 3),
   (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 - k 3), k 1 + k 2}

/-- The central six roots (4.3), PDF p. 9. -/
def center1 : Finset V := signed
  {k 3, (1 / 2 : ℝ) • (firstThreeSum + k 3), (1 / 2 : ℝ) • (firstThreeSum - k 3)}

/-- The nine roots (4.4), PDF p. 11. -/
def block2 : Finset V :=
  {-k 0 + k 3, -k 0 - k 3, -k 0 + k 4, -k 0 - k 4, k 1 + k 2,
   (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 + k 3 - k 4 - Real.sqrt (3 : ℝ) • k 5),
   (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 + k 3 + k 4 + Real.sqrt (3 : ℝ) • k 5),
   (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 - k 3 + k 4 - Real.sqrt (3 : ℝ) • k 5),
   (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 - k 3 - k 4 + Real.sqrt (3 : ℝ) • k 5)}

/-- First central A2 factor, §4.2.2, PDF p. 11. -/
def center2First : Finset V := signed
  {k 3 + k 4, (1 / 2 : ℝ) • (firstThreeSum - k 3 - k 4 - Real.sqrt (3 : ℝ) • k 5),
   (1 / 2 : ℝ) • (firstThreeSum + k 3 + k 4 - Real.sqrt (3 : ℝ) • k 5)}

/-- Second central A2 factor, §4.2.2, PDF p. 11. -/
def center2Second : Finset V := signed
  {k 3 - k 4, (1 / 2 : ℝ) • (firstThreeSum - k 3 + k 4 + Real.sqrt (3 : ℝ) • k 5),
   (1 / 2 : ℝ) • (firstThreeSum + k 3 - k 4 + Real.sqrt (3 : ℝ) • k 5)}

/-- The central twelve roots, §4.2.2, PDF p. 11. -/
def center2 : Finset V := center2First ∪ center2Second

/-- The fifteen roots (4.5), corrected using eta_3+eta_5 on p. 16.
The third half-root family has +k_6, rather than the printed -k_6. -/
def block4 : Finset V :=
  {k 1 + k 2} ∪
  (({3, 4, 5} : Finset (Fin 8)).biUnion fun j => {-k 0 + k j, -k 0 - k j}) ∪
  ((Finset.univ.filter fun s : Fin 3 → Bool => plusCount 3 s % 2 = 0).biUnion
    fun s => Finset.univ.image fun b : Bool => (1 / 2 : ℝ) •
      (-k 0 + k 1 + k 2 + (∑ i : Fin 3, sign (s i) • k ⟨i.val + 3, by omega⟩)
        + sign b • (Real.sqrt (2 : ℝ) • k 6)))

/-- The thirty central roots, §4.3.2, PDF p. 15.
Inside the outer ±, even parity counts the six coefficients k_1,...,k_6. -/
def center4 : Finset V := dRoots {3, 4, 5} ∪ signed {Real.sqrt (2 : ℝ) • k 6} ∪
  signed ((Finset.univ.filter fun s : Fin 3 → Bool => plusCount 3 s % 2 = 1).biUnion
    fun s => Finset.univ.image fun b : Bool => (1 / 2 : ℝ) •
      (firstThreeSum + (∑ i : Fin 3, sign (s i) • k ⟨i.val + 3, by omega⟩)
        + sign b • (Real.sqrt (2 : ℝ) • k 6)))

/-- The twenty-seven roots (4.6), PDF p. 17; parity on the five free signs. -/
def block8 : Finset V := {k 1 + k 2} ∪
  (({3, 4, 5, 6, 7} : Finset (Fin 8)).biUnion fun j => {-k 0 + k j, -k 0 - k j}) ∪
  ((Finset.univ.filter fun s : Fin 5 → Bool => plusCount 5 s % 2 = 0).image
    fun s => (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 +
      ∑ i : Fin 5, sign (s i) • k ⟨i.val + 3, by omega⟩))

/-- The seventy-two roots (4.7), PDF p. 18.
With the first three coefficients positive, the five free signs have ODD plus parity.
An outer minus negates the entire vector. -/
def center8 : Finset V := dRoots {3, 4, 5, 6, 7} ∪
  signed ((Finset.univ.filter fun s : Fin 5 → Bool => plusCount 5 s % 2 = 1).image
    fun s => (1 / 2 : ℝ) • (firstThreeSum +
      ∑ i : Fin 5, sign (s i) • k ⟨i.val + 3, by omega⟩))

/-- A cyclic block and its opposite, with true choosing the positive orientation. -/
def orientedBlock (B : Finset V) (c : Fin 3) (positive : Bool) : Finset V :=
  if positive then B.image (cycleFirstThree c) else (B.image (cycleFirstThree c)).image (fun x => -x)

/-- Indices of the external, central, and six pair-root blocks. -/
abbrev Piece := Bool ⊕ (Fin 3 × Bool)

/-- The eight pieces of the root pattern, PDF Fig. 3. -/
def piece (C B : Finset V) : Piece → Finset V
  | .inl false => external
  | .inl true => C
  | .inr (c, b) => orientedBlock B c b

/-- Exact disjoint root partition, including multiplicities and orthogonal projections.
This predicate concerns finite root sets, not Jordan products or Lie ideals. -/
def rootPartition (R C B : Finset V) (centralSize blockSize : ℕ) : Prop :=
  R = Finset.univ.biUnion (piece C B) ∧
  (∀ i j : Piece, i ≠ j → Disjoint (piece C B i) (piece C B j)) ∧
  R.card = 6 + centralSize + 6 * blockSize ∧ external.card = 6 ∧
  C.card = centralSize ∧
  (∀ c b, (orientedBlock B c b).card = blockSize) ∧
  (∀ x ∈ C, rootProjection x = 0) ∧ (∀ x ∈ external, rootProjection x = x) ∧
  (∀ c b, ∀ x ∈ orientedBlock B c b,
    rootProjection x = if b then externalWeight c else -externalWeight c)

/-- The six eta vectors defined in §4.3.2, PDF p. 15. -/
def d6Frame : Fin 6 → V :=
  ![(1 / 2 : ℝ) • (-k 0 - k 3 - k 4 - k 5),
    (1 / 2 : ℝ) • (-k 0 - k 3 + k 4 + k 5),
    (1 / 2 : ℝ) • (-k 0 + k 3 - k 4 + k 5),
    (1 / 2 : ℝ) • (-k 0 + k 3 + k 4 - k 5),
    (1 / 2 : ℝ) • (k 1 + k 2 + Real.sqrt (2 : ℝ) • k 6),
    (1 / 2 : ℝ) • (k 1 + k 2 - Real.sqrt (2 : ℝ) • k 6)]

/-- All ordered eta differences, with distinct indices. -/
def etaDifferences : Finset V := Finset.univ.biUnion fun i : Fin 6 =>
  (Finset.univ.erase i).image fun j => d6Frame i - d6Frame j

/-- Distinct unordered eta sums, so no repeated-index junk values occur. -/
def etaSums : Finset V := Finset.univ.biUnion fun i : Fin 6 =>
  (Finset.univ.filter fun j : Fin 6 => i < j).image fun j => d6Frame i + d6Frame j

/-- The D6 root system in the displayed eta frame. -/
def etaD6 : Finset V := Finset.univ.biUnion fun i : Fin 6 =>
  (Finset.univ.filter fun j : Fin 6 => i < j).biUnion fun j =>
    {d6Frame i + d6Frame j, d6Frame i - d6Frame j, -d6Frame i + d6Frame j, -d6Frame i - d6Frame j}

/-- The two orthogonal central A2 plane frames, PDF p. 12. -/
def planeFrame : Fin 4 → V :=
  ![(Real.sqrt 2 / 2) • (k 3 + k 4),
    (Real.sqrt 6 / 6) • (firstThreeSum - Real.sqrt (3 : ℝ) • k 5),
    (Real.sqrt 2 / 2) • (k 3 - k 4),
    (Real.sqrt 6 / 6) • (firstThreeSum + Real.sqrt (3 : ℝ) • k 5)]

/-- Offsets u_i, PDF p. 12. -/
def firstPlaneOffsets : Fin 3 → V :=
  ![(1 / 6 : ℝ) • ((-5 : ℝ) • k 0 + k 1 + k 2 + (3 : ℝ) • k 3 - (3 : ℝ) • k 4 - Real.sqrt (3 : ℝ) • k 5),
    (1 / 3 : ℝ) • (-k 0 + (2 : ℝ) • k 1 + (2 : ℝ) • k 2 + Real.sqrt (3 : ℝ) • k 5),
    (1 / 6 : ℝ) • ((-5 : ℝ) • k 0 + k 1 + k 2 - (3 : ℝ) • k 3 + (3 : ℝ) • k 4 - Real.sqrt (3 : ℝ) • k 5)]

/-- Offsets v_i, PDF p. 12. -/
def secondPlaneOffsets : Fin 3 → V :=
  ![(1 / 6 : ℝ) • ((-5 : ℝ) • k 0 + k 1 + k 2 + (3 : ℝ) • k 3 + (3 : ℝ) • k 4 + Real.sqrt (3 : ℝ) • k 5),
    (1 / 3 : ℝ) • (-k 0 + (2 : ℝ) • k 1 + (2 : ℝ) • k 2 - Real.sqrt (3 : ℝ) • k 5),
    (1 / 6 : ℝ) • ((-5 : ℝ) • k 0 + k 1 + k 2 - (3 : ℝ) • k 3 - (3 : ℝ) • k 4 + Real.sqrt (3 : ℝ) • k 5)]

/-- The three displayed weights in Table 3, PDF p. 13. -/
def tableWeights : Fin 3 → ℝ × ℝ :=
  ![(Real.sqrt 2 / 2, -Real.sqrt 6 / 6),
    (0, Real.sqrt 6 / 3), (-Real.sqrt 2 / 2, -Real.sqrt 6 / 6)]

/-- The nine Table 3 roots, PDF p. 13.
Entry (3,2) is corrected from the duplicated (1,2) entry using u_3,v_2 on p. 12.
The printed minus plane headings are corrected to plus, as fixed by those offsets. -/
def tableRoot (i j : Fin 3) : V :=
  (![![-k 0 + k 3,
      (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 + k 3 - k 4 - Real.sqrt (3 : ℝ) • k 5), -k 0 - k 4],
     ![(1 / 2 : ℝ) • (-k 0 + k 1 + k 2 + k 3 + k 4 + Real.sqrt (3 : ℝ) • k 5), k 1 + k 2,
      (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 - k 3 - k 4 + Real.sqrt (3 : ℝ) • k 5)],
     ![-k 0 + k 4,
      (1 / 2 : ℝ) • (-k 0 + k 1 + k 2 - k 3 + k 4 - Real.sqrt (3 : ℝ) • k 5), -k 0 - k 3]] i) j

/-- An affine two-plane with the specified directions. -/
def plane (a b c : V) : Set V := {x | ∃ s t : ℝ, x = a + s • b + t • c}

/-- The E6 change of frame on PDF p. 18. -/
def rebaseE6 (x : V) : V :=
  (∑ i : Fin 5, x ⟨i.val, by omega⟩ • k ⟨i.val + 3, by omega⟩) -
    (x 5 / Real.sqrt 3) • firstThreeSum

/-- The E7 change of frame on PDF p. 18. -/
def rebaseE7 (x : V) : V :=
  (∑ i : Fin 5, x ⟨i.val, by omega⟩ • k ⟨i.val + 3, by omega⟩) +
    x (5 : Fin 8) • k 0 + (x 6 / Real.sqrt 2) • (k 1 + k 2)

/-- The inner flavor-axis coordinate sum, PDF p. 21. -/
def zInner : V := k 3 + k 4 + k 5

/-- The nine-root inner block for family f+4, PDF p. 21.
Membership in the original even-parity E8 set resolves the compact sign instruction. -/
def innerBlock (f : Fin 3) : Finset V :=
  let a := k ⟨f.val + 3, by omega⟩
  {-a + k 6, -a - k 6, -a + k 7, -a - k 7, zInner - a} ∪
  ((Finset.univ.image fun s : Fin 3 → Bool =>
    -a + (1 / 2 : ℝ) • (sign (s 0) • firstThreeSum + zInner +
      sign (s 1) • k 6 + sign (s 2) • k 7)).filter fun x => x ∈ rootsE8)

/-- Four explicit six-root sets on PDF p. 21; labels c,f,g1,g2 are only indices. -/
def nestedA2 : Fin 4 → Finset V :=
  ![external, differences {3, 4, 5},
    signed {k 6 + k 7, (1 / 2 : ℝ) • (firstThreeSum + zInner - k 6 - k 7),
      (1 / 2 : ℝ) • (firstThreeSum + zInner + k 6 + k 7)},
    signed {k 6 - k 7, (1 / 2 : ℝ) • (-firstThreeSum + zInner - k 6 + k 7),
      (1 / 2 : ℝ) • (-firstThreeSum + zInner + k 6 - k 7)}]

/-- Indices for four A2 sets, three outer pairs, and three inner pairs. -/
abbrev NestedPiece := Fin 4 ⊕ ((Fin 3 ⊕ Fin 3) × Bool)

/-- The sixteen disjoint pieces of the explicit E8 root list, PDF p. 21. -/
def nestedPiece : NestedPiece → Finset V
  | .inl i => nestedA2 i
  | .inr (.inl c, b) => orientedBlock block8 c b
  | .inr (.inr f, true) => innerBlock f
  | .inr (.inr f, false) => (innerBlock f).image (fun x => -x)

/-- The underlying coordinate frame is fixed, not a free possibly degenerate basis. -/
example (i : Fin 8) : k i i = 1 := by simp [k]

/-- Sign normalization is literal, including the scalar imaginary-unit-independent convention. -/
example : sign true = 1 ∧ sign false = -1 := by simp [sign]

/-- Projection fixes the first coordinate of the displayed simple root. -/
example : rootProjection (k 0 - k 1) 0 = 1 := by norm_num [rootProjection, k, Fin.ext_iff]

end

end QAlgorithms.Papers.Independent.Renew46.P14


