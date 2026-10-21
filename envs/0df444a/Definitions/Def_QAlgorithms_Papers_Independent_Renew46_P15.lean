-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P15
-- name    : QAlgorithms_Papers_Independent_Renew46_P15
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T20:13:33.115734+00:00
-- url     : https://prove2.me/theorems/4ce96df3-f7e7-4221-8546-3ee2fdcd2448
-- title:
--   Definitions for A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients
-- statement:
--   The objects the formalized statements of *A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients* (arXiv:1009.0437) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `GTTopRow`: Normalized dominant integral top row, PDF p.6, (19). This is unrelated to an operator-algebra weight on a positive cone.
--   - `weightLt`: Ordinary lexicographic comparison, PDF p.16, (C1).
--   - `weightRank`: Independent finite counting definition (C2), not the desired formula. Every smaller dominant weight lies inside this box.
--   - `weightRankFormula`: RHS of (C6): subtract one after adding the positive N-k.
--   - `gridEntry`: Zero-based grid coordinates; outside the grid the value is zero.
--   - `IsPattern`: Fixed top row, zero off-triangle storage and betweenness, PDF p.6, (20)-(21).
--   - `Pattern`: All integral GT-patterns of s, with finite storage bounded by s_1. Betweenness implies these bounds; no lower-row determinant shifts are taken.
--   - `patternGrid`: Natural-coordinate view of a stored pattern.
--   - `rowSum`: One-based row sums, with sigma_0=0, PDF p.7.
--   - `zWeight`: Exact J_z eigenvalues (24), with coordinate i corresponding to l=i+1.
--   - `highestZ`: Highest z-weight, invariant under uniform determinant shifts.
--   - `zMatrix`: The diagonal J_z matrix, PDF pp.6-7, (23)-(24).
--   - `loweringSquared`: Squared lowering amplitude (28), PDF p.8; differences are taken in ℝ. Only valid single-entry moves evaluate this formula.
--   - `IsLowerMove`: Single-entry decrement checked in ℤ, avoiding truncated subtraction at zero.
--   - `lowerMatrix`: Exact GT lowering matrices (28), zero for invalid moves, using the nonnegative real square root that fixes the source's GT phases.
--   - `raiseMatrix`: Raising is the real transpose of lowering, PDF p.9, (29).
--   - `tensorGeneratorMatrix`: Primitive generator on the tensor product, PDF p.3, (3b). This is a Kronecker sum, not a tensor product of channel matrices.
--   - `coupledMatrix`: Block sum over a finite list of irreps, retaining repeated labels as copies.
--   - `CGTable`: Definition of a real CG change of orthonormal bases, PDF pp.2-3, (3b),(5),(6a)-(6b). Complex-linear extension gives the same SU(N)/SL(N,C) coefficients. No selection rule, multiplicity count, kernel dimension or reconstruction conclusion is assumed as a field.
--   - `outerMultiplicity`: Outer multiplicity in a full decomposition, counting all repeated labels (2).
--   - `highestKernel`: Product raising kernel restricted to the specified highest z-weight, PDF p.10, (35)-(36); other irreps' highest states are excluded.
--   - `lrIncrement`: l-box count in tableau row k, (A1), using zero-based coordinates.
--   - `lrB`: Corrected B(k,l): sum over the summation index; k counts completed rows.
--   - `lrPositions`: VIII step 2: diagonals k ascending, entries l descending from N-1 to k.
--   - `lrUpdate`: The actual trial update, VIII step 3.
--   - `lrAccepted`: Every intermediate trial weight must stay dominant; no early normalization.
--   - `lrChainWeight`: The chain in (31): B(k,l') on the left, B(k+1,l') on the right. The left segment is empty at zero-based l=0.
--   - `lrFinal`: Final homogeneous trial row.
--   - `lrMultiplicity`: Accepted-pattern count for each normalized output, aggregating determinant shifts after processing all trial weights, PDF pp.9-10.
--   - `positionLt`: C.2 coordinate order: top to bottom, left to right.
--   - `patternLt`: Strict pattern lexicographic order with immutable top row.
--   - `patternRank`: Inclusive one-based mathematical Q in (C7), not the implementation's Q-1.
--   - `patternPositions`: Positions in row order, including the top row.
--   - `predecessorPivot`: Last lower-row entry strictly greater than its lower bound in the row above.
--   - `predecessorReset`: C9 resetting, recursively top to bottom; t is distance below the top. Earlier entries stay fixed and later entries copy their new upper neighbors.
--   - `patternPredecessor`: Partial predecessor. Validity of returned raw grids is a conclusion below.
--   - `HasPredecessorChain`: Exactly t successful predecessor steps followed by None.
--   - `euclideanRow`: Rows are interpreted in the Euclidean norm, never the function sup norm.
--   - `IsRREF`: Mathematical RREF, with unit pivots and no zero rows. The positive scaling freedom in the printed (37) disappears after normalized Gram-Schmidt.
--   - `canonicalRows`: Normalized Gram-Schmidt, from the first RREF row to the last.
--   - `WeightPatterns`: Output weight space indexed by z-weights, avoiding determinant shifts.
--   - `ParentOccurrences`: All parent occurrences (M'',k,l), retaining duplicated parent equations.
--   - `reconstructionMatrix`: Rectangular b of (39)-(40), with all target states as columns.
--   - `reconstructionRHS`: Known RHS of (40), product-lowering each correctly expanded parent.
-- source:
--   A numerical algorithm for the explicit calculation of SU(N) and SL(N,C) Clebsch-Gordan coefficients, arXiv:1009.0437v2, https://arxiv.org/abs/1009.0437v2

import Mathlib

/-!
Alex, Kalus, Huckleberry and von Delft, arXiv:1009.0437v2.
Throughout N=n+2. Normalized integral dominant top rows are nonnegative.
Lower rows are never normalized. The real generator matrices below act by
complex-linear extension on the complex GT carriers. Their real CG tables
are shared by SU(N) and SL(N,C), without asserting that the latter's group
representation matrices are unitary. The operational construction and the
unspecified runtime assertion are deferred; see this unit's HARD.md.
-/

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Renew46.P15

attribute [local instance] Classical.propDecidable

/-- Normalized dominant integral top row, PDF p.6, (19).
This is unrelated to an operator-algebra weight on a positive cone. -/
abbrev GTTopRow (n : ℕ) :=
  {s : Fin (n + 2) → ℕ // Antitone s ∧ s (Fin.last (n + 1)) = 0}

/-- Ordinary lexicographic comparison, PDF p.16, (C1). -/
def weightLt {n : ℕ} (a b : Fin (n + 2) → ℕ) : Prop :=
  ∃ i, (∀ j, j < i → a j = b j) ∧ a i < b i

/-- Independent finite counting definition (C2), not the desired formula.
Every smaller dominant weight lies inside this box. -/
def weightRank {n : ℕ} (s : GTTopRow n) : ℕ :=
  (Finset.univ.filter fun a : Fin (n + 2) → Fin (s.val 0 + 1) =>
    Antitone (fun i => (a i).val) ∧ (a (Fin.last (n + 1))).val = 0 ∧
      weightLt (fun i => (a i).val) s.val).card

/-- RHS of (C6): subtract one after adding the positive N-k. -/
def weightRankFormula {n : ℕ} (s : Fin (n + 2) → ℕ) : ℕ :=
  ∑ k : Fin (n + 1), Nat.choose (n + 1 - k.val + s k.castSucc - 1)
    (n + 1 - k.val)

/-- Zero-based grid coordinates; outside the grid the value is zero. -/
def gridEntry {n : ℕ} (a : Fin (n + 2) → Fin (n + 2) → ℕ)
    (l k : ℕ) : ℕ :=
  if h : l < n + 2 ∧ k < n + 2 then a ⟨l, h.1⟩ ⟨k, h.2⟩ else 0

/-- Fixed top row, zero off-triangle storage and betweenness, PDF p.6, (20)-(21). -/
def IsPattern {n : ℕ} (s : GTTopRow n)
    (a : Fin (n + 2) → Fin (n + 2) → ℕ) : Prop :=
  (∀ k, a (Fin.last (n + 1)) k = s.val k) ∧
  (∀ l k, l < k → a l k = 0) ∧
  ∀ l k : ℕ, l + 1 < n + 2 → k ≤ l →
    gridEntry a (l + 1) k ≥ gridEntry a l k ∧
      gridEntry a l k ≥ gridEntry a (l + 1) (k + 1)

/-- All integral GT-patterns of s, with finite storage bounded by s_1.
Betweenness implies these bounds; no lower-row determinant shifts are taken. -/
abbrev Pattern {n : ℕ} (s : GTTopRow n) :=
  {a : Fin (n + 2) → Fin (n + 2) → Fin (s.val 0 + 1) //
    IsPattern s (fun l k => (a l k).val)}

/-- Natural-coordinate view of a stored pattern. -/
def patternGrid {n : ℕ} {s : GTTopRow n} (m : Pattern s) :
    Fin (n + 2) → Fin (n + 2) → ℕ := fun l k => (m.val l k).val

/-- One-based row sums, with sigma_0=0, PDF p.7. -/
def rowSum {n : ℕ} {s : GTTopRow n} (m : Pattern s) (l : ℕ) : ℝ :=
  if l = 0 then 0 else
    ∑ k ∈ Finset.range l, (gridEntry (patternGrid m) (l - 1) k : ℝ)

/-- Exact J_z eigenvalues (24), with coordinate i corresponding to l=i+1. -/
def zWeight {n : ℕ} {s : GTTopRow n} (m : Pattern s) : Fin (n + 1) → ℝ :=
  fun i => rowSum m (i.val + 1) -
    (rowSum m (i.val + 2) + rowSum m i.val) / 2

/-- Highest z-weight, invariant under uniform determinant shifts. -/
def highestZ {n : ℕ} (s : GTTopRow n) : Fin (n + 1) → ℝ :=
  fun i => ((s.val i.castSucc : ℝ) - (s.val i.succ : ℝ)) / 2

/-- The diagonal J_z matrix, PDF pp.6-7, (23)-(24). -/
def zMatrix {n : ℕ} (s : GTTopRow n) (i : Fin (n + 1)) :
    Matrix (Pattern s) (Pattern s) ℝ := Matrix.diagonal (fun m => zWeight m i)

/-- Squared lowering amplitude (28), PDF p.8; differences are taken in ℝ.
Only valid single-entry moves evaluate this formula. -/
def loweringSquared {n : ℕ} {s : GTTopRow n} (m : Pattern s) (l k : ℕ) : ℝ :=
  let a := fun r j => (gridEntry (patternGrid m) r j : ℝ)
  let upper : ℝ := ∏ j ∈ Finset.range (l + 2),
    (a (l + 1) j - a l k + (k : ℝ) - (j : ℝ) + 1)
  let lower : ℝ := ∏ j ∈ Finset.range l,
    (a (l - 1) j - a l k + (k : ℝ) - (j : ℝ))
  let denominator : ℝ := ∏ j ∈ (Finset.range (l + 1)).erase k,
    (a l j - a l k + (k : ℝ) - (j : ℝ) + 1) *
      (a l j - a l k + (k : ℝ) - (j : ℝ))
  (-(upper * lower) / denominator : ℝ)

/-- Single-entry decrement checked in ℤ, avoiding truncated subtraction at zero. -/
def IsLowerMove {n : ℕ} {s : GTTopRow n} (out input : Pattern s) (l k : ℕ) : Prop :=
  ∀ r j : Fin (n + 2),
    (patternGrid out r j : ℤ) = (patternGrid input r j : ℤ) -
      (if r.val = l ∧ j.val = k then 1 else 0)

/-- Exact GT lowering matrices (28), zero for invalid moves, using the
nonnegative real square root that fixes the source's GT phases. -/
def lowerMatrix {n : ℕ} (s : GTTopRow n) (i : Fin (n + 1)) :
    Matrix (Pattern s) (Pattern s) ℝ :=
  fun out input => ∑ k ∈ Finset.range (i.val + 1),
    if IsLowerMove out input i.val k then Real.sqrt (loweringSquared input i.val k) else 0

/-- Raising is the real transpose of lowering, PDF p.9, (29). -/
def raiseMatrix {n : ℕ} (s : GTTopRow n) (i : Fin (n + 1)) :
    Matrix (Pattern s) (Pattern s) ℝ := (lowerMatrix s i).transpose

/-- Primitive generator on the tensor product, PDF p.3, (3b).
This is a Kronecker sum, not a tensor product of channel matrices. -/
def tensorGeneratorMatrix {A B : Type*} [DecidableEq A] [DecidableEq B]
    (x : Matrix A A ℝ) (y : Matrix B B ℝ) : Matrix (A × B) (A × B) ℝ :=
  fun p q => (if p.2 = q.2 then x p.1 q.1 else 0) +
    (if p.1 = q.1 then y p.2 q.2 else 0)

/-- Block sum over a finite list of irreps, retaining repeated labels as copies. -/
def coupledMatrix {n r : ℕ} (t : Fin r → GTTopRow n)
    (a : (s : GTTopRow n) → Matrix (Pattern s) (Pattern s) ℝ) :
    Matrix ((j : Fin r) × Pattern (t j)) ((j : Fin r) × Pattern (t j)) ℝ :=
  fun p q => if h : p.1 = q.1 then a (t p.1) p.2 (h.symm ▸ q.2) else 0

/-- Definition of a real CG change of orthonormal bases, PDF pp.2-3,
(3b),(5),(6a)-(6b). Complex-linear extension gives the same SU(N)/SL(N,C)
coefficients. No selection rule, multiplicity count, kernel dimension or
reconstruction conclusion is assumed as a field. -/
structure CGTable {n r : ℕ} (s sPrime : GTTopRow n) (t : Fin r → GTTopRow n) where
  coeff : Matrix ((j : Fin r) × Pattern (t j)) (Pattern s × Pattern sPrime) ℝ
  rows : coeff * coeff.transpose = 1
  columns : coeff.transpose * coeff = 1
  cartan : ∀ i, coeff * tensorGeneratorMatrix (zMatrix s i) (zMatrix sPrime i) =
    coupledMatrix t (fun u => zMatrix u i) * coeff
  lowering : ∀ i, coeff * tensorGeneratorMatrix (lowerMatrix s i) (lowerMatrix sPrime i) =
    coupledMatrix t (fun u => lowerMatrix u i) * coeff
  raising : ∀ i, coeff * tensorGeneratorMatrix (raiseMatrix s i) (raiseMatrix sPrime i) =
    coupledMatrix t (fun u => raiseMatrix u i) * coeff

/-- Outer multiplicity in a full decomposition, counting all repeated labels (2). -/
def outerMultiplicity {n r : ℕ} (t : Fin r → GTTopRow n) (u : GTTopRow n) : ℕ :=
  (Finset.univ.filter fun j => t j = u).card

/-- Product raising kernel restricted to the specified highest z-weight,
PDF p.10, (35)-(36); other irreps' highest states are excluded. -/
def highestKernel {n : ℕ} (s sPrime u : GTTopRow n) :
    Submodule ℝ ((Pattern s × Pattern sPrime) → ℝ) :=
  (⨅ i : Fin (n + 1), LinearMap.ker (Matrix.toLin'
    (tensorGeneratorMatrix (zMatrix s i) (zMatrix sPrime i) -
      Matrix.diagonal (fun _ => highestZ u i)))) ⊓
  (⨅ i : Fin (n + 1), LinearMap.ker (Matrix.toLin'
    (tensorGeneratorMatrix (raiseMatrix s i) (raiseMatrix sPrime i))))

/-- l-box count in tableau row k, (A1), using zero-based coordinates. -/
def lrIncrement {n : ℕ} {s : GTTopRow n} (m : Pattern s) (k l : ℕ) : ℕ :=
  gridEntry (patternGrid m) l k -
    (if k < l then gridEntry (patternGrid m) (l - 1) k else 0)

/-- Corrected B(k,l): sum over the summation index; k counts completed rows. -/
def lrB {n : ℕ} {s : GTTopRow n} (m : Pattern s) (sPrime : GTTopRow n)
    (k : ℕ) (l : Fin (n + 2)) : ℕ :=
  sPrime.val l + ∑ j ∈ Finset.range k, lrIncrement m j l.val

/-- VIII step 2: diagonals k ascending, entries l descending from N-1 to k. -/
def lrPositions (n : ℕ) : List (ℕ × ℕ) :=
  (List.range (n + 2)).flatMap fun k =>
    ((List.range (n + 2)).reverse.filter fun l => decide (k ≤ l)).map fun l => (k,l)

/-- The actual trial update, VIII step 3. -/
def lrUpdate {n : ℕ} {s : GTTopRow n} (m : Pattern s)
    (w : Fin (n + 2) → ℕ) (p : ℕ × ℕ) : Fin (n + 2) → ℕ :=
  fun l => w l + (if l.val = p.2 then lrIncrement m p.1 p.2 else 0)

/-- Every intermediate trial weight must stay dominant; no early normalization. -/
def lrAccepted {n : ℕ} {s : GTTopRow n} (m : Pattern s) (sPrime : GTTopRow n) : Prop :=
  ∀ w ∈ (lrPositions n).scanl (lrUpdate m) sPrime.val, Antitone w

/-- The chain in (31): B(k,l') on the left, B(k+1,l') on the right.
The left segment is empty at zero-based l=0. -/
def lrChainWeight {n : ℕ} {s : GTTopRow n} (m : Pattern s) (sPrime : GTTopRow n)
    (k l : ℕ) : Fin (n + 2) → ℕ :=
  fun j => if j.val < l then lrB m sPrime k j else lrB m sPrime (k + 1) j

/-- Final homogeneous trial row. -/
def lrFinal {n : ℕ} {s : GTTopRow n} (m : Pattern s) (sPrime : GTTopRow n) :
    Fin (n + 2) → ℕ := fun l => lrB m sPrime (l.val + 1) l

/-- Accepted-pattern count for each normalized output, aggregating determinant
shifts after processing all trial weights, PDF pp.9-10. -/
def lrMultiplicity {n : ℕ} (s sPrime u : GTTopRow n) : ℕ :=
  (Finset.univ.filter fun m : Pattern s => lrAccepted m sPrime ∧
    ∀ l, lrFinal m sPrime l - lrFinal m sPrime (Fin.last (n + 1)) = u.val l).card

/-- C.2 coordinate order: top to bottom, left to right. -/
def positionLt {n : ℕ} (p q : Fin (n + 2) × Fin (n + 2)) : Prop :=
  q.1 < p.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

/-- Strict pattern lexicographic order with immutable top row. -/
def patternLt {n : ℕ} {s : GTTopRow n} (a b : Pattern s) : Prop :=
  ∃ p : Fin (n + 2) × Fin (n + 2), p.2 ≤ p.1 ∧
    (∀ q : Fin (n + 2) × Fin (n + 2), q.2 ≤ q.1 → positionLt q p →
      patternGrid a q.1 q.2 = patternGrid b q.1 q.2) ∧
    patternGrid a p.1 p.2 < patternGrid b p.1 p.2

/-- Inclusive one-based mathematical Q in (C7), not the implementation's Q-1. -/
def patternRank {n : ℕ} {s : GTTopRow n} (m : Pattern s) : ℕ :=
  1 + (Finset.univ.filter fun p : Pattern s => patternLt p m).card

/-- Positions in row order, including the top row. -/
def patternPositions (n : ℕ) : List (Fin (n + 2) × Fin (n + 2)) :=
  (List.finRange (n + 2)).reverse.flatMap fun l =>
    (List.finRange (l.val + 1)).map fun k => (l, ⟨k.val, by omega⟩)

/-- Last lower-row entry strictly greater than its lower bound in the row above. -/
def predecessorPivot {n : ℕ} {s : GTTopRow n} (m : Pattern s) :
    Option (Fin (n + 2) × Fin (n + 2)) :=
  (patternPositions n).reverse.find? fun p => decide
    (p.1.val < n + 1 ∧ gridEntry (patternGrid m) (p.1.val + 1) (p.2.val + 1) <
      patternGrid m p.1 p.2)

/-- C9 resetting, recursively top to bottom; t is distance below the top.
Earlier entries stay fixed and later entries copy their new upper neighbors. -/
def predecessorReset {n : ℕ} {s : GTTopRow n} (m : Pattern s)
    (p : Fin (n + 2) × Fin (n + 2)) : ℕ → ℕ → ℕ
  | 0, k => gridEntry (patternGrid m) (n + 1) k
  | t + 1, k =>
    let l := n + 1 - (t + 1)
    if l < k then 0 else
    if p.1.val < l ∨ (l = p.1.val ∧ k < p.2.val) then
      gridEntry (patternGrid m) l k
    else if l = p.1.val ∧ k = p.2.val then gridEntry (patternGrid m) l k - 1
    else predecessorReset m p t k

/-- Partial predecessor. Validity of returned raw grids is a conclusion below. -/
def patternPredecessor {n : ℕ} {s : GTTopRow n} (m : Pattern s) :
    Option (Fin (n + 2) → Fin (n + 2) → ℕ) :=
  (predecessorPivot m).map fun p l k => predecessorReset m p (n + 1 - l.val) k.val

/-- Exactly t successful predecessor steps followed by None. -/
def HasPredecessorChain {n : ℕ} {s : GTTopRow n} : ℕ → Pattern s → Prop
  | 0, m => patternPredecessor m = none
  | t + 1, m => ∃ p : Pattern s,
      patternPredecessor m = some (patternGrid p) ∧ HasPredecessorChain t p

/-- Rows are interpreted in the Euclidean norm, never the function sup norm. -/
def euclideanRow {I : Type*} [Fintype I] {m : ℕ}
    (a : Matrix (Fin m) I ℝ) (i : Fin m) : EuclideanSpace ℝ I :=
  WithLp.toLp 2 (a i)

/-- Mathematical RREF, with unit pivots and no zero rows. The positive scaling
freedom in the printed (37) disappears after normalized Gram-Schmidt. -/
def IsRREF {m d : ℕ} (a : Matrix (Fin m) (Fin d) ℝ) : Prop :=
  ∃ pivot : Fin m → Fin d, StrictMono pivot ∧
    (∀ i, a i (pivot i) = 1) ∧
    (∀ i k, k < pivot i → a i k = 0) ∧
    ∀ i j, i ≠ j → a j (pivot i) = 0

/-- Normalized Gram-Schmidt, from the first RREF row to the last. -/
def canonicalRows {m d : ℕ} (a : Matrix (Fin m) (Fin d) ℝ) :
    Fin m → EuclideanSpace ℝ (Fin d) :=
  InnerProductSpace.gramSchmidtNormed ℝ (euclideanRow a)

/-- Output weight space indexed by z-weights, avoiding determinant shifts. -/
abbrev WeightPatterns {n : ℕ} (u : GTTopRow n) (w : Fin (n + 1) → ℝ) :=
  {m : Pattern u // zWeight m = w}

/-- All parent occurrences (M'',k,l), retaining duplicated parent equations. -/
abbrev ParentOccurrences {n : ℕ} (u : GTTopRow n) (w : Fin (n + 1) → ℝ) :=
  {p : WeightPatterns u w × Fin (n + 1) × Fin (n + 2) × Pattern u //
    p.2.2.1.val ≤ p.2.1.val ∧
      IsLowerMove p.1.val p.2.2.2 p.2.1.val p.2.2.1.val}

/-- Rectangular b of (39)-(40), with all target states as columns. -/
def reconstructionMatrix {n : ℕ} (u : GTTopRow n) (w : Fin (n + 1) → ℝ) :
    Matrix (ParentOccurrences u w) (WeightPatterns u w) ℝ :=
  fun p m => lowerMatrix u p.val.2.1 m.val p.val.2.2.2

/-- Known RHS of (40), product-lowering each correctly expanded parent. -/
def reconstructionRHS {n : ℕ} (s sPrime u : GTTopRow n) (w : Fin (n + 1) → ℝ)
    (parents : Matrix (ParentOccurrences u w) (Pattern s × Pattern sPrime) ℝ) :
    Matrix (ParentOccurrences u w) (Pattern s × Pattern sPrime) ℝ :=
  fun p q => ∑ b, tensorGeneratorMatrix (lowerMatrix s p.val.2.1)
    (lowerMatrix sPrime p.val.2.1) q b * parents p b

/-- C6 sanity: in SU(2) the formula is P((a,0))=a. -/
example (s : Fin 2 → ℕ) : weightRankFormula (n := 0) s = s 0 := by
  simp [weightRankFormula]

/-- A label is never lexicographically smaller than itself. -/
example {n : ℕ} (s : Fin (n + 2) → ℕ) : ¬ weightLt s s := by
  rintro ⟨i, _, h⟩
  exact (lt_irrefl _ h)

/-- The row-sum convention includes sigma_0=0. -/
example {n : ℕ} {s : GTTopRow n} (m : Pattern s) : rowSum m 0 = 0 := by
  simp [rowSum]

/-- The resetting operation preserves the top row. -/
example {n : ℕ} {s : GTTopRow n} (m : Pattern s)
    (p : Fin (n + 2) × Fin (n + 2)) (k : ℕ) :
    predecessorReset m p 0 k = gridEntry (patternGrid m) (n + 1) k := by
  rfl

/-- On one-dimensional factors the primitive generator is the sum, not the
product of the two scalar generator entries. -/
example (a b : ℝ) :
    tensorGeneratorMatrix (fun _ _ : Unit => a) (fun _ _ : Unit => b) ((), ()) ((), ()) = a + b := by
  simp [tensorGeneratorMatrix]

/-- The single unit-pivot row is in the source RREF convention. -/
example : IsRREF (fun _ _ : Fin 1 => (1 : ℝ)) := by
  refine ⟨id, strictMono_id, ?_, ?_, ?_⟩
  · intro i
    rfl
  · intro i k h
    have e : k = i := Subsingleton.elim _ _
    subst k
    exact False.elim ((lt_irrefl i) h)
  · intro i j h
    exact False.elim (h (Subsingleton.elim _ _))

end QAlgorithms.Papers.Independent.Renew46.P15


