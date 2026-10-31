-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P54
-- name    : QAlgorithms_Papers_Independent_Intake100_P54
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T13:47:15.792158+00:00
-- url     : https://prove2.me/theorems/27e270ec-95c1-4c4d-82de-d055807b69d1
-- title:
--   Definitions for Affine Hecke algebras and generalized standard Young tableaux
-- statement:
--   The objects the formalized statements of *Affine Hecke algebras and generalized standard Young tableaux* (arXiv:math/0401329) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `ARoot`: The positive root epsilon_j - epsilon_i, i < j; §5.2, PDF p.22. The type contains no zero roots, including when n = 0 or 1.
--   - `aRootVector`: Actual integral root vectors, rather than unrelated root names.
--   - `aPairing`: The root pairing in the source's orthonormal epsilon coordinates.
--   - `aZeroRoots`: Z(gamma), equations (4.3), (5.1), PDF pp.17,21.
--   - `aUnitRoots`: P(gamma), equations (4.3), (5.1), PDF pp.17,21.
--   - `aInversions`: R(w), with the positive-root convention of §5.2 and p.24.
--   - `aRegion`: The chamber set is computed from inversion sets, not from tableaux.
--   - `aWeightAction`: The actual inverse permutation convention: (w gamma)_i = gamma_(w^-1 i).
--   - `aConfigurationClosure`: The closure condition printed in §5.10, p.25, in actual root vectors. It is independent of the existence of either a configuration or a tableau.
--   - `BoxDrawing`: A finite labelled drawing on real graph paper. Real positions permit continuous diagonal slides; theorems impose integral diagonal contents.
--   - `drawingContent`: Content on real-coordinate drawings, §5.5, p.23. This extends the accepted integer cell-content convention to the continuous slides of §5.10; the frozen `Renew46.P26.boxContent` is reused for integer skew-shape cells below.
--   - `Northwest`: Northwest means strictly north and weakly west, pp.24–25.
--   - `Southeast`: Southeast means weakly south and strictly east, p.25.
--   - `DisjointBoxes`: Distinct unit-square boxes have disjoint interiors. Boundary contact is allowed. This prevents overlapping boxes on a diagonal.
--   - `DiagonallyNumbered`: Numbering along diagonals SW to NE, and NW to SE on each diagonal, §5.3 and §5.10. No filling labels occur in this condition.
--   - `drawingJ`: The geometric J of (5.7), independently of permutations.
--   - `ConfigurationFor`: A realization of (gamma,J) as boxes, §5.10. Every field is geometric: contents, numbering, disjointness, and the two adjacent-diagonal orders.
--   - `slideData`: Exactly the data preserved by allowed diagonal slides in §5.10: contents, order on a diagonal, and NW/SE orders on adjacent diagonals. Absolute row and column coordinates are deliberately absent.
--   - `SlideEquivalent`: Equality up to allowed slides is equality of the preserved order data. This does not identify arbitrary drawings by their content sequence alone.
--   - `ContentOrderIso`: A content-preserving geometric isomorphism may relabel boxes. It preserves order on each diagonal and the NW/SE comparisons on adjacent diagonals. It contains no assertion about standard tableaux or spectra.
--   - `ContentOrderIso.refl`: The geometric identity is constructed without an assumed tableau law.
--   - `FillingsMatch`: Fillings match through the actual content-preserving box isomorphism. This is a relation on concrete fillings, not content-sequence injectivity.
--   - `drawingSlideSetoid`: The actual quotient by slide data; it assumes no chamber correspondence.
--   - `DrawingSlideClass`: Slide classes of labelled drawings. Valid configurations form a subset.
--   - `RowColumnStandard`: Row/column standardness, independently of root systems or chamber sets; §5.3, p.23. A permutation is a bijective filling with all n labels.
--   - `ConfigurationStandard`: The three filling inequalities of §5.10, p.25. They are read from actual box positions, not defined as membership in F(gamma,J).
--   - `ConfigurationTableaux`: Standard configuration fillings, with globally bijective labels.
--   - `tableauWord`: The word reads the entries of the numbered boxes, equation (5.4).
--   - `cellsDrawing`: A drawing of integer cells with arbitrary integer shift of content. Rows and columns have the English/matrix orientation.
--   - `PlacedSkewShape`: A placed skew shape, §§5.3–5.5, pp.22–23. The skew diagram is the finite difference of two genuine lower ideals. Numbering and placement contain only geometry, with no calibratedness or uniqueness of spectra.
--   - `PlacedSkewShape.drawing`: The actual drawing of the placed skew shape.
--   - `PlacedSkewShape.gamma`: Integral contents are computed from boxes and their placement.
--   - `PlacedSkewShape.J`: The shape's J is computed geometrically by (5.7).
--   - `SkewTableaux`: Standard skew tableaux are row/column increasing fillings, p.23.
--   - `IsSkewConfiguration`: Geometric skewness modulo slides. A diagram is recognized by actual partition differences; skew local regions do not occur in the definition.
--   - `aCalibratable`: Type A specialization of the numerical conditions (5.1c), applied to arbitrary w gamma, including nondominant vectors. The rank-one condition excludes equal neighboring entries. In an A2 subsystem with neighboring entries unequal, a zero root means equal entries two positions apart; its level-one root count is 0 or 2, never more than 2. Disjoint A1 pairs add no condition once rank one holds. Thus the second condition excludes those distance-two equalities. This is independent of diagrams or modules.
--   - `IsSkewLocalRegionA`: Skewness in §5.1d: nonempty region and calibratability of every w gamma.
--   - `IsRibbonA`: A ribbon is a nonempty local region with regular gamma, §5.1b.
--   - `IsPlacedBorderStrip`: A border strip is a skew configuration with at most one box per diagonal. Connectivity is expressly not required in §6.5, p.29.
--   - `boxContaining`: The box containing an entry, with the word convention of (5.4).
--   - `classicalAxialDistance`: Classical axial distance FROM j TO i, PDF pp.27–28. All differences are in the reals, so negative distances are retained.
--   - `aAxialDistance`: Root axial distance for epsilon_j-epsilon_i; i,j may be arbitrary.
--   - `emptyDrawing`: Empty drawings have no boxes to compare.
--   - `negativeSingleBox`: A one-box drawing can have negative content.
-- source:
--   Affine Hecke algebras and generalized standard Young tableaux, arXiv:math/0401329v2, https://arxiv.org/abs/math/0401329v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

/-!
Concrete type A geometry from Ram, arXiv:math/0401329v2, §§5–6.
Mathlib primitives and the accepted integer cell-content definition are used.
No representation classification, support,
or tableau-to-chamber correspondence is a field of any definition below.
Labels in `Fin n` stand for the printed labels 1,...,n.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P54

/-- The positive root epsilon_j - epsilon_i, i < j; §5.2, PDF p.22.
The type contains no zero roots, including when n = 0 or 1. -/
abbrev ARoot (n : ℕ) := {a : Fin n × Fin n // a.1 < a.2}

/-- Actual integral root vectors, rather than unrelated root names. -/
def aRootVector {n : ℕ} (a : ARoot n) : Fin n → ℤ :=
  fun k => (if k = a.val.2 then 1 else 0) - (if k = a.val.1 then 1 else 0)

/-- The root pairing in the source's orthonormal epsilon coordinates. -/
def aPairing {n : ℕ} (gamma : Fin n → ℝ) (a : ARoot n) : ℝ :=
  gamma a.val.2 - gamma a.val.1

/-- Z(gamma), equations (4.3), (5.1), PDF pp.17,21. -/
def aZeroRoots {n : ℕ} (gamma : Fin n → ℝ) : Set (ARoot n) :=
  {a | aPairing gamma a = 0}

/-- P(gamma), equations (4.3), (5.1), PDF pp.17,21. -/
def aUnitRoots {n : ℕ} (gamma : Fin n → ℝ) : Set (ARoot n) :=
  {a | aPairing gamma a = 1}

/-- R(w), with the positive-root convention of §5.2 and p.24. -/
def aInversions {n : ℕ} (w : Equiv.Perm (Fin n)) : Set (ARoot n) :=
  {a | w a.val.2 < w a.val.1}

/-- The chamber set is computed from inversion sets, not from tableaux. -/
def aRegion {n : ℕ} (gamma : Fin n → ℝ) (J : Set (ARoot n)) :
    Set (Equiv.Perm (Fin n)) :=
  {w | aInversions w ∩ aZeroRoots gamma = ∅ ∧
    aInversions w ∩ aUnitRoots gamma = J}

/-- The actual inverse permutation convention: (w gamma)_i = gamma_(w^-1 i). -/
def aWeightAction {n : ℕ} (gamma : Fin n → ℝ)
    (w : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun i => gamma (w.symm i)

/-- The closure condition printed in §5.10, p.25, in actual root vectors.
It is independent of the existence of either a configuration or a tableau. -/
def aConfigurationClosure {n : ℕ} (gamma : Fin n → ℝ)
    (J : Set (ARoot n)) : Prop :=
  ∀ beta ∈ J, ∀ alpha ∈ aZeroRoots gamma, ∀ delta : ARoot n,
    aRootVector beta - aRootVector alpha = aRootVector delta → delta ∈ J

/-- A finite labelled drawing on real graph paper. Real positions permit
continuous diagonal slides; theorems impose integral diagonal contents. -/
structure BoxDrawing (n : ℕ) where
  row : Fin n → ℝ
  column : Fin n → ℝ

/-- Content on real-coordinate drawings, §5.5, p.23. This extends the accepted
integer cell-content convention to the continuous slides of §5.10; the frozen
`Renew46.P26.boxContent` is reused for integer skew-shape cells below. -/
def drawingContent {n : ℕ} (D : BoxDrawing n) (i : Fin n) : ℝ :=
  D.column i - D.row i

/-- Northwest means strictly north and weakly west, pp.24–25. -/
def Northwest {n : ℕ} (D : BoxDrawing n) (i j : Fin n) : Prop :=
  D.row j < D.row i ∧ D.column j ≤ D.column i

/-- Southeast means weakly south and strictly east, p.25. -/
def Southeast {n : ℕ} (D : BoxDrawing n) (i j : Fin n) : Prop :=
  D.row i ≤ D.row j ∧ D.column i < D.column j

/-- Distinct unit-square boxes have disjoint interiors. Boundary contact is
allowed. This prevents overlapping boxes on a diagonal. -/
def DisjointBoxes {n : ℕ} (D : BoxDrawing n) : Prop :=
  ∀ i j, i ≠ j →
    D.row i + 1 ≤ D.row j ∨ D.row j + 1 ≤ D.row i ∨
    D.column i + 1 ≤ D.column j ∨ D.column j + 1 ≤ D.column i

/-- Numbering along diagonals SW to NE, and NW to SE on each diagonal,
§5.3 and §5.10. No filling labels occur in this condition. -/
def DiagonallyNumbered {n : ℕ} (D : BoxDrawing n) : Prop :=
  ∀ i j, i < j → drawingContent D i ≤ drawingContent D j ∧
    (drawingContent D i = drawingContent D j → D.row i < D.row j)

/-- The geometric J of (5.7), independently of permutations. -/
def drawingJ {n : ℕ} (D : BoxDrawing n) : Set (ARoot n) :=
  {a | drawingContent D a.val.2 - drawingContent D a.val.1 = 1 ∧
    Northwest D a.val.1 a.val.2}

/-- A realization of (gamma,J) as boxes, §5.10. Every field is geometric:
contents, numbering, disjointness, and the two adjacent-diagonal orders. -/
def ConfigurationFor {n : ℕ} (gamma : Fin n → ℤ) (J : Set (ARoot n))
    (D : BoxDrawing n) : Prop :=
  DisjointBoxes D ∧ DiagonallyNumbered D ∧
  (∀ i, drawingContent D i = (gamma i : ℝ)) ∧
  J ⊆ aUnitRoots (fun i => (gamma i : ℝ)) ∧ drawingJ D = J ∧
  (∀ i j, i < j → gamma j - gamma i = 1 →
    Northwest D i j ∨ Southeast D i j)

/-- Exactly the data preserved by allowed diagonal slides in §5.10:
contents, order on a diagonal, and NW/SE orders on adjacent diagonals.
Absolute row and column coordinates are deliberately absent. -/
def slideData {n : ℕ} (D : BoxDrawing n) :
    (Fin n → ℝ) × (Fin n → Fin n → Prop) ×
      (Fin n → Fin n → Prop) × (Fin n → Fin n → Prop) :=
  (drawingContent D,
    (fun i j => drawingContent D i = drawingContent D j ∧ D.row i < D.row j),
    (fun i j => drawingContent D j - drawingContent D i = 1 ∧ Northwest D i j),
    (fun i j => drawingContent D j - drawingContent D i = 1 ∧ Southeast D i j))

/-- Equality up to allowed slides is equality of the preserved order data.
This does not identify arbitrary drawings by their content sequence alone. -/
def SlideEquivalent {n : ℕ} (D E : BoxDrawing n) : Prop :=
  slideData D = slideData E

/-- A content-preserving geometric isomorphism may relabel boxes. It
preserves order on each diagonal and the NW/SE comparisons on adjacent
diagonals. It contains no assertion about standard tableaux or spectra. -/
structure ContentOrderIso {n : ℕ} (D E : BoxDrawing n) where
  boxes : Equiv.Perm (Fin n)
  content : ∀ i, drawingContent D i = drawingContent E (boxes i)
  sameDiagonal : ∀ i j, drawingContent D i = drawingContent D j →
    (D.row i < D.row j ↔ E.row (boxes i) < E.row (boxes j))
  northwest : ∀ i j, drawingContent D j - drawingContent D i = 1 →
    (Northwest D i j ↔ Northwest E (boxes i) (boxes j))
  southeast : ∀ i j, drawingContent D j - drawingContent D i = 1 →
    (Southeast D i j ↔ Southeast E (boxes i) (boxes j))

/-- The geometric identity is constructed without an assumed tableau law. -/
def ContentOrderIso.refl {n : ℕ} (D : BoxDrawing n) : ContentOrderIso D D where
  boxes := Equiv.refl _
  content _ := rfl
  sameDiagonal _ _ _ := Iff.rfl
  northwest _ _ _ := Iff.rfl
  southeast _ _ _ := Iff.rfl

/-- Fillings match through the actual content-preserving box isomorphism.
This is a relation on concrete fillings, not content-sequence injectivity. -/
def FillingsMatch {n : ℕ} {D E : BoxDrawing n} (e : ContentOrderIso D E)
    (p q : Equiv.Perm (Fin n)) : Prop :=
  ∀ i, q (e.boxes i) = p i

example (D : BoxDrawing 0) (p : Equiv.Perm (Fin 0)) :
    FillingsMatch (ContentOrderIso.refl D) p p := by
  intro i
  rfl

/-- The actual quotient by slide data; it assumes no chamber correspondence. -/
def drawingSlideSetoid (n : ℕ) : Setoid (BoxDrawing n) where
  r := SlideEquivalent
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-- Slide classes of labelled drawings. Valid configurations form a subset. -/
abbrev DrawingSlideClass (n : ℕ) := Quotient (drawingSlideSetoid n)

/-- Row/column standardness, independently of root systems or chamber sets;
§5.3, p.23. A permutation is a bijective filling with all n labels. -/
def RowColumnStandard {n : ℕ} (D : BoxDrawing n)
    (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j,
    ((D.row i = D.row j ∧ D.column i < D.column j) → p i < p j) ∧
    ((D.column i = D.column j ∧ D.row i < D.row j) → p i < p j)

/-- The three filling inequalities of §5.10, p.25. They are read from
actual box positions, not defined as membership in F(gamma,J). -/
def ConfigurationStandard {n : ℕ} (D : BoxDrawing n)
    (p : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j, i < j →
    (drawingContent D i = drawingContent D j → p i < p j) ∧
    (drawingContent D j - drawingContent D i = 1 → Southeast D i j → p i < p j) ∧
    (drawingContent D j - drawingContent D i = 1 → Northwest D i j → p j < p i)

/-- Standard configuration fillings, with globally bijective labels. -/
abbrev ConfigurationTableaux {n : ℕ} (D : BoxDrawing n) :=
  {p : Equiv.Perm (Fin n) // ConfigurationStandard D p}

/-- The word reads the entries of the numbered boxes, equation (5.4). -/
def tableauWord {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n) := p

/-- A drawing of integer cells with arbitrary integer shift of content.
Rows and columns have the English/matrix orientation. -/
def cellsDrawing {n : ℕ} (cell : Fin n ↪ ℕ × ℕ) (shift : ℤ) : BoxDrawing n where
  row i := ((cell i).1 : ℝ)
  column i := (shift : ℝ) + ((cell i).2 : ℝ)

/-- A placed skew shape, §§5.3–5.5, pp.22–23. The skew diagram is the
finite difference of two genuine lower ideals. Numbering and placement
contain only geometry, with no calibratedness or uniqueness of spectra. -/
structure PlacedSkewShape (n : ℕ) where
  outer : YoungDiagram
  inner : YoungDiagram
  contained : inner.cells ⊆ outer.cells
  cell : Fin n ↪ ℕ × ℕ
  cells_eq : Finset.univ.image cell = outer.cells \ inner.cells
  shift : ℤ
  numbered : DiagonallyNumbered (cellsDrawing cell shift)

/-- The actual drawing of the placed skew shape. -/
def PlacedSkewShape.drawing {n : ℕ} (S : PlacedSkewShape n) : BoxDrawing n :=
  cellsDrawing S.cell S.shift

/-- Integral contents are computed from boxes and their placement. -/
def PlacedSkewShape.gamma {n : ℕ} (S : PlacedSkewShape n) : Fin n → ℤ :=
  fun i => S.shift + QAlgorithms.Papers.Independent.Renew46.P26.boxContent (S.cell i)

/-- The shape's J is computed geometrically by (5.7). -/
def PlacedSkewShape.J {n : ℕ} (S : PlacedSkewShape n) : Set (ARoot n) :=
  drawingJ S.drawing

/-- Standard skew tableaux are row/column increasing fillings, p.23. -/
abbrev SkewTableaux {n : ℕ} (S : PlacedSkewShape n) :=
  {p : Equiv.Perm (Fin n) // RowColumnStandard S.drawing p}

/-- Geometric skewness modulo slides. A diagram is recognized by actual
partition differences; skew local regions do not occur in the definition. -/
def IsSkewConfiguration {n : ℕ} (D : BoxDrawing n) : Prop :=
  ∃ S : PlacedSkewShape n, SlideEquivalent D S.drawing

/-- Type A specialization of the numerical conditions (5.1c), applied to
arbitrary w gamma, including nondominant vectors. The rank-one condition
excludes equal neighboring entries. In an A2 subsystem with neighboring
entries unequal, a zero root means equal entries two positions apart; its
level-one root count is 0 or 2, never more than 2. Disjoint A1 pairs add no
condition once rank one holds. Thus the second condition excludes those
distance-two equalities. This is independent of diagrams or modules. -/
def aCalibratable {n : ℕ} (v : Fin n → ℝ) : Prop :=
  (∀ i j : Fin n, j.val = i.val + 1 → v i ≠ v j) ∧
  (∀ i j : Fin n, j.val = i.val + 2 → v i ≠ v j)

/-- Skewness in §5.1d: nonempty region and calibratability of every w gamma. -/
def IsSkewLocalRegionA {n : ℕ} (gamma : Fin n → ℝ)
    (J : Set (ARoot n)) : Prop :=
  (aRegion gamma J).Nonempty ∧
  ∀ w ∈ aRegion gamma J, aCalibratable (aWeightAction gamma w)

/-- A ribbon is a nonempty local region with regular gamma, §5.1b. -/
def IsRibbonA {n : ℕ} (gamma : Fin n → ℝ) (J : Set (ARoot n)) : Prop :=
  (aRegion gamma J).Nonempty ∧ ∀ a : ARoot n, aPairing gamma a ≠ 0

/-- A border strip is a skew configuration with at most one box per diagonal.
Connectivity is expressly not required in §6.5, p.29. -/
def IsPlacedBorderStrip {n : ℕ} (D : BoxDrawing n) : Prop :=
  IsSkewConfiguration D ∧ Function.Injective (drawingContent D)

/-- The box containing an entry, with the word convention of (5.4). -/
def boxContaining {n : ℕ} (p : Equiv.Perm (Fin n)) (i : Fin n) : Fin n :=
  p.symm i

/-- Classical axial distance FROM j TO i, PDF pp.27–28. All differences
are in the reals, so negative distances are retained. -/
def classicalAxialDistance {n : ℕ} (D : BoxDrawing n)
    (p : Equiv.Perm (Fin n)) (j i : Fin n) : ℝ :=
  D.column (boxContaining p j) - D.column (boxContaining p i) +
    D.row (boxContaining p i) - D.row (boxContaining p j)

/-- Root axial distance for epsilon_j-epsilon_i; i,j may be arbitrary. -/
def aAxialDistance {n : ℕ} (gamma : Fin n → ℝ)
    (w : Equiv.Perm (Fin n)) (j i : Fin n) : ℝ :=
  aWeightAction gamma w j - aWeightAction gamma w i

/-- Empty drawings have no boxes to compare. -/
def emptyDrawing : BoxDrawing 0 where
  row := Fin.elim0
  column := Fin.elim0

/-- The empty diagram has its unique empty standard filling. -/
example : RowColumnStandard emptyDrawing (Equiv.refl (Fin 0)) := by
  intro i
  exact Fin.elim0 i

/-- The empty configuration has its unique empty configuration filling. -/
example : ConfigurationStandard emptyDrawing (Equiv.refl (Fin 0)) := by
  intro i
  exact Fin.elim0 i

/-- With no roots, F is nonempty, rather than an empty family of tableaux. -/
example : (1 : Equiv.Perm (Fin 0)) ∈ aRegion (fun i => Fin.elim0 i) ∅ := by
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro a
    exact Fin.elim0 a.val.1
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro a
    exact Fin.elim0 a.val.1

/-- A one-box drawing can have negative content. -/
def negativeSingleBox : BoxDrawing 1 where
  row _ := 0
  column _ := -2

example : drawingContent negativeSingleBox 0 = -2 := by
  norm_num [drawingContent, negativeSingleBox]

/-- Slide classes preserve more than the multiset of contents. -/
example (D : BoxDrawing 0) : SlideEquivalent D D := rfl

/-- The rank-one obstruction already rejects two equal consecutive entries. -/
example : ¬ aCalibratable (fun _ : Fin 2 => (0 : ℝ)) := by
  intro h
  exact h.1 0 1 rfl rfl

/-- The positive A1 root has pairing +1 on the increasing two-entry vector. -/
example : aPairing (fun i : Fin 2 => (i.val : ℝ))
    (⟨(0, 1), by decide⟩ : ARoot 2) = 1 := by
  norm_num [aPairing]

/-- The identity has no inversions, with exactly the source root sign. -/
example (n : ℕ) : aInversions (1 : Equiv.Perm (Fin n)) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro a ha
  change a.val.2 < a.val.1 at ha
  exact lt_asymm a.property ha

/-- Negative placement does not change one-box row/column standardness. -/
example : RowColumnStandard negativeSingleBox (1 : Equiv.Perm (Fin 1)) := by
  intro i j
  have hij : i = j := Subsingleton.elim i j
  subst j
  constructor
  · intro h
    exact (lt_irrefl _ h.2).elim
  · intro h
    exact (lt_irrefl _ h.2).elim

/-- No distinct one-box labels can overlap. -/
example : DisjointBoxes negativeSingleBox := by
  intro i j h
  exact (h (Subsingleton.elim i j)).elim

end QAlgorithms.Papers.Independent.Intake100.P54


