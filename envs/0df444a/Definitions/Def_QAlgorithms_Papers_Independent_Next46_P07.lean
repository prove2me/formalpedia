-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Next46_P07
-- name    : QAlgorithms_Papers_Independent_Next46_P07
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-20T12:53:07.529723+00:00
-- url     : https://prove2.me/theorems/c0205db3-aec6-4e27-8438-9852d758080e
-- title:
--   Definitions for Contingency tables and the generalized Littlewood-Richardson coefficients
-- statement:
--   The objects the formalized statements of *Contingency tables and the generalized Littlewood-Richardson coefficients* (arXiv:2012.06928) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `MatrixModel`: Finite matrix coordinates for the concrete actions constructed below. Only computed actions, never arbitrary instances of this record, occur in the paper's statements. Source: arXiv:2012.06928v1, PDF pp.1-3.
--   - `coordinateModel`: Coordinates of a specified action on an actual finite-dimensional space. The choice of basis changes no Hom or invariant dimension (PDF p.3).
--   - `zeroModel`: The zero space is the explicit totalization at an inadmissible label. Every theorem uses admissible labels; no result is asserted on this branch.
--   - `trivialModel`: The one-dimensional trivial action, including the empty tensor (PDF pp.3-4).
--   - `tensorModel`: Diagonal tensor action with the actual product basis, including zero factors. Source: PDF p.3, (2.4).
--   - `homSpace`: Actual equivariant linear maps, with the first model as domain. Source: PDF p.3, definition of [V:W].
--   - `homDimension`: The bracket is complex Hom dimension, including reducible domains (PDF p.3).
--   - `invariantDimension`: Invariant dimension, realized as Hom from the trivial complex line. Source: PDF pp.3-4 and 14.
--   - `diagram`: A list of nonnegative row lengths defines a partition after sorting; zeros are omitted by YoungDiagram.ofRowLens (PDF p.2).
--   - `rowPartition`: The one-row partition; degree zero is the empty partition (PDF pp.2,9).
--   - `columnPartition`: The one-column partition of height a, the label for an exterior power (PDF p.11, Example 8).
--   - `polynomialModel`: Polynomial GL_n module from the accepted concrete Young-symmetrizer image. The invalid-height branch is explicitly the zero space (PDF pp.2-3).
--   - `RationalLabel`: Positive and negative partitions of a dominant rational GL_n weight. Admissibility is always imposed separately as their total length at most n (PDF pp.2-3, (2.1)).
--   - `weightEntry`: The padded integer tuple in (2.1), read in the standard Borel convention. This formula is used only when the positive and negative supports do not overlap.
--   - `shiftedDiagram`: Shift the dominant tuple by its largest negative part to get a polynomial partition. Sorting is inert for admissible labels (PDF pp.1-3, determinant twist).
--   - `rationalModel`: The concrete rational irreducible: its shifted polynomial Schur module, tensored with det to the negative of the largest negative part. This is the usual determinant construction described on PDF pp.1-3, not a free multiplicity.
--   - `RationalLabelFits`: Rank admissibility for the pair notation in (2.1) (PDF p.2). The accepted predicates named Admissible concern channel models, not weights.
--   - `rationalLRC`: Generalized LRC is the actual Hom dimension in (2.4) (PDF p.3).
--   - `polynomialLRC`: Polynomial generalized LRC, evaluated at a fixed sufficiently large positive rank for all its labels. Polynomial multiplicity stability is recalled on PDF p.3. No support condition or conclusion of the paper is built into this definition.
--   - `lrWeight`: Definition 1, the product of all row and column coefficients (PDF p.7).
--   - `IsLRTable`: Definition 2: nonzero weight, without a hollow requirement (PDF p.7).
--   - `partitionBox`: Every partition inside a B by B square, enumerated once as a Finset. The degree constraints from margins bound every contributing diagram by such a square; no infinite-sum default is used (PDF pp.7-9).
--   - `PartitionTable`: Finite square arrays of the actual bounded diagrams, with no repeated codes.
--   - `hollowLRSum`: The complete finite weighted sum over hollow LR-contingency tables. The bound is the sum of all positive and negative margin sizes (PDF pp.7-9).
--   - `contingencyCount`: A bounded enumeration of nonnegative matrices with prescribed margins. Every entry is bounded by the sum of both margins. Unequal totals give no tables. Source: PDF pp.7,9-10.
--   - `derangements`: The number of permutations with no fixed point, including !0 = 1 (PDF p.10).
--   - `classicalAlternatingMatrix`: Bilinear alternating form on C^(2n), with e_i paired with e_(n+i). This is transpose, not conjugate transpose (PDF pp.12-14). The accepted real one-mode symplecticForm has a different domain and sign.
--   - `Orthogonal`: Full complex O_n: all invertible matrices preserving the standard symmetric bilinear form, with no determinant-one condition (PDF pp.12-13).
--   - `ComplexSymplecticGroup`: Complex Sp_(2n), preserving the bilinear alternating form (PDF pp.12-14). Accepted declarations named Symplectic are real-form or real-matrix predicates; this object is the full complex group of invertible matrices.
--   - `tensorSlotContraction`: A two-slot contraction functional on tensors, distinct from the accepted Brauer endomorphism and Gaussian channel contractions. Redundant full words x avoid any truncated arity at degrees zero and one. The form matrix is used on tensor indices; for our standard forms its inverse is itself up to a harmless sign. Source: PDF p.13, tensor/harmonic partition labels.
--   - `traceFree`: Completely trace-free tensors: every contraction of two distinct slots vanishes. In degrees zero and one there are no such constraints (PDF p.13).
--   - `harmonicModel`: Trace-free Schur tensors, with the restricted diagonal matrix action. For a group preserving form, the Young image and every trace kernel are stable, so projection merely expresses a map into the subtype. These are the classical harmonic tensor models for the partition labels on PDF pp.13-14.
--   - `orthogonalModel`: The full O_n harmonic tensor representation E_n^lambda, for lambda.colLen 0 + lambda.colLen 1 ≤ n (PDF p.13).
--   - `symplecticModel`: The irreducible Sp_(2n) harmonic tensor representation V_(2n)^lambda, for lambda.colLen 0 ≤ n (PDF pp.13-14).
--   - `symmetricLRWeight`: Definition 10: the product over rows once, not rows times columns (PDF p.14).
--   - `hollowSymmetricLRSum`: Definition 11 and hollowness, counting each symmetric matrix once. The square bound is the sum of margin sizes (PDF p.14).
--   - `pairingCount`: Fixed-point-free involution count: the even product is (r-1)!! and equals one at r=0; the odd branch is zero (PDF p.14, Example 13).
-- source:
--   Contingency tables and the generalized Littlewood-Richardson coefficients, arXiv:2012.06928v1, https://arxiv.org/abs/2012.06928v1

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurModules

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix

namespace QAlgorithms.Papers.Independent.Next46.P07

attribute [local instance] Classical.propDecidable

/-- Finite matrix coordinates for the concrete actions constructed below.
Only computed actions, never arbitrary instances of this record, occur in the
paper's statements. Source: arXiv:2012.06928v1, PDF pp.1-3. -/
structure MatrixModel (G : Type*) where
  dimension : ℕ
  action : G → Matrix (Fin dimension) (Fin dimension) ℂ

/-- Coordinates of a specified action on an actual finite-dimensional space.
The choice of basis changes no Hom or invariant dimension (PDF p.3). -/
def coordinateModel {G V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (action : G → V →ₗ[ℂ] V) : MatrixModel G where
  dimension := Module.finrank ℂ V
  action g := LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (action g)

/-- The zero space is the explicit totalization at an inadmissible label.
Every theorem uses admissible labels; no result is asserted on this branch. -/
def zeroModel (G : Type*) : MatrixModel G where
  dimension := 0
  action _ := 0

/-- The one-dimensional trivial action, including the empty tensor (PDF pp.3-4). -/
def trivialModel (G : Type*) : MatrixModel G where
  dimension := 1
  action _ := 1

/-- Diagonal tensor action with the actual product basis, including zero factors.
Source: PDF p.3, (2.4). -/
def tensorModel {G : Type*} {r : ℕ} (M : Fin r → MatrixModel G) : MatrixModel G where
  dimension := Fintype.card (∀ i : Fin r, Fin (M i).dimension)
  action g := fun a b =>
    ∏ i : Fin r, (M i).action g
      ((Fintype.equivFin (∀ i : Fin r, Fin (M i).dimension)).symm a i)
      ((Fintype.equivFin (∀ i : Fin r, Fin (M i).dimension)).symm b i)

/-- Actual equivariant linear maps, with the first model as domain.
Source: PDF p.3, definition of [V:W]. -/
def homSpace {G : Type*} (V W : MatrixModel G) :
    Submodule ℂ (Matrix (Fin W.dimension) (Fin V.dimension) ℂ) where
  carrier := {A | ∀ g, W.action g * A = A * V.action g}
  zero_mem' := by intro g; simp
  add_mem' := by
    intro A B hA hB g
    simp only [Matrix.mul_add, Matrix.add_mul, hA g, hB g]
  smul_mem' := by
    intro c A hA g
    simp only [Matrix.mul_smul, Matrix.smul_mul, hA g]

/-- The bracket is complex Hom dimension, including reducible domains (PDF p.3). -/
def homDimension {G : Type*} (V W : MatrixModel G) : ℕ :=
  Module.finrank ℂ (homSpace V W)

/-- Invariant dimension, realized as Hom from the trivial complex line.
Source: PDF pp.3-4 and 14. -/
def invariantDimension {G : Type*} (V : MatrixModel G) : ℕ :=
  homDimension (trivialModel G) V

/-- A list of nonnegative row lengths defines a partition after sorting;
zeros are omitted by YoungDiagram.ofRowLens (PDF p.2). -/
def diagram (rows : List ℕ) : YoungDiagram :=
  YoungDiagram.ofRowLens (rows.mergeSort (· ≥ ·)) (List.sortedGE_mergeSort (l := rows))

/-- The one-row partition; degree zero is the empty partition (PDF pp.2,9). -/
def rowPartition (a : ℕ) : YoungDiagram := diagram [a]

/-- The one-column partition of height a, the label for an exterior power
(PDF p.11, Example 8). -/
def columnPartition (a : ℕ) : YoungDiagram := (rowPartition a).transpose

/-- Polynomial GL_n module from the accepted concrete Young-symmetrizer image.
The invalid-height branch is explicitly the zero space (PDF pp.2-3). -/
def polynomialModel (n : ℕ) (lambda : YoungDiagram) :
    MatrixModel (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  if h : lambda.colLen 0 ≤ n then
    coordinateModel fun g : Matrix.GeneralLinearGroup (Fin n) ℂ =>
      QAlgorithms.Schur.polynomialRepresentation
        (⟨lambda, rfl, h⟩ : QAlgorithms.Schur.Partition n lambda.card)
        (g : Matrix (Fin n) (Fin n) ℂ)
  else zeroModel _

/-- Positive and negative partitions of a dominant rational GL_n weight.
Admissibility is always imposed separately as their total length at most n
(PDF pp.2-3, (2.1)). -/
abbrev RationalLabel := YoungDiagram × YoungDiagram

/-- The padded integer tuple in (2.1), read in the standard Borel convention.
This formula is used only when the positive and negative supports do not overlap. -/
def weightEntry (n : ℕ) (lambda : RationalLabel) (i : Fin n) : ℤ :=
  (lambda.1.rowLen i.val : ℤ) - (lambda.2.rowLen (n - 1 - i.val) : ℤ)

/-- Shift the dominant tuple by its largest negative part to get a polynomial
partition. Sorting is inert for admissible labels (PDF pp.1-3, determinant twist). -/
def shiftedDiagram (n : ℕ) (lambda : RationalLabel) : YoungDiagram :=
  diagram (List.ofFn fun i : Fin n =>
    (weightEntry n lambda i + (lambda.2.rowLen 0 : ℤ)).toNat)

/-- The concrete rational irreducible: its shifted polynomial Schur module,
tensored with det to the negative of the largest negative part. This is the
usual determinant construction described on PDF pp.1-3, not a free multiplicity. -/
def rationalModel (n : ℕ) (lambda : RationalLabel) :
    MatrixModel (Matrix.GeneralLinearGroup (Fin n) ℂ) where
  dimension := (polynomialModel n (shiftedDiagram n lambda)).dimension
  action g :=
    (Matrix.det (g : Matrix (Fin n) (Fin n) ℂ) ^ (-(lambda.2.rowLen 0 : ℤ))) •
      (polynomialModel n (shiftedDiagram n lambda)).action g

/-- Rank admissibility for the pair notation in (2.1) (PDF p.2).
The accepted predicates named Admissible concern channel models, not weights. -/
def RationalLabelFits (n : ℕ) (lambda : RationalLabel) : Prop :=
  lambda.1.colLen 0 + lambda.2.colLen 0 ≤ n

/-- Generalized LRC is the actual Hom dimension in (2.4) (PDF p.3). -/
def rationalLRC (n : ℕ) {r : ℕ} (lambda : RationalLabel)
    (mu : Fin r → RationalLabel) : ℕ :=
  homDimension (rationalModel n lambda) (tensorModel fun i => rationalModel n (mu i))

/-- Polynomial generalized LRC, evaluated at a fixed sufficiently large positive
rank for all its labels. Polynomial multiplicity stability is recalled on PDF p.3.
No support condition or conclusion of the paper is built into this definition. -/
def polynomialLRC {r : ℕ} (lambda : YoungDiagram) (mu : Fin r → YoungDiagram) : ℕ :=
  let n := 1 + lambda.colLen 0 + ∑ i, (mu i).colLen 0
  homDimension (polynomialModel n lambda) (tensorModel fun i => polynomialModel n (mu i))

/-- Definition 1, the product of all row and column coefficients (PDF p.7). -/
def lrWeight {r : ℕ} (mu : Fin r → RationalLabel)
    (table : Fin r → Fin r → YoungDiagram) : ℕ :=
  ∏ i, polynomialLRC (mu i).1 (table i) *
    polynomialLRC (mu i).2 (fun j => table j i)

/-- Definition 2: nonzero weight, without a hollow requirement (PDF p.7). -/
def IsLRTable {r : ℕ} (mu : Fin r → RationalLabel)
    (table : Fin r → Fin r → YoungDiagram) : Prop := lrWeight mu table ≠ 0

/-- Every partition inside a B by B square, enumerated once as a Finset.
The degree constraints from margins bound every contributing diagram by such a
square; no infinite-sum default is used (PDF pp.7-9). -/
def partitionBox (B : ℕ) : Finset YoungDiagram :=
  Finset.univ.image fun rows : Fin B → Fin (B + 1) =>
    diagram (List.ofFn fun i => (rows i).val)

/-- Finite square arrays of the actual bounded diagrams, with no repeated codes. -/
abbrev PartitionTable (r B : ℕ) :=
  Fin r → Fin r → {lambda : YoungDiagram // lambda ∈ partitionBox B}

/-- The complete finite weighted sum over hollow LR-contingency tables.
The bound is the sum of all positive and negative margin sizes (PDF pp.7-9). -/
def hollowLRSum {r : ℕ} (mu : Fin r → RationalLabel) : ℕ :=
  let B := ∑ i, ((mu i).1.card + (mu i).2.card)
  ∑ table : PartitionTable r B,
    if (∀ i, (table i i).val = ⊥) ∧
        IsLRTable mu (fun i j => (table i j).val) then
      lrWeight mu (fun i j => (table i j).val) else 0

/-- A bounded enumeration of nonnegative matrices with prescribed margins.
Every entry is bounded by the sum of both margins. Unequal totals give no tables.
Source: PDF pp.7,9-10. -/
def contingencyCount {r s : ℕ} (a : Fin r → ℕ) (b : Fin s → ℕ)
    (extra : (Fin r → Fin s → ℕ) → Prop) : ℕ :=
  let B := (∑ i, a i) + ∑ j, b j
  (Finset.univ.filter fun T : Fin r → Fin s → Fin (B + 1) =>
    (∀ i, ∑ j, (T i j).val = a i) ∧
    (∀ j, ∑ i, (T i j).val = b j) ∧ extra (fun i j => (T i j).val)).card

/-- The number of permutations with no fixed point, including !0 = 1 (PDF p.10). -/
def derangements (r : ℕ) : ℕ :=
  (Finset.univ.filter fun p : Equiv.Perm (Fin r) => ∀ i, p i ≠ i).card

/-- Bilinear alternating form on C^(2n), with e_i paired with e_(n+i).
This is transpose, not conjugate transpose (PDF pp.12-14).
The accepted real one-mode symplecticForm has a different domain and sign. -/
def classicalAlternatingMatrix (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ :=
  fun i j => if i.val < n ∧ j.val = n + i.val then 1
    else if j.val < n ∧ i.val = n + j.val then -1 else 0

/-- Full complex O_n: all invertible matrices preserving the standard symmetric
bilinear form, with no determinant-one condition (PDF pp.12-13). -/
abbrev Orthogonal (n : ℕ) :=
  {g : Matrix.GeneralLinearGroup (Fin n) ℂ //
    (g : Matrix (Fin n) (Fin n) ℂ).transpose * (g : Matrix (Fin n) (Fin n) ℂ) = 1}

/-- Complex Sp_(2n), preserving the bilinear alternating form (PDF pp.12-14).
Accepted declarations named Symplectic are real-form or real-matrix predicates;
this object is the full complex group of invertible matrices. -/
abbrev ComplexSymplecticGroup (n : ℕ) :=
  {g : Matrix.GeneralLinearGroup (Fin (2 * n)) ℂ //
    (g : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ).transpose * classicalAlternatingMatrix n *
      (g : Matrix (Fin (2 * n)) (Fin (2 * n)) ℂ) = classicalAlternatingMatrix n}

/-- A two-slot contraction functional on tensors, distinct from the accepted
Brauer endomorphism and Gaussian channel contractions. Redundant full words x avoid
any truncated arity at degrees zero and one. The form matrix is used on tensor
indices; for our standard forms its inverse is itself up to a harmless sign.
Source: PDF p.13, tensor/harmonic partition labels. -/
def tensorSlotContraction {d m : ℕ} (form : Matrix (Fin d) (Fin d) ℂ)
    (p q : Fin m) (x : Fin m → Fin d) :
    EuclideanSpace ℂ (Fin m → Fin d) →ₗ[ℂ] ℂ where
  toFun v := ∑ a : Fin d, ∑ b : Fin d,
    form a b * v (Function.update (Function.update x p a) q b)
  map_add' v w := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp [Finset.mul_sum, mul_left_comm, mul_assoc]

/-- Completely trace-free tensors: every contraction of two distinct slots
vanishes. In degrees zero and one there are no such constraints (PDF p.13). -/
def traceFree {d m : ℕ} (form : Matrix (Fin d) (Fin d) ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin m → Fin d)) :=
  ⨅ p : Fin m, ⨅ q : Fin m, ⨅ (_ : p ≠ q),
    ⨅ x : Fin m → Fin d, LinearMap.ker (tensorSlotContraction form p q x)

/-- Trace-free Schur tensors, with the restricted diagonal matrix action.
For a group preserving form, the Young image and every trace kernel are stable,
so projection merely expresses a map into the subtype. These are the classical
harmonic tensor models for the partition labels on PDF pp.13-14. -/
def harmonicModel {G : Type*} (d : ℕ) (lambda : YoungDiagram)
    (form : Matrix (Fin d) (Fin d) ℂ)
    (matrix : G → Matrix.GeneralLinearGroup (Fin d) ℂ) : MatrixModel G :=
  if h : lambda.colLen 0 ≤ d then
    let shape : QAlgorithms.Schur.Partition d lambda.card := ⟨lambda, rfl, h⟩
    let H := QAlgorithms.Schur.schurModule shape ⊓ traceFree (m := lambda.card) form
    coordinateModel fun g : G =>
      H.orthogonalProjectionOnto.toLinearMap.comp
        ((Matrix.toEuclideanLin (QAlgorithms.piKron lambda.card
          (matrix g : Matrix (Fin d) (Fin d) ℂ))).comp H.subtype)
  else zeroModel _

/-- The full O_n harmonic tensor representation E_n^lambda, for
lambda.colLen 0 + lambda.colLen 1 ≤ n (PDF p.13). -/
def orthogonalModel (n : ℕ) (lambda : YoungDiagram) : MatrixModel (Orthogonal n) :=
  harmonicModel n lambda 1 (fun g : Orthogonal n => g.val)

/-- The irreducible Sp_(2n) harmonic tensor representation V_(2n)^lambda,
for lambda.colLen 0 ≤ n (PDF pp.13-14). -/
def symplecticModel (n : ℕ) (lambda : YoungDiagram) : MatrixModel (ComplexSymplecticGroup n) :=
  harmonicModel (2 * n) lambda (classicalAlternatingMatrix n) (fun g : ComplexSymplecticGroup n => g.val)

/-- Definition 10: the product over rows once, not rows times columns (PDF p.14). -/
def symmetricLRWeight {r : ℕ} (mu : Fin r → YoungDiagram)
    (table : Fin r → Fin r → YoungDiagram) : ℕ :=
  ∏ i, polynomialLRC (mu i) (table i)

/-- Definition 11 and hollowness, counting each symmetric matrix once.
The square bound is the sum of margin sizes (PDF p.14). -/
def hollowSymmetricLRSum {r : ℕ} (mu : Fin r → YoungDiagram) : ℕ :=
  let B := ∑ i, (mu i).card
  ∑ table : PartitionTable r B,
    if (∀ i, (table i i).val = ⊥) ∧
        (∀ i j, (table i j).val = (table j i).val) ∧
        symmetricLRWeight mu (fun i j => (table i j).val) ≠ 0 then
      symmetricLRWeight mu (fun i j => (table i j).val) else 0

/-- Fixed-point-free involution count: the even product is (r-1)!! and equals
one at r=0; the odd branch is zero (PDF p.14, Example 13). -/
def pairingCount (r : ℕ) : ℕ :=
  if Even r then ∏ k ∈ Finset.range (r / 2), (2 * k + 1) else 0

/-- Sanity: finite degree-zero tensors have dimension one, including over the
zero vector space; the source's group ranks themselves are positive. -/
example {G : Type*} (M : Fin 0 → MatrixModel G) : (tensorModel M).dimension = 1 := by
  simp [tensorModel]

/-- Sanity: no distinct tensor slots can be contracted in degree zero. -/
example (d : ℕ) (form : Matrix (Fin d) (Fin d) ℂ) :
    traceFree (m := 0) form = ⊤ := by
  simp [traceFree]

/-- Sanity: both parity and factorial conventions give the unique empty pairing. -/
example : pairingCount 0 = 1 := by simp [pairingCount]

/-- Sanity: a zero-margin empty rectangular table is counted once. -/
example : contingencyCount (fun i : Fin 0 => i.elim0)
    (fun j : Fin 0 => j.elim0) (fun _ => True) = 1 := by
  simp [contingencyCount]

/-- Sanity: zero is an empty partition, not a positive part of size zero. -/
example : rowPartition 0 = ⊥ := by
  apply YoungDiagram.ext
  simp [rowPartition, diagram, List.mergeSort, YoungDiagram.ofRowLens,
    YoungDiagram.cellsOfRowLens]

/-- Sanity: negative labels absent means the padded tuple is polynomial. -/
example (n : ℕ) (lambda : YoungDiagram) (i : Fin n) :
    weightEntry n (lambda, ⊥) i = (lambda.rowLen i.val : ℤ) := by
  simp [weightEntry, YoungDiagram.rowLen_eq_card, YoungDiagram.row]

/-- Sanity: the alternating pairing has the expected signs on one symplectic pair. -/
example : classicalAlternatingMatrix 1 0 1 = 1 ∧ classicalAlternatingMatrix 1 1 0 = -1 := by
  norm_num [classicalAlternatingMatrix]

end QAlgorithms.Papers.Independent.Next46.P07


