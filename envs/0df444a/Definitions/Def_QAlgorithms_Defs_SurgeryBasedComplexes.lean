-- Prove2me | Definitions.Def_QAlgorithms_Defs_SurgeryBasedComplexes
-- name    : QAlgorithms_Defs_SurgeryBasedComplexes
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:26:08.939896+00:00
-- url     : https://prove2.me/theorems/a73cb97d-9543-4859-88a3-77589228f95d
-- title:
--   SurgeryBasedComplexes
-- statement:
--   SurgeryBasedComplexes
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\SurgeryBasedComplexes.lean

import Definitions.Def_QAlgorithms_Defs_BinaryCheckPresentations
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.Surgery

/-- Finitely many binary coordinates graded by integers; the single block matrix has
only degree-minus-one entries (2510.14895 pp.10--11,32).
arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11; arxiv-2510.14895v1 PDF p.32. -/
structure BasedBinaryComplex where
  Cell : Type
  finite : Fintype Cell
  degree : Cell → ℤ
  differential : Matrix Cell Cell (ZMod 2)
  lowers : ∀ a b, differential a b ≠ 0 → degree a+1 = degree b
  square : differential*differential = 0

attribute [instance] BasedBinaryComplex.finite

/-- The specified coordinate basis in integer degree i (2510.14895 p.10). -/
abbrev Basis (C : BasedBinaryComplex) (i : ℤ) := {a : C.Cell // C.degree a = i}

/-- The degreewise boundary matrix, extracted from the graded block matrix
(2510.14895 pp.10--11). -/
def boundary (C : BasedBinaryComplex) (i : ℤ) :
    Matrix (Basis C (i-1)) (Basis C i) (ZMod 2) :=
  C.differential.submatrix Subtype.val Subtype.val

/-- Actual cycle subspace (2510.14895 p.11). -/
def cycles (C : BasedBinaryComplex) (i : ℤ) := LinearMap.ker (boundary C i).mulVecLin

/-- Actual boundaries restricted to cycles (2510.14895 p.11). -/
def boundaries (C : BasedBinaryComplex) (i : ℤ) : Submodule (ZMod 2) (cycles C i) :=
  (LinearMap.range (C.differential.submatrix
    (Subtype.val : Basis C i → C.Cell) (Subtype.val : Basis C (i+1) → C.Cell)).mulVecLin).comap (cycles C i).subtype

/-- Homology is the computed kernel/image quotient (2510.14895 p.11). -/
abbrev Homology (C : BasedBinaryComplex) (i : ℤ) := (cycles C i) ⧸ boundaries C i

/-- General based chain map; no injectivity or basis-preservation assumption
(2510.14895 pp.10--11,32).
arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11; arxiv-2510.14895v1 PDF p.32. -/
structure BasedChainMap (A C : BasedBinaryComplex) where
  matrix : Matrix C.Cell A.Cell (ZMod 2)
  graded : ∀ a b, matrix a b ≠ 0 → C.degree a = A.degree b
  commutes : C.differential*matrix = matrix*A.differential

/-- Degreewise component of an attaching map (2510.14895 pp.10--11). -/
def component {A C : BasedBinaryComplex} (f : BasedChainMap A C) (i : ℤ) :
    Matrix (Basis C i) (Basis A i) (ZMod 2) := f.matrix.submatrix Subtype.val Subtype.val

/-- Tagged binary direct sum, retaining the original coordinate bases
(2510.14895 pp.10--11,32).
arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11; arxiv-2510.14895v1 PDF p.32. -/
def directSumComplex (A C : BasedBinaryComplex) : BasedBinaryComplex where
  Cell := A.Cell ⊕ C.Cell
  finite := inferInstance
  degree := Sum.elim A.degree C.degree
  differential := Matrix.fromBlocks A.differential 0 0 C.differential
  lowers := by
    intro a b h
    cases a <;> cases b <;> simp only [Matrix.fromBlocks] at h ⊢
    · exact A.lowers _ _ h
    · contradiction
    · contradiction
    · exact C.lowers _ _ h
  square := by
    rw [Matrix.fromBlocks_multiply]
    simp [A.square,C.square]

/-- The empty based complex (2510.14895 p.10, zero object). -/
def zeroComplex : BasedBinaryComplex where
  Cell := Fin 0
  finite := inferInstance
  degree := fun _ => 0
  differential := 0
  lowers := by simp
  square := by simp

/-- Sanity check for the source model (arxiv-2510.14895v1 PDF p.10). -/
example : (directSumComplex zeroComplex zeroComplex).differential = 0 := by
  ext a b; exact Fin.elim0 (Sum.elim id id a)

end QAlgorithms.Surgery


