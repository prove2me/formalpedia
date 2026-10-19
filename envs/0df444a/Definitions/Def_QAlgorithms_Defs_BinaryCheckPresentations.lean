-- Prove2me | Definitions.Def_QAlgorithms_Defs_BinaryCheckPresentations
-- name    : QAlgorithms_Defs_BinaryCheckPresentations
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:59.792171+00:00
-- url     : https://prove2.me/theorems/efa95d2d-65f4-4ef4-8a02-95afd68a988a
-- title:
--   BinaryCheckPresentations
-- statement:
--   BinaryCheckPresentations
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\BinaryCheckPresentations.lean

import Definitions.Def_QAlgorithms_Defs_BinaryCSSParameters
noncomputable section

open scoped Matrix ComplexOrder

attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

namespace QAlgorithms.PresentedCSS

/-- arxiv-2206.13228v4 PDF p.2; arxiv-2510.14895v1 PDF p.9; arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11. -/
structure CheckPresentation (n mx mz : ℕ) where
  HX : Matrix (Fin mx) (Fin n) (ZMod 2)
  HZ : Matrix (Fin mz) (Fin n) (ZMod 2)
  orthogonal : HX*HZ.transpose = 0
  css : codeDual (FieldCodes.parityCheckCode HZ) ≤ FieldCodes.parityCheckCode HX

/-- arxiv-2510.14895v1 PDF p.9; arxiv-2510.14895v1 PDF p.16; arxiv-2510.14895v1 PDF p.32; arxiv-2206.13228v4 PDF p.2. -/
def HasSparsity {R I : Type*} [Fintype R] [Fintype I] (H : Matrix R I (ZMod 2)) (s : ℕ) : Prop :=
  (∀ r, (Finset.univ.filter fun i => H r i ≠ 0).card ≤ s) ∧
  ∀ i, (Finset.univ.filter fun r => H r i ≠ 0).card ≤ s

/-- The classical X code, ker HX (NLTS p.2; surgery pp.10--11).
arxiv-2206.13228v4 PDF p.2; arxiv-2510.14895v1 PDF p.9; arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11. -/
def CheckPresentation.Cx {n mx mz : ℕ} (C : CheckPresentation n mx mz) := FieldCodes.parityCheckCode C.HX

/-- The classical Z code, ker HZ (NLTS p.2; surgery pp.10--11).
arxiv-2206.13228v4 PDF p.2; arxiv-2510.14895v1 PDF p.9; arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11. -/
def CheckPresentation.Cz {n mx mz : ℕ} (C : CheckPresentation n mx mz) := FieldCodes.parityCheckCode C.HZ

/-- Computed logical dimension of the CSS quotient (surgery p.11).
arxiv-2206.13228v4 PDF p.2; arxiv-2510.14895v1 PDF p.9; arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11. -/
def CheckPresentation.logicalDimension {n mx mz : ℕ} (C : CheckPresentation n mx mz) : ℕ :=
  BinaryCSS.logicalDimension C.Cx C.Cz C.css

/-- Computed CSS distance, with infinite empty-quotient distance (surgery p.11).
arxiv-2206.13228v4 PDF p.2; arxiv-2510.14895v1 PDF p.9; arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11. -/
def CheckPresentation.distance {n mx mz : ℕ} (C : CheckPresentation n mx mz) : ℕ∞ :=
  BinaryCSS.distance C.Cx C.Cz C.css

/-- The physical +1 eigenspace of the HX X checks and HZ Z checks (surgery p.10).
The frozen constructor takes the Z kernel first and the X kernel second.
arxiv-2206.13228v4 PDF p.2; arxiv-2510.14895v1 PDF p.9; arxiv-2510.14895v1 PDF p.10; arxiv-2510.14895v1 PDF p.11. -/
def CheckPresentation.code {n mx mz : ℕ} (C : CheckPresentation n mx mz) := cssCode C.Cz C.Cx

/-- Sanity check for the source model (arxiv-2206.13228v4 PDF p.2). -/
example {R I : Type*} [Fintype R] [Fintype I] : HasSparsity (0 : Matrix R I (ZMod 2)) 0 := by
  simp [HasSparsity]

end QAlgorithms.PresentedCSS


