-- Prove2me | Definitions.Def_QAlgorithms_Defs_HypergraphProducts
-- name    : QAlgorithms_Defs_HypergraphProducts
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T19:23:10.582835+00:00
-- url     : https://prove2.me/theorems/c9c89df0-5b22-41e7-940c-be191d5e334e
-- title:
--   HypergraphProducts
-- statement:
--   HypergraphProducts
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\HypergraphProducts.lean

import Definitions.Def_QAlgorithms_Defs_BinaryCSSParameters
noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix Kronecker

namespace QAlgorithms.HypergraphProduct

/-- Check-variable product; 0903.0566 pp.8,18, 1504.00822 p.5.
Called H_X in the first paper and H_Z in the second. -/
def checkVariable {R1 I1 R2 I2 : Type*} [DecidableEq I2] [DecidableEq R1]
    (H1 : Matrix R1 I1 (ZMod 2)) (H2 : Matrix R2 I2 (ZMod 2)) :
    Matrix (R1 × I2) ((I1 × I2) ⊕ (R1 × R2)) (ZMod 2) :=
  Matrix.fromCols (H1 ⊗ₖ 1) (1 ⊗ₖ H2.transpose)

/-- Variable-check product on identical physical coordinates; 0903.0566 pp.8,18. -/
def variableCheck {R1 I1 R2 I2 : Type*} [DecidableEq I1] [DecidableEq R2]
    (H1 : Matrix R1 I1 (ZMod 2)) (H2 : Matrix R2 I2 (ZMod 2)) :
    Matrix (I1 × R2) ((I1 × I2) ⊕ (R1 × R2)) (ZMod 2) :=
  Matrix.fromCols (1 ⊗ₖ H2) (H1.transpose ⊗ₖ 1)

/-- Row-major indexing, variable summand first; 0903.0566 pp.8,18. -/
def coordinateEquiv (n1 n2 r1 r2 : ℕ) :
    ((Fin n1 × Fin n2) ⊕ (Fin r1 × Fin r2)) ≃ Fin (n1*n2+r1*r2) :=
  (Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans finSumFinEquiv

/-- Constructed physical CSS subspace; 0903.0566 pp.3,8,18.
Orthogonality is a consequence, not an input assumption. -/
def code {n1 n2 r1 r2 : ℕ}
    (H1 : Matrix (Fin r1) (Fin n1) (ZMod 2))
    (H2 : Matrix (Fin r2) (Fin n2) (ZMod 2)) :
    Submodule ℂ (EuclideanSpace ℂ (Qubits (n1*n2+r1*r2))) :=
  let e := coordinateEquiv n1 n2 r1 r2
  cssCode (FieldCodes.parityCheckCode ((checkVariable H1 H2).submatrix id e.symm))
    (FieldCodes.parityCheckCode ((variableCheck H1 H2).submatrix id e.symm))

example : coordinateEquiv 1 1 1 1 (Sum.inl (0,0)) = 0 ∧
    coordinateEquiv 1 1 1 1 (Sum.inr (0,0)) = 1 := by decide

example : checkVariable (!![1] : Matrix (Fin 1) (Fin 1) (ZMod 2)) !![1]
    (0,0) (Sum.inl (0,0)) = 1 := by decide

end QAlgorithms.HypergraphProduct


