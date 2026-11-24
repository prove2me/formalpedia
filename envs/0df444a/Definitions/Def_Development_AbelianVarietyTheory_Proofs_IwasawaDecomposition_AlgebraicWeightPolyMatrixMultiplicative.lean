-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicative
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicative
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:03.30512+00:00
-- url     : https://prove2.me/theorems/7892242a-82c1-477a-bff4-1a9d09ee3696
-- title:
--   Algebraic Weight Poly Matrix Multiplicative
-- statement:
--   Definitions and structural lemmas for Algebraic Weight Poly Matrix Multiplicative, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraicWeightPolyMatrixMultiplicative.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EvalUnitaryCoordinateZeroOfRationalPointsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
noncomputable section
namespace GlobalTheory.AlgWtMul
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
def substL (A : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.C (A v.1 v.2.1 m) * MvPolynomial.X (v.1, m, v.2.2)
def substR (B : (L →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (v : (L →+* ℂ) × Fin n × Fin n) :
    MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ :=
  ∑ m : Fin n, MvPolynomial.X (v.1, v.2.1, m) * MvPolynomial.C (B v.1 m v.2.2)
end GlobalTheory.AlgWtMul


