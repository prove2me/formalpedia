-- Prove2me | Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
-- name    : QEC_Semantics_Entropy_MatrixRelative
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T12:37:54.565088+00:00
-- url     : https://prove2.me/theorems/6f86697f-3bc6-4595-bd83-5307c4aff533
-- title:
--   Matrix Relative
-- statement:
--   Definitions and structural lemmas for Matrix Relative, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Entropy/MatrixRelative.lean

import Definitions.Def_QEC_Semantics_Entropy_FiniteDimensional
import Definitions.Def_QEC_Locality_CorrectableRegions_LocalPauliErasureTransfer
set_option autoImplicit false
universe u
namespace QEC
namespace Semantics
open scoped BigOperators ComplexOrder Kronecker TensorProduct
noncomputable section
namespace FiniteMatrixEntropy
def logMatrix {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) : Matrix n n Complex :=
  hA.cfc Real.log
def log2Matrix {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n Complex) (hA : A.IsHermitian) : Matrix n n Complex :=
  hA.cfc (Real.logb 2)
def realTrace {n : Type u} [Fintype n] (A : Matrix n n Complex) : Real :=
  Complex.re A.trace
def relativeEntropy {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) : Real :=
  realTrace (A * (logMatrix A hA - logMatrix B hB))
def relativeEntropy2 {n : Type u} [Fintype n] [DecidableEq n]
    (A B : Matrix n n Complex) (hA : A.IsHermitian) (hB : B.IsHermitian) : Real :=
  realTrace (A * (log2Matrix A hA - log2Matrix B hB))
def overlapWeight {n : Type u} [Fintype n] [DecidableEq n]
    (U V : Matrix.unitaryGroup n Complex) (i j : n) : Real :=
  Complex.normSq ((star (U : Matrix n n Complex) * (V : Matrix n n Complex)) i j)
def epsilonRegularizationDenominator {n : Type u} [Fintype n] (epsilon : Real) : Real :=
  1 + epsilon * Fintype.card n
def epsilonRegularize {n : Type u} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (epsilon : Real) : Matrix n n Complex :=
  ((epsilonRegularizationDenominator (n := n) epsilon)⁻¹ : Real) •
    (B + (epsilon : Real) • (1 : Matrix n n Complex))
theorem epsilonRegularizationDenominator_pos {n : Type u} [Fintype n]
    {epsilon : Real} (hepsilon : 0 < epsilon) :
    0 < epsilonRegularizationDenominator (n := n) epsilon := by
  unfold epsilonRegularizationDenominator
  positivity
theorem epsilonRegularize_posDef {n : Type u} [Fintype n] [DecidableEq n]
    (B : Matrix n n Complex) (hB : B.PosSemidef) {epsilon : Real} (hepsilon : 0 < epsilon) :
    (epsilonRegularize B epsilon).PosDef := by
  unfold epsilonRegularize
  have hidentity : (epsilon • (1 : Matrix n n Complex)).PosDef := by
    exact (Matrix.PosDef.one (n := n)).smul hepsilon
  have hshift : (B + epsilon • (1 : Matrix n n Complex)).PosDef :=
    Matrix.PosDef.posSemidef_add hB hidentity
  exact Matrix.PosDef.smul hshift
    (inv_pos.mpr (epsilonRegularizationDenominator_pos (n := n) hepsilon))
noncomputable def partialTraceLeftRaw (H K : Type u)
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K] :
    Operator (CompositeSystem H K) →ₗ[Complex] Operator K :=
  (partialTraceRightRaw K H).comp
    ((TensorProduct.comm Complex H K).conj.toLinearMap)
end FiniteMatrixEntropy
end
end Semantics
end QEC


