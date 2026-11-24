-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPolynomialRepGLComplexAlgebraicWeightEvalPoint
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:10.687723+00:00
-- url     : https://prove2.me/theorems/e3ec29ff-ea7f-4884-8705-d602b97b0b5b
-- title:
--   Is Polynomial Rep GLComplex Algebraic Weight Eval Point
-- statement:
--   Definitions and structural lemmas for Is Polynomial Rep GLComplex Algebraic Weight Eval Point, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsPolynomialRepGLComplexAlgebraicWeightEvalPoint.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ConjugateNeSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraicWeightPolyMatrixMultiplicativeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SpanRationalPointOrbitAlgebraicWeightStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW
namespace GlobalTheory.AlgWtHW
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}
open Classical in

def tauSubst (τ : L →+* ℂ) : (L →+* ℂ) × Fin n × Fin n →
    MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ := fun p =>
  if p.1 = τ then MvPolynomial.X (Sum.inl (p.2.1, p.2.2))
  else if p.1 = ComplexEmbedding.conjugate τ then MvPolynomial.X (Sum.inr (p.2.2, p.2.1))
  else MvPolynomial.C ((1 : Matrix (Fin n) (Fin n) ℂ) p.2.1 p.2.2)
end GlobalTheory.AlgWtHW


