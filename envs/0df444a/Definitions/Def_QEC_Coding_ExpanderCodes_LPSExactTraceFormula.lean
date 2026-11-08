-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
-- name    : QEC_Coding_ExpanderCodes_LPSExactTraceFormula
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-07T11:48:44.027196+00:00
-- url     : https://prove2.me/theorems/1eb3ae96-04e7-4151-88e7-db6720fdf0b5
-- title:
--   LPSExact Trace Formula
-- statement:
--   Definitions and structural lemmas for LPSExact Trace Formula, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSExactTraceFormula.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
set_option autoImplicit false
open scoped MatrixGroups
namespace QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
noncomputable def lpsCenteredHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    Module.End ℂ (PSL(2, ZMod a.q) → ℂ) :=
  (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
    (algebraMap ℂ (Module.End ℂ (PSL(2, ZMod a.q) → ℂ)))
    (cayleyRightRegularRepresentation.asAlgebraHom
      (cayleyCenteredGeneratorSum (lpsQuaternionLabel a)))
noncomputable def lpsCenteredEuclideanHeckeOperator
    (a : LPSResiduePrime p) (n : ℕ) :
    Module.End ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q)) :=
  (lpsHeckePolynomial ℂ (p : ℂ) n).eval₂
    (algebraMap ℂ
      (Module.End ℂ (EuclideanSpace ℂ PSL(2, ZMod a.q))))
    (SmallSetExpansion.centeredAdjacencyEuclidean
      (rightCayleyGraph (lpsQuaternionLabel a))
      (Fintype.card (LPSGeneratorIndex p)))
end QEC.Coding.TannerLiftedProduct


