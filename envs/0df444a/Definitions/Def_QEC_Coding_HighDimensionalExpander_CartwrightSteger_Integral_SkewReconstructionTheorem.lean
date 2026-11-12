-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstructionTheorem
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:11:13.961201+00:00
-- url     : https://prove2.me/theorems/501eee70-18d4-4131-be3c-a7c8b6d1b0f7
-- title:
--   Skew Reconstruction Theorem
-- statement:
--   Definitions and structural lemmas for Skew Reconstruction Theorem, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstructionTheorem.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def integralCyclicSkewReconstruction
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p) :
    CartwrightStegerSkewLaurentRing P r :=
  ∑ p, integralCyclicCoordinateSkew P r x hcoords p *
    skewLaurentCyclicBasisMonomial P r p
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


