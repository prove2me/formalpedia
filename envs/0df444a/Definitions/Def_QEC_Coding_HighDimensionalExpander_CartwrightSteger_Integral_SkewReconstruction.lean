-- Prove2me | Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
-- name    : QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewReconstruction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-11T14:08:36.569079+00:00
-- url     : https://prove2.me/theorems/2dc07604-b171-473b-9674-0969479e23bc
-- title:
--   Skew Reconstruction
-- statement:
--   Definitions and structural lemmas for Skew Reconstruction, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Integral/SkewReconstruction.lean

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewCoordinates
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_skewLaurent_of_integralArithmetic

set_option autoImplicit false
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
noncomputable def integralCyclicCoordinate
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) : IntegralArithmeticRing P :=
  Classical.choose (hcoords p)
noncomputable def integralCyclicCoordinateSkew
    (P : BasePrime) (r : Rank) (x : CyclicAlgebra P r)
    (hcoords : ∀ p : Fin r.matrixRank × Fin r.matrixRank,
      ∃ a : IntegralArithmeticRing P,
        integralArithmeticToFunctionField P a =
          (functionFieldCyclicBasis P r).repr x p)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    CartwrightStegerSkewLaurentRing P r :=
  Classical.choose (exists_skewLaurent_of_integralArithmetic P r
    (integralCyclicCoordinate P r x hcoords p))
end QEC.Coding.HighDimensionalExpander.CartwrightSteger


