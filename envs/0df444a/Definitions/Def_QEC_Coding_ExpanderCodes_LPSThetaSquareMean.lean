-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaSquareMean
-- name    : QEC_Coding_ExpanderCodes_LPSThetaSquareMean
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-19T07:23:53.065322+00:00
-- url     : https://prove2.me/theorems/db0ed7da-ea32-4cc5-a607-96142e51a212
-- title:
--   LPSTheta Square Mean
-- statement:
--   Definitions and structural lemmas for LPSTheta Square Mean, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LPSThetaSquareMean.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSCuspSquareLSeries
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSThetaCuspidalRemainder
set_option autoImplicit false
namespace QEC.Coding.TannerLiftedProduct
open Complex Filter Topology MeasureTheory Asymptotics
open scoped MatrixGroups UpperHalfPlane ModularForm
noncomputable def lpsThetaSquareCoeff (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (n : ℕ) : ℝ :=
  lpsWeightTwoCusp_squareCoeff ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) n
noncomputable def lpsThetaSquareMean (q : ℕ) [Fact q.Prime] (hq4 : q%4=1) (y : ℝ) : ℝ :=
  lpsCuspHorocycleSquareMean ((4*q)^2) (lpsThetaCuspidalRemainder q hq4) y
end QEC.Coding.TannerLiftedProduct


