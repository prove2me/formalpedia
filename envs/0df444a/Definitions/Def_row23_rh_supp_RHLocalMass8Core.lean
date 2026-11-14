-- Prove2me | Definitions.Def_row23_rh_supp_RHLocalMass8Core
-- name    : row23_rh_supp_RHLocalMass8Core
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-13T22:18:37.30018+00:00
-- url     : https://prove2.me/theorems/524f6e4d-1626-466d-ba33-50c85f1f2e30
-- title:
--   Row 23 RH support: RHLocalMass8Core
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLegendreCellBounds
import Definitions.Def_row23_rh_supp_RHLegendreMassPolynomial
set_option autoImplicit false
set_option maxHeartbeats 30000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 100000
namespace RHLocalMass8
open Polynomial Finset MeasureTheory intervalIntegral DusartLegendreSmoothing
noncomputable def p : ℚ[X] := rationalMassPolynomial 8 (1/1000000000:ℚ)
end RHLocalMass8


