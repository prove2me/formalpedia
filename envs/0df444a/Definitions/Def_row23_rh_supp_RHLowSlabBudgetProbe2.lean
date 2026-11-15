-- Prove2me | Definitions.Def_row23_rh_supp_RHLowSlabBudgetProbe2
-- name    : row23_rh_supp_RHLowSlabBudgetProbe2
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-11-14T19:49:57.629094+00:00
-- url     : https://prove2.me/theorems/181fa699-f653-4585-9842-64a66d71708e
-- title:
--   Row 23 RH support: RHLowSlabBudgetProbe2
-- statement:
--   A Lean-checked supporting component of the finite-height Riemann hypothesis and Chebyshev psi reduction for the b=23 Dusart Table 1 bound. Its declarations and hypotheses are stated exactly in the attached Lean source; this module alone does not assert the complete row estimate.
-- source:
--   Supporting arithmetic and analytic certificate for P. Dusart, Ramanujan J. 45 (2018), Table 1 and explicit psi bounds, pp. 233–235, DOI 10.1007/s11139-016-9839-4.

import Definitions.Def_row23_rh_supp_RHLowSlabBudgetProbe
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
open Arb4 Arb4.Q
def candidate2 (n r radiusDen : ℕ) : SlabD := { candidate n r with
  Qr := 10^15, L := Q.ofNat 7, R := Q.frac 1 radiusDen }


