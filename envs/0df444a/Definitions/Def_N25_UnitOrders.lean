-- Prove2me | Definitions.Def_N25_UnitOrders
-- name    : N25_UnitOrders
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:00:16.536116+00:00
-- url     : https://prove2.me/theorems/5fb59fbe-b8f8-4b70-bcb7-bf2f0368fb92
-- title:
--   The cyclic cusp-order matrix of five modular units
-- statement:
--   Defines the integer matrix $(ord_{P_j}u_i)_{0≤i,j<5}$ with rows given by cyclic shifts of $(1,−1,2,1,−3)$. This frozen table is a certificate carrier for the divisors and multiplicative relations of the five units.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
set_option autoImplicit false
namespace N25

/-- The frozen cyclic order table of the five original units. -/
def unitOrders25 : Fin 5 → Fin 5 → ℤ :=
  ![![ 1, -1,  2,  1, -3],
    ![-1,  2,  1, -3,  1],
    ![ 2,  1, -3,  1, -1],
    ![ 1, -3,  1, -1,  2],
    ![-3,  1, -1,  2,  1]]

end N25


