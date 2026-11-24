-- Prove2me | Definitions.Def_HodgeComputerCycleQ2DenomX2Cubed
-- name    : HodgeComputerCycleQ2DenomX2Cubed
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-24T17:37:48.969794+00:00
-- url     : https://prove2.me/theorems/53b86eaa-8a11-4677-ba71-e0fd3dd1fc5b
-- title:
--   NormalChart denominator $X_2^3$
-- statement:
--   Write $\mathtt{denomX2Cubed}$ for the ambient monomial $X_2^3$ used as the fixed NormalChart denominator in the character-zero degree-three specialization of the cyclic sextic residue system.
-- source:
--   Abbreviation for S=X_2^3 in CycleQ2 NormalChart linear system (Prove2Me 9d61a7a7).

import Definitions.Def_HodgeComputerCycleQ2

set_option autoImplicit false
noncomputable section
open HodgeComputer HodgeComputer.CycleQ2

/-- The fixed NormalChart denominator $X_2^3$. -/
def HodgeComputer.CycleQ2.denomX2Cubed : AmbientPoly n :=
  (MvPolynomial.X (R := ℂ) (2 : Fin 6)) ^ (3 : ℕ)


