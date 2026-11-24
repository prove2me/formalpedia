-- Prove2me | Definitions.Def_RequestProject_Aqt_DGamma
-- name    : RequestProject_Aqt_DGamma
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:52:51.475326+00:00
-- url     : https://prove2.me/theorems/66861e55-1b03-4767-9099-1acd512d7484
-- title:
--   DGamma
-- statement:
--   Definitions and structural lemmas for DGamma, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/DGamma.lean

import Definitions.Def_RequestProject_Aqt_PreserveKernel
set_option autoImplicit true
namespace DyckAlgebra
namespace DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
def dGammaTail : List ℕ → ρ.carrier
  | [] => ρ.zz 1 * ρ.dp
  | g :: gs => ρ.zz 1 * (-ρ.yy 1) ^ g * dGammaTail gs
def dGamma : List ℕ → ρ.carrier
  | [] => 0
  | g :: gs => ρ.dm * (-ρ.yy 1) ^ (g - 1) * ρ.dGammaTail gs
def thetaDGammaTail : List ℕ → ρ.carrier
  | [] => ρ.Θz1 * ρ.Θdp
  | g :: gs => ρ.Θz1 * (-ρ.Θy1) ^ g * thetaDGammaTail gs
def thetaDGamma : List ℕ → ρ.carrier
  | [] => 0
  | g :: gs => ρ.dm * (-ρ.Θy1) ^ (g - 1) * ρ.thetaDGammaTail gs
def e1Word : ρ.carrier := ρ.dm * ρ.dp
def dOneWord : ρ.carrier := ρ.dm * (-ρ.yy 1) * ρ.dps
def dPositiveSeries : ρ.carrier := ρ.dm * ρ.w 1 * (-ρ.yy 1) * ρ.dps
def thetaE1Word : ρ.carrier := ρ.dm * ρ.Θdp
def thetaDOneWord : ρ.carrier := ρ.dm * (-ρ.Θy1) * ρ.Θdps
end DyckRepU
end DyckAlgebra


