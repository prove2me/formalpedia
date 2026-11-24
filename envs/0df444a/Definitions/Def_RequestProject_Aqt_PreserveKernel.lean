-- Prove2me | Definitions.Def_RequestProject_Aqt_PreserveKernel
-- name    : RequestProject_Aqt_PreserveKernel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:51:55.58619+00:00
-- url     : https://prove2.me/theorems/3677d552-f5ff-4c87-9115-1ba172d4d71f
-- title:
--   Preserve Kernel
-- statement:
--   Definitions and structural lemmas for Preserve Kernel, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/PreserveKernel.lean

import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
namespace DyckAlgebra
namespace DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)
end DyckRepU
end DyckAlgebra


