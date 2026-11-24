-- Prove2me | Definitions.Def_RequestProject_Aqt_ThetaDescent
-- name    : RequestProject_Aqt_ThetaDescent
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:54:31.024226+00:00
-- url     : https://prove2.me/theorems/f738596d-440b-430c-b4a3-a3a93d013e19
-- title:
--   Theta Descent
-- statement:
--   Definitions and structural lemmas for Theta Descent, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/ThetaDescent.lean

import Definitions.Def_RequestProject_Aqt_Theta
set_option autoImplicit true
namespace DyckAlgebra
universe v
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜}
variable {C : Type v} [Ring C] [Algebra 𝕜 C]
def thetaPre (thetaGen : Gen → C) : Pre 𝕜 →ₐ[𝕜] C :=
  FreeAlgebra.lift 𝕜 thetaGen
def thetaDescent (thetaGen : Gen → C)
    (preserves : ∀ ⦃a b : Pre 𝕜⦄, Rel q t a b →
      thetaPre thetaGen a = thetaPre thetaGen b) :
    Aqt q t →ₐ[𝕜] C :=
  RingQuot.liftAlgHom 𝕜 ⟨thetaPre thetaGen, preserves⟩
end DyckAlgebra


