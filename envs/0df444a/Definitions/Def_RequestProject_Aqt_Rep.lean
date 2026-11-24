-- Prove2me | Definitions.Def_RequestProject_Aqt_Rep
-- name    : RequestProject_Aqt_Rep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T22:49:57.583863+00:00
-- url     : https://prove2.me/theorems/8eeb3472-1588-4a11-b968-fe6ecf617fef
-- title:
--   Rep
-- statement:
--   Definitions and structural lemmas for Rep, from SashaIr/leaving-the-hall contributors (see pinned CC0-1.0 LICENSE and source headers)'s pinned Dyck-path algebra and decorated-Dyck-path bijection development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/SashaIr/leaving-the-hall/blob/309149b9b3284a81cdbde5de942f50696d16bec0/RequestProject/Aqt/Rep.lean

import Definitions.Def_RequestProject_Aqt_Algebra
set_option autoImplicit true
namespace DyckAlgebra
universe v
structure AqtAction (𝕜 : Type*) [Field 𝕜] (q t : 𝕜) where
  /-- The total carrier of the graded representation. -/
  carrier : Type v
  [addCommGroup : AddCommGroup carrier]
  [module : Module 𝕜 carrier]
  /-- The algebra homomorphism defining the action. -/
  act : Aqt q t →ₐ[𝕜] Module.End 𝕜 carrier
attribute [instance] AqtAction.addCommGroup AqtAction.module
namespace AqtAction
variable {𝕜 : Type*} [Field 𝕜] {q t : 𝕜} (ρ : AqtAction 𝕜 q t)
def apply (a : Aqt q t) (v : ρ.carrier) : ρ.carrier := ρ.act a v
end AqtAction
end DyckAlgebra


