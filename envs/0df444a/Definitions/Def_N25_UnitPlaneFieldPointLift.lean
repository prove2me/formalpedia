-- Prove2me | Definitions.Def_N25_UnitPlaneFieldPointLift
-- name    : N25_UnitPlaneFieldPointLift
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:15:41.134017+00:00
-- url     : https://prove2.me/theorems/e86b0d22-f561-41ec-aa84-d8bda09c24a9
-- title:
--   From a transcendental plane point to the function field
-- statement:
--   Given a field-valued point of the plane relation whose first coordinate is transcendental over the rationals, defines the induced homomorphism from the actual plane function field to the target field. This upgrades affine evaluation to the function-field map used to compare modular functions.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CanonicalFunctionField
import Definitions.Def_N25_UnitPlaneFieldPointInjective
noncomputable section
namespace N25

/-- A field-valued plane point with transcendental first coordinate defines a
homomorphism on the actual plane function field. -/
def unitPlaneFieldPointLift25 {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental ℚ u) :
    UnitPlaneFF25 →ₐ[ℚ] F :=
  IsFractionRing.liftAlgHom (unitPlaneFieldPointEvaluation25_injective u v hr hu)

end N25


