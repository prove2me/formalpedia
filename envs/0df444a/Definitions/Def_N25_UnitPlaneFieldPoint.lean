-- Prove2me | Definitions.Def_N25_UnitPlaneFieldPoint
-- name    : N25_UnitPlaneFieldPoint
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:02.183719+00:00
-- url     : https://prove2.me/theorems/04d64825-ba12-47aa-be39-7f83de5db4e0
-- title:
--   Evaluation at a field-valued plane point
-- statement:
--   Given $u,v∈F$ satisfying $F(u,v)=0$, defines the rational-algebra homomorphism from the affine plane coordinate ring to $F$ that sends the two coordinate classes to $u$ and $v$. It realizes field-valued solutions through the universal property of the quotient algebra.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneRing
noncomputable section
namespace N25

/-- A point of the plane equation in any rational field gives its coordinate-ring map. -/
def unitPlaneFieldPointEvaluation25 {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) : UnitPlaneRing →ₐ[ℚ] F :=
  AdjoinRoot.liftAlgHom unitPlanePolynomial (Polynomial.aeval u) v (by
    simpa [unitPlanePolynomial, planeRelation, Polynomial.eval₂_pow] using hr)

end N25


