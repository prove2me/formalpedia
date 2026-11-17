-- Prove2me | Definitions.Def_N25_UnitPlaneFieldPointOverField
-- name    : N25_UnitPlaneFieldPointOverField
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:03:40.359337+00:00
-- url     : https://prove2.me/theorems/bc2f8082-8e61-4ec0-8b12-ba07fe8273ab
-- title:
--   Evaluation of unit-plane points over arbitrary fields
-- statement:
--   Let $K$ and $F$ be fields with a $K$-algebra structure on $F$, and let $u,v∈F$ satisfy the unit-plane equation $R(u,v)=0$. The file defines the induced $K$-algebra homomorphism $$K[U,V]/(R)→F,\qquad U↦u,\quad V↦v.$$ This is the basic evaluation map used to realize the plane coordinate ring and its function field at field-valued points.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneAlgebraOverRing
/-! Evaluation of the unit-plane coordinate ring over an arbitrary coefficient field. -/
noncomputable section
namespace N25

/-- A field-valued point of the plane equation defines a map of its actual coordinate ring. -/
def unitPlaneFieldPointEvaluation25C {K F : Type*} [Field K] [Field F] [Algebra K F]
    (u v : F) (hr : planeRelation u v = 0) : UnitPlaneRing25C K →ₐ[K] F :=
  AdjoinRoot.liftAlgHom (unitPlanePolynomial25C K) (Polynomial.aeval u) v (by
    simpa [unitPlanePolynomial25C, planeRelation, Polynomial.eval₂_pow] using hr)

end N25


