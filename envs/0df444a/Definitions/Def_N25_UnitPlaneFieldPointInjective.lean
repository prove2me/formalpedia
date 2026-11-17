-- Prove2me | Definitions.Def_N25_UnitPlaneFieldPointInjective
-- name    : N25_UnitPlaneFieldPointInjective
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:05:24.795173+00:00
-- url     : https://prove2.me/theorems/e544e318-cf51-4702-929f-ae8ba71a7934
-- title:
--   Injective evaluation at a transcendental plane point
-- statement:
--   For a field-valued solution $(u,v)$ of $F(u,v)=0$, identifies the restriction of the coordinate-ring evaluation map to $ℚ[u]$ with ordinary polynomial evaluation $p↦p(u)$. When $u$ is transcendental over $ℚ$, the full map from the plane coordinate ring is injective, allowing evaluation to extend to its function field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_UnitPlaneFieldPoint
import Definitions.Def_N25_UnitPlaneDomain
namespace N25

/-- The coordinate-ring point map restricts to polynomial evaluation in its first coordinate. -/
theorem unitPlaneFieldPointEvaluation25_base {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) (a : Polynomial ℚ) :
    unitPlaneFieldPointEvaluation25 u v hr (algebraMap (Polynomial ℚ) UnitPlaneRing a) =
      Polynomial.aeval u a := by
  simp [unitPlaneFieldPointEvaluation25, AdjoinRoot.algebraMap_eq]

/-- Transcendence of the first coordinate makes the actual plane point map injective. -/
theorem unitPlaneFieldPointEvaluation25_injective {F : Type*} [Field F] [Algebra ℚ F]
    (u v : F) (hr : planeRelation u v = 0) (hu : Transcendental ℚ u) :
    Function.Injective (unitPlaneFieldPointEvaluation25 u v hr) := by
  letI : IsDomain UnitPlaneRing := unitPlaneRing_isDomain
  letI : Module.Finite (Polynomial ℚ) UnitPlaneRing := unitPlanePolynomial_monic.finite_adjoinRoot
  letI : Algebra.IsIntegral (Polynomial ℚ) UnitPlaneRing := Algebra.IsIntegral.of_finite _ _
  change Function.Injective (unitPlaneFieldPointEvaluation25 u v hr).toRingHom
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := Polynomial ℚ)
  ext a
  change unitPlaneFieldPointEvaluation25 u v hr
    (algebraMap (Polynomial ℚ) UnitPlaneRing a) = 0 ↔ a = 0
  rw [unitPlaneFieldPointEvaluation25_base]
  constructor
  · intro ha
    apply (transcendental_iff_injective.mp hu)
    simpa using ha
  · intro ha
    rw [ha, map_zero]

end N25


