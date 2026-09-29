-- Prove2me | solution 1 for AlgebraicCurve.isAffineOpen_of_maximal_domain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/0e9c03b4-4ba3-5ce5-935b-3d4ff29fdb87

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal
import Theorems.Thm_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
import Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_isAffineOpen_of_maximal_domain

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial AlgebraicGeometry.Polynomial"

theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s)) :
    IsAffineOpen U := by

  let φ : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k[X]) :=
    (U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))

  haveI : IsProper φ := Scheme.Opens.isProper_toSpecPolynomial_of_maximal c
    (valuationRing_stalk_of_smoothOfRelativeDimension_one c) U s hU

  haveI : LocallyQuasiFinite φ := LocallyQuasiFinite.of_finite_preimage_singleton φ
    (Scheme.Opens.finite_preimage_singleton_toSpecPolynomial c U s hs)

  haveI : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  exact isAffine_of_isAffineHom φ

end S_AlgebraicCurve_isAffineOpen_of_maximal_domain
end P2MW
export P2MW.S_AlgebraicCurve_isAffineOpen_of_maximal_domain (solution)
