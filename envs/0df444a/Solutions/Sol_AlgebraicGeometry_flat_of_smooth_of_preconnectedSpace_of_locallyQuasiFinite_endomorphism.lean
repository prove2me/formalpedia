-- Prove2me | solution 1 for AlgebraicGeometry.flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/147a83bb-d066-5add-9060-ecc47fbefd18

import Mathlib
import Theorems.Thm_Module_Flat_of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_AlgebraicGeometry_LocallyQuasiFinite_ringKrullDim_stalk_quotient_eq_zero
import Theorems.Thm_AlgebraicGeometry_ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

open IsLocalRing

theorem solution
    {k : Type} [Field k] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of k)}
    [Smooth f] [PreconnectedSpace X]
    (h : X ⟶ X) (hov : h ≫ f = f) [LocallyQuasiFinite h] :
    Flat h := by
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := inferInstance
  haveI hnoeth : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  rw [AlgebraicGeometry.Flat.iff_flat_stalkMap]
  intro x
  haveI : Nonempty X := ⟨x⟩
  haveI hint : IsIntegral X := AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace f
  algebraize [(h.stalkMap x).hom]
  haveI : IsRegularLocalRing (X.presheaf.stalk x) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) x
  haveI : IsRegularLocalRing (X.presheaf.stalk (h.base x)) :=
    AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := f) (h.base x)
  haveI : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
  haveI : IsLocalHom (algebraMap
      ↑(X.presheaf.stalk (h.base x)) ↑(X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (h.stalkMap x).hom)

  have hfib : ringKrullDim (↑(X.presheaf.stalk x) ⧸
      (maximalIdeal ↑(X.presheaf.stalk (h.base x))).map
        (algebraMap ↑(X.presheaf.stalk (h.base x)) ↑(X.presheaf.stalk x))) = 0 :=
    AlgebraicGeometry.LocallyQuasiFinite.ringKrullDim_stalk_quotient_eq_zero h x

  have hdim : ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (X.presheaf.stalk (h.base x)) :=
    AlgebraicGeometry.ringKrullDim_stalk_eq_of_locallyQuasiFinite_endomorphism
      (f := f) h hov x
  exact Module.Flat.of_isLocalHom_of_isRegularLocalRing_of_ringKrullDim_quotient_eq_zero
    (X.presheaf.stalk (h.base x)) (X.presheaf.stalk x) hfib hdim

end S_AlgebraicGeometry_flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism
end P2MW
export P2MW.S_AlgebraicGeometry_flat_of_smooth_of_preconnectedSpace_of_locallyQuasiFinite_endomorphism (solution)
