-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/97204446-e1a2-54b0-b415-f6556f5431aa

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_forall_exists_basis_map_eq_of_forall_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_iso_free_of_forall_exists_basis
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
p2m_attr_erase "simp" "PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply"

set_option autoImplicit false

open CategoryTheory Opposite AlgebraicGeometry

universe u

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] :
    Scheme.Modules.IsLocallyFreeOfRank d f.kaehler ∧
      Scheme.Modules.IsLocallyFreeOfRank 1 (f.topDifferentials d) := by
  have h1 : Scheme.Modules.IsLocallyFreeOfRank d f.kaehler := by
    refine ⟨fun x => ?_⟩
    obtain ⟨U, hxU, e, he⟩ :=
      AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension f d x
    exact ⟨U, hxU, AlgebraicGeometry.Scheme.Modules.nonempty_pullback_iso_free_of_forall_exists_basis
      f.kaehler U e
        (AlgebraicGeometry.Scheme.Modules.forall_exists_basis_map_eq_of_forall_isAffineOpen f.kaehler e he)⟩
  refine ⟨h1, ?_⟩
  unfold AlgebraicGeometry.Scheme.Hom.topDifferentials
  exact (AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_one_iff_isInvertible _).mpr
    (AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h1)

end S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isLocallyFreeOfRank_kaehler_and_topDifferentials_of_smoothOfRelativeDimension (solution)
