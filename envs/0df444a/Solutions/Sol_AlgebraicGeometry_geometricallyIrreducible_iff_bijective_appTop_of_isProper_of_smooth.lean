-- Prove2me | solution 1 for AlgebraicGeometry.geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/3705e717-8940-598a-91a2-35587cc0a7d8

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_pullback_snd_of_bijective_appTop
import Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_bijective_algebraMap_sections
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace H2a2N1

variable {K : Type u} [Field K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K))

theorem geometricallyReduced_of_smooth [Smooth g] : GeometricallyReduced g := by
  refine ⟨fun L _ y Z fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback (P := @Smooth) h inferInstance
  exact AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian snd

theorem bijective_of_geometricallyIrreducible [IsProper g] [Smooth g] [GeometricallyIrreducible g] :
    Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom := by
  haveI := AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected g
  haveI := geometricallyReduced_of_smooth g
  have h := AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected g
  rw [CommRingCat.hom_comp]
  exact h.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)

theorem geometricallyIrreducible_of_bijective [IsProper g] [Smooth g] [Nonempty ↥X]
    (hb : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom) :
    GeometricallyIrreducible g := by
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace g
  haveI : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated g

  haveI hgc : GeometricallyConnected g := by
    refine AlgebraicGeometry.geometricallyConnected_of_bijective_algebraMap_sections g fun A _ _ => ?_
    have h0 := AlgebraicGeometry.bijective_appTop_pullback_snd_of_bijective_appTop g hb A
    dsimp only [Scheme.Hom.appTop] at h0
    rw [Scheme.Hom.app_eq_appLE] at h0
    exact h0

  let kb : Type u := AlgebraicClosure K
  let y : Spec (CommRingCat.of kb) ⟶ Spec (CommRingCat.of K) := Spec.map (CommRingCat.ofHom (algebraMap K kb))
  haveI : ConnectedSpace ↥(pullback g y) :=
    hgc.geometrically_connectedSpace y _ _ (IsPullback.of_hasPullback g y)
  haveI : Nonempty ↥(pullback g y) := by
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥X)
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := y) x (IsLocalRing.closedPoint kb)
      (Subsingleton.elim _ _)
    exact ⟨z⟩
  haveI : IsIntegral (pullback g y) :=
    AlgebraicGeometry.isIntegral_of_smooth_of_preconnectedSpace (pullback.snd g y)
  exact AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_pullback_of_isAlgClosed g kb

theorem main [IsProper g] [Smooth g] [Nonempty ↥X] :
    GeometricallyIrreducible g ↔ Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom :=
  ⟨fun _ => bijective_of_geometricallyIrreducible g, geometricallyIrreducible_of_bijective g⟩

end H2a2N1

theorem solution
    {K : Type u} [Field K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K)) [IsProper g] [Smooth g] [Nonempty ↥X] :
    GeometricallyIrreducible g ↔ Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop).hom :=
  H2a2N1.main g

end S_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth
end P2MW
export P2MW.S_AlgebraicGeometry_geometricallyIrreducible_iff_bijective_appTop_of_isProper_of_smooth (solution)
