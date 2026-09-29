-- Prove2me | solution 1 for AlgebraicGeometry.SchemeHomOver.ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/fdc4d374-e880-51dc-9081-7818cf1b0302

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

open CategoryTheory.Limits in
theorem solution
    (κ : Type u) [Field κ] [IsAlgClosed κ] {X Y : Scheme.{u}}
    {gX : X ⟶ Spec (CommRingCat.of κ)} {gY : Y ⟶ Spec (CommRingCat.of κ)}
    [LocallyOfFiniteType gX] [IsReduced X]
    (φ ψ : SchemeHomOver gX gY)
    (h : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) gX, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by
  classical
  haveI : JacobsonSpace ↥X := LocallyOfFiniteType.jacobsonSpace gX

  let fg : X ⟶ pullback gY gY := pullback.lift φ.1 ψ.1 (φ.2.trans ψ.2.symm)
  have hfg1 : fg ≫ pullback.fst gY gY = φ.1 := pullback.lift_fst _ _ _
  have hfg2 : fg ≫ pullback.snd gY gY = ψ.1 := pullback.lift_snd _ _ _
  let ι := pullback.fst fg (pullback.diagonal gY)
  haveI : IsImmersion ι := MorphismProperty.pullback_fst _ _ inferInstance

  have hι : ι ≫ φ.1 = ι ≫ ψ.1 := by
    have hc : ι ≫ fg = pullback.snd fg (pullback.diagonal gY) ≫ pullback.diagonal gY := pullback.condition
    have h1 := congrArg (· ≫ pullback.fst gY gY) hc
    have h2 := congrArg (· ≫ pullback.snd gY gY) hc
    simp only [Category.assoc, hfg1, hfg2, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [h1, h2]

  have hcl : closedPoints ↥X ⊆ Set.range ι := by
    intro x hx
    let xp : Spec (CommRingCat.of κ) ⟶ X := pointOfClosedPoint gX x hx
    have hxp : xp ≫ gX = 𝟙 _ := pointOfClosedPoint_comp gX x hx
    have heq : xp ≫ φ.1 = xp ≫ ψ.1 := h ⟨xp, hxp⟩
    let e : Spec (CommRingCat.of κ) ⟶ pullback fg (pullback.diagonal gY) :=
      pullback.lift xp (xp ≫ φ.1) (by
        apply pullback.hom_ext
        · rw [Category.assoc, hfg1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
        · rw [Category.assoc, hfg2, Category.assoc, pullback.diagonal_snd, Category.comp_id, heq])
    have he : e ≫ ι = xp := pullback.lift_fst _ _ _
    refine ⟨e (IsLocalRing.closedPoint κ), ?_⟩
    rw [← Scheme.Hom.comp_apply, he]
    exact pointOfClosedPoint_apply gX x hx _

  have hrange : Set.range ι = Set.univ := by
    obtain ⟨U, Z, hU, hZ, hUZ⟩ := ι.isLocallyClosed_range
    have hZ' : Z = Set.univ := by
      apply Set.eq_univ_of_univ_subset
      rw [← closure_closedPoints (X := ↥X)]
      exact closure_minimal (hcl.trans (hUZ.le.trans Set.inter_subset_right)) hZ
    rw [hZ', Set.inter_univ] at hUZ
    rw [hUZ]
    by_contra hne
    obtain ⟨x, hxU, hxc⟩ := nonempty_inter_closedPoints (Z := Uᶜ)
      (Set.nonempty_compl.mpr hne) hU.isClosed_compl.isLocallyClosed
    exact hxU (hUZ ▸ hcl hxc)
  haveI : IsClosedImmersion ι := IsClosedImmersion.of_isPreimmersion ι (by rw [hrange]; exact isClosed_univ)
  haveI : Surjective ι := ⟨Set.range_eq_univ.mp hrange⟩
  haveI : IsIso ι := isIso_of_isClosedImmersion_of_surjective ι
  apply Subtype.ext
  rw [← cancel_epi ι]
  exact hι

end S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType
end P2MW
export P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_point_of_isReduced_of_locallyOfFiniteType (solution)
