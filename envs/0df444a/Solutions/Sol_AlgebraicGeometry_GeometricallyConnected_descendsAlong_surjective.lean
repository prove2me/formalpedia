-- Prove2me | solution 1 for AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/41c82a0b-d62e-55b7-a4a6-2547843d86ac

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective Spec Scheme GeometricallyConnected geometrically"
namespace GeometricallyConnectedDescentAux
p2m_open "AlgebraicGeometry"

theorem geometricallyConnected_of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S) [Surjective σ]
    [hgc : GeometricallyConnected (pullback.snd f σ)] : GeometricallyConnected f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩

  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp only [kL, l', Category.assoc, pullback.condition]
  haveI : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩

  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l') (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by rw [hm₁]; exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd b kL) sq

  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous

end AlgebraicGeometry.GeometricallyConnectedDescentAux

theorem solution :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by
  refine DescendsAlong.mk' fun {X Y Z} {f} {g} _ hf hfst => ?_
  haveI : Surjective f := hf
  haveI : GeometricallyConnected (pullback.fst f g) := hfst
  haveI : GeometricallyConnected (pullback.snd g f) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr hfst
  exact AlgebraicGeometry.GeometricallyConnectedDescentAux.geometricallyConnected_of_pullback_snd g f

end S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective (solution)
