-- Prove2me | solution 1 for AlgebraicGeometry.topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/678d11ee-4c31-5ccd-8fd9-a35673645228

import Mathlib
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace KrullBC

private theorem _root_.KrullBC.topologicalKrullDim_eq {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension n f] [Nonempty ↥X] : topologicalKrullDim ↥X = n :=
  le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f n) (SmoothOfRelativeDimension.le_topologicalKrullDim f n)

p2m_export "KrullBC" "topologicalKrullDim_eq"

theorem smoothOfRelativeDimension_fiber {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] (s : ↥Y)
    (hconn : _root_.IsConnected (f.base ⁻¹' {s})) (n : ℕ) (hdim : topologicalKrullDim ↥(f.base ⁻¹' {s}) = n) :
    Nonempty ↥(f.fiber s) ∧ SmoothOfRelativeDimension n (f.fiberToSpecResidueField s) := by
  haveI : Smooth (f.fiberToSpecResidueField s) := MorphismProperty.pullback_snd (P := @Smooth) _ _ inferInstance
  haveI : ConnectedSpace ↥(f.base ⁻¹' {s}) := isConnected_iff_connectedSpace.mp hconn
  haveI hne : Nonempty ↥(f.fiber s) := (Equiv.nonempty_congr (f.fiberHomeo s).toEquiv).mpr inferInstance
  haveI : PreconnectedSpace ↥(f.fiber s) := by
    constructor
    rw [← Set.preimage_univ (f := f.fiberHomeo s), Homeomorph.isPreconnected_preimage]
    exact isPreconnected_univ
  obtain ⟨m, hm⟩ := Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace (f.fiberToSpecResidueField s)
  have h1 : topologicalKrullDim ↥(f.fiber s) = m := @topologicalKrullDim_eq _ _ _ (f.fiberToSpecResidueField s) m hm hne
  have h2 : topologicalKrullDim ↥(f.fiber s) = topologicalKrullDim ↥(f.base ⁻¹' {s}) :=
    IsHomeomorph.topologicalKrullDim_eq _ (f.fiberHomeo s).isHomeomorph
  have hmn : m = n := by
    have : (m : WithBot ℕ∞) = n := by rw [← h1, h2, hdim]
    exact_mod_cast this
  subst hmn
  exact ⟨hne, hm⟩

theorem isPullback_fiber {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (s' : ↥Y') :
    ∃ u : (pullback.snd f g).fiber s' ⟶ f.fiber (g.base s'),
      IsPullback u ((pullback.snd f g).fiberToSpecResidueField s') (f.fiberToSpecResidueField (g.base s'))
        (Spec.map (g.residueFieldMap s')) := by

  have big := (IsPullback.of_hasPullback (pullback.snd f g) (Y'.fromSpecResidueField s')).paste_horiz
    (IsPullback.of_hasPullback f g)
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField] at big

  refine ⟨pullback.lift (pullback.fst (pullback.snd f g) (Y'.fromSpecResidueField s') ≫ pullback.fst f g)
      ((pullback.snd f g).fiberToSpecResidueField s' ≫ Spec.map (g.residueFieldMap s')) big.w, ?_⟩
  refine IsPullback.of_right (h₁₂ := f.fiberι (g.base s')) (h₂₂ := Y.fromSpecResidueField (g.base s')) ?_
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f (Y.fromSpecResidueField (g.base s')))
  have hlift : pullback.lift (pullback.fst (pullback.snd f g) (Y'.fromSpecResidueField s') ≫ pullback.fst f g)
      ((pullback.snd f g).fiberToSpecResidueField s' ≫ Spec.map (g.residueFieldMap s')) big.w ≫ f.fiberι (g.base s') =
      pullback.fst (pullback.snd f g) (Y'.fromSpecResidueField s') ≫ pullback.fst f g :=
    pullback.lift_fst _ _ _
  rw [← hlift] at big
  exact big

end KrullBC

open KrullBC in
theorem solution
    {S S' : Type u} [CommRing S] [CommRing S'] (φ : S →+* S')
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [Smooth f]
    (hconn : ∀ s : ↥(Spec (CommRingCat.of S)), _root_.IsConnected (f.base ⁻¹' {s}))
    (n : ℕ) (hdim : ∀ s : ↥(Spec (CommRingCat.of S)), topologicalKrullDim ↥(f.base ⁻¹' {s}) = n)
    (s' : ↥(Spec (CommRingCat.of S'))) :
    topologicalKrullDim ↥((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).base ⁻¹' {s'}) = n := by
  obtain ⟨hne, hsm⟩ := smoothOfRelativeDimension_fiber f ((Spec.map (CommRingCat.ofHom φ)).base s') (hconn _) n (hdim _)
  obtain ⟨u, hu⟩ := isPullback_fiber f (Spec.map (CommRingCat.ofHom φ)) s'
  haveI := hsm
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange n
  have hsm' : SmoothOfRelativeDimension n ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).fiberToSpecResidueField s') :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension n) hu hsm

  haveI : Surjective u := by
    refine MorphismProperty.of_isPullback (P := @Surjective) hu.flip ?_
    exact ⟨fun p => ⟨default, Subsingleton.elim _ _⟩⟩
  have hne' : Nonempty ↥((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).fiber s') := by
    obtain ⟨x⟩ := hne
    obtain ⟨x', -⟩ := u.surjective x
    exact ⟨x'⟩
  rw [← IsHomeomorph.topologicalKrullDim_eq _ ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).fiberHomeo s').isHomeomorph]
  exact @topologicalKrullDim_eq _ _ _ ((pullback.snd f (Spec.map (CommRingCat.ofHom φ))).fiberToSpecResidueField s') n hsm' hne'

end S_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
end P2MW
export P2MW.S_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected (solution)
