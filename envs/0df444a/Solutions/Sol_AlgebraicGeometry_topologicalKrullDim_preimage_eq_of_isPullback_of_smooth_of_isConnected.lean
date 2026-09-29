-- Prove2me | solution 1 for AlgebraicGeometry.topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/a062f430-258c-5c91-b225-5217180a82cd

import Mathlib
import Theorems.Thm_AlgebraicGeometry_topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_preimage_singleton_eq
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_smoothOfRelativeDimension_of_preconnectedSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace DIMBCpgr

theorem topologicalKrullDim_preimage_eq_of_subsingleton {X B : Type} [TopologicalSpace X] [TopologicalSpace B]
    [Subsingleton B] (p : X → B) (b : B) :
    topologicalKrullDim ↥(p ⁻¹' {b}) = topologicalKrullDim X := by
  have hU : p ⁻¹' {b} = Set.univ := by
    ext x; simp [Subsingleton.elim (p x) b]
  rw [hU]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph

end DIMBCpgr

open DIMBCpgr in
theorem solution
    {X S X' S' : Scheme.{0}} (f : X ⟶ S) (hs : Smooth f) (b : S' ⟶ S) (f' : X' ⟶ S') (g : X' ⟶ X)
    (hg : IsPullback g f' f b) (s' : ↥S') (hconn : _root_.IsConnected (f.base ⁻¹' {b.base s'})) :
    topologicalKrullDim ↥(f'.base ⁻¹' {s'}) = topologicalKrullDim ↥(f.base ⁻¹' {b.base s'}) := by
  classical
  haveI := hs
  set s : ↥S := b.base s' with hsdef

  let F := f.fiber s
  let pF : F ⟶ Spec (S.residueField s) := f.fiberToSpecResidueField s
  haveI : Smooth pF := MorphismProperty.pullback_snd _ _ hs
  haveI hne : Nonempty ↥(f.base ⁻¹' {s}) := hconn.nonempty.to_subtype
  haveI : ConnectedSpace ↥(f.base ⁻¹' {s}) := isConnected_iff_connectedSpace.mp hconn
  haveI : ConnectedSpace ↥F := (f.fiberHomeo s).connectedSpace_iff.mpr inferInstance
  haveI : Subsingleton ↥(Spec (S.residueField s)) := inferInstanceAs (Subsingleton (PrimeSpectrum (S.residueField s)))
  haveI : Subsingleton ↥(Spec (S'.residueField s')) := inferInstanceAs (Subsingleton (PrimeSpectrum (S'.residueField s')))
  obtain ⟨n, hn⟩ := AlgebraicGeometry.Smooth.exists_smoothOfRelativeDimension_of_preconnectedSpace pF

  have hdimF : ∀ t : ↥(Spec (S.residueField s)), topologicalKrullDim ↥(pF.base ⁻¹' {t}) = n := by
    intro t
    haveI := hn
    refine AlgebraicGeometry.SmoothOfRelativeDimension.topologicalKrullDim_preimage_singleton_eq pF n t ?_
    obtain ⟨y⟩ := hne
    exact ⟨(f.fiberHomeo s).symm y, Subsingleton.elim _ _⟩
  have hconnF : ∀ t : ↥(Spec (S.residueField s)), _root_.IsConnected (pF.base ⁻¹' {t}) := by
    intro t
    have hU : pF.base ⁻¹' {t} = Set.univ := by ext x; simp [Subsingleton.elim (pF.base x) t]
    rw [hU]; exact isConnected_univ
  have hdim0 : topologicalKrullDim ↥(f.base ⁻¹' {s}) = n := by
    rw [← hdimF (IsLocalRing.closedPoint _), topologicalKrullDim_preimage_eq_of_subsingleton pF.base]
    exact (IsHomeomorph.topologicalKrullDim_eq (f.fiberHomeo s) (f.fiberHomeo s).isHomeomorph).symm

  let φ := b.residueFieldMap s'
  have hbc := AlgebraicGeometry.topologicalKrullDim_preimage_pullback_snd_eq_of_smooth_of_isConnected
    φ.hom pF hconnF n hdimF (IsLocalRing.closedPoint _)

  have sq1 : IsPullback (pullback.fst pF (Spec.map (CommRingCat.ofHom φ.hom)) ≫ f.fiberι s)
      (pullback.snd pF (Spec.map (CommRingCat.ofHom φ.hom))) f
      (Spec.map (CommRingCat.ofHom φ.hom) ≫ S.fromSpecResidueField s) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback pF (Spec.map (CommRingCat.ofHom φ.hom)))
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
  have sq2 : IsPullback (f'.fiberι s' ≫ g) (f'.fiberToSpecResidueField s') f
      (S'.fromSpecResidueField s' ≫ b) :=
    IsPullback.paste_horiz (IsPullback.of_hasPullback f' (S'.fromSpecResidueField s')) hg
  have hsq : Spec.map (CommRingCat.ofHom φ.hom) ≫ S.fromSpecResidueField s = S'.fromSpecResidueField s' ≫ b := by
    rw [CommRingCat.ofHom_hom]
    exact Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField b s'
  rw [hsq] at sq1
  let e := sq1.isoIsPullback _ _ sq2

  have hdim1 : topologicalKrullDim ↥(pullback pF (Spec.map (CommRingCat.ofHom φ.hom))) =
      topologicalKrullDim ↥(f'.fiber s') :=
    IsHomeomorph.topologicalKrullDim_eq (Scheme.homeoOfIso e) (Scheme.homeoOfIso e).isHomeomorph
  have hdim2 : topologicalKrullDim ↥(f'.fiber s') = topologicalKrullDim ↥(f'.base ⁻¹' {s'}) :=
    IsHomeomorph.topologicalKrullDim_eq (f'.fiberHomeo s') (f'.fiberHomeo s').isHomeomorph
  haveI : Subsingleton ↥(Spec (CommRingCat.of ↑(S'.residueField s'))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (S'.residueField s')))
  have hbc' : topologicalKrullDim ↥(pullback pF (Spec.map (CommRingCat.ofHom φ.hom))) = n :=
    (topologicalKrullDim_preimage_eq_of_subsingleton
      (pullback.snd pF (Spec.map (CommRingCat.ofHom φ.hom))).base _).symm.trans hbc
  rw [hdim0, ← hdim2, ← hdim1, hbc']

end S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected
end P2MW
export P2MW.S_AlgebraicGeometry_topologicalKrullDim_preimage_eq_of_isPullback_of_smooth_of_isConnected (solution)
