-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/7623b4b6-ec67-5110-a53b-ae735b031cb3

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

universe u

open TopologicalSpace Opposite

namespace PiSpecCover

variable {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]

noncomputable def θ : (∀ i, C i) ≃+* (∀ j : ULift.{u} (Fin k), C j.down) :=
  RingEquiv.piCongrLeft' C Equiv.ulift.symm

theorem eval_comp_θ (i : Fin k) :
    (Pi.evalRingHom (fun j : ULift.{u} (Fin k) => C j.down) (ULift.up i)).comp (θ C).toRingHom = Pi.evalRingHom C i := by
  ext f; rfl

theorem specMap_eval (i : Fin k) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) =
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j : ULift.{u} (Fin k) => C j.down) (ULift.up i))) ≫
        Spec.map (CommRingCat.ofHom (θ C).toRingHom) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, eval_comp_θ]

scoped instance : IsIso (Spec.map (CommRingCat.ofHom (θ C).toRingHom)) := by
  change IsIso (Scheme.Spec.map (Quiver.Hom.op (θ C).toCommRingCatIso.hom))
  infer_instance

theorem exists_eval_eq (s : ↥(Spec (CommRingCat.of (∀ i, C i)))) :
    ∃ (i : Fin k) (y : ↥(Spec (CommRingCat.of (C i)))), Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i)) y = s := by
  let Rf : ULift.{u} (Fin k) → CommRingCat.{u} := fun j => CommRingCat.of (C j.down)
  let Θ := Spec.map (CommRingCat.ofHom (θ C).toRingHom)
  obtain ⟨⟨j, y⟩, hy⟩ := (sigmaMk (fun j => Spec (Rf j))).surjective (inv (sigmaSpec Rf) (inv Θ s))
  refine ⟨j.down, y, ?_⟩
  rw [sigmaMk_mk] at hy
  have e := congrArg (fun φ => φ y) (ι_sigmaSpec Rf j)
  simp only [Scheme.Hom.comp_apply] at e
  rw [specMap_eval, Scheme.Hom.comp_apply]
  change Θ ((Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun j => ↑(Rf j)) j))) y) = s
  have h1 : ∀ x, (sigmaSpec Rf) ((inv (sigmaSpec Rf)) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  have h2 : ∀ x, Θ ((inv Θ) x) = x := fun x => by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl
  rw [← e, hy]
  change Θ ((sigmaSpec Rf) ((inv (sigmaSpec Rf)) ((inv Θ) s))) = s
  rw [h1, h2]

theorem isEmpty_of_comp_eval_eq {i₁ i₂ : Fin k} (h : i₁ ≠ i₂) {Z : Scheme.{u}}
    (a : Z ⟶ Spec (CommRingCat.of (C i₁))) (b : Z ⟶ Spec (CommRingCat.of (C i₂)))
    (hab : a ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i₁)) = b ≫ Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i₂))) :
    IsEmpty ↥Z := by
  let Rf : ULift.{u} (Fin k) → CommRingCat.{u} := fun j => CommRingCat.of (C j.down)
  rw [specMap_eval C i₁, specMap_eval C i₂, ← Category.assoc, ← Category.assoc, cancel_mono] at hab
  have hab' : (a ≫ Sigma.ι (fun j => Spec (Rf j)) (ULift.up i₁)) ≫ sigmaSpec Rf =
      (b ≫ Sigma.ι (fun j => Spec (Rf j)) (ULift.up i₂)) ≫ sigmaSpec Rf := by
    rw [Category.assoc, Category.assoc, ι_sigmaSpec, ι_sigmaSpec]; exact hab
  rw [cancel_mono] at hab'
  exact isEmpty_of_commSq_sigmaι_of_ne ⟨hab'⟩ (fun e => h (congrArg ULift.down e))

end PiSpecCover
p2m_reactivate "P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ.PiSpecCover"

theorem solution
    {k : ℕ} (C : Fin k → Type u) [∀ i, CommRing (C i)]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i))) (M M' : X.Modules)
    {Xi : Fin k → Scheme.{u}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (h : ∀ i, LocIsoOnBase (gi i) ((Scheme.Modules.pullback (v i)).obj M) ((Scheme.Modules.pullback (v i)).obj M')) :
    LocIsoOnBase g M M' := by
  classical
  intro s

  let σ : ∀ i, Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) := fun i =>
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))
  haveI hσ : ∀ i, IsOpenImmersion (σ i) := fun i =>
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (C ·) i))))
  obtain ⟨i, y, hy⟩ := PiSpecCover.exists_eval_eq C s

  obtain ⟨Ui, hyU, ⟨ei⟩⟩ := h i y
  let U : (Spec (CommRingCat.of (∀ i, C i))).Opens :=
    ⟨σ i '' (Ui : Set _), (σ i).isOpenEmbedding.isOpenMap _ Ui.isOpen⟩
  refine ⟨U, ⟨y, hyU, hy⟩, ?_⟩

  haveI : IsOpenImmersion (v i) := by
    rw [← (hv i).isoPullback_hom_fst]; infer_instance
  have hsq : ∀ w, σ i (gi i w) = g (v i w) := fun w => by
    have := congrArg (fun φ => φ w) (hv i).w
    simp only [Scheme.Hom.comp_apply] at this
    exact this.symm

  have hrange : Set.range (g ⁻¹ᵁ U).ι = Set.range (((gi i) ⁻¹ᵁ Ui).ι ≫ v i) := by
    ext x
    rw [Scheme.Opens.range_ι]
    constructor
    · rintro ⟨u, hu, hux⟩
      have hx : x ∈ Set.range (pullback.fst g (σ i)) := by
        rw [Scheme.Pullback.range_fst]; exact ⟨u, hux⟩
      obtain ⟨p, rfl⟩ := hx
      have hw : v i ((hv i).isoPullback.inv p) = pullback.fst g (σ i) p := by
        rw [← Scheme.Hom.comp_apply, (hv i).isoPullback_inv_fst]
      refine ⟨⟨(hv i).isoPullback.inv p, ?_⟩, ?_⟩
      · change gi i ((hv i).isoPullback.inv p) ∈ (Ui : Set _)
        have h1 := hsq ((hv i).isoPullback.inv p)
        rw [hw, ← hux] at h1
        rwa [(σ i).isOpenEmbedding.injective h1]
      · rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
        exact hw
    · rintro ⟨⟨w, hw⟩, rfl⟩
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
      exact ⟨gi i w, hw, hsq w⟩
  let φ := IsOpenImmersion.isoOfRangeEq (g ⁻¹ᵁ U).ι (((gi i) ⁻¹ᵁ Ui).ι ≫ v i) hrange
  have hfac : φ.hom ≫ ((gi i) ⁻¹ᵁ Ui).ι ≫ v i = (g ⁻¹ᵁ U).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

  exact ⟨(Scheme.Modules.pullbackCongr hfac.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp φ.hom (((gi i) ⁻¹ᵁ Ui).ι ≫ v i)).app M).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso
      (((Scheme.Modules.pullbackComp ((gi i) ⁻¹ᵁ Ui).ι (v i)).app M).symm ≪≫ ei ≪≫
        (Scheme.Modules.pullbackComp ((gi i) ⁻¹ᵁ Ui).ι (v i)).app M') ≪≫
    (Scheme.Modules.pullbackComp φ.hom (((gi i) ⁻¹ᵁ Ui).ι ≫ v i)).app M' ≪≫
    (Scheme.Modules.pullbackCongr hfac).app M'⟩

end S_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi_univ (solution)
