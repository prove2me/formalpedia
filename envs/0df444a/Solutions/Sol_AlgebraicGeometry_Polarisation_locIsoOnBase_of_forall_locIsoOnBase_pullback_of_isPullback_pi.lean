-- Prove2me | solution 1 for AlgebraicGeometry.Polarisation.locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/17028cd2-d6b4-530e-9412-dea94126f1b3

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

namespace P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.Polarisation"

theorem solution
    {k : ℕ} (C : Fin k → Type) [∀ i, CommRing (C i)]
    {X : Scheme.{0}} (g : X ⟶ Spec (CommRingCat.of (∀ i, C i))) (M M' : X.Modules)
    {Xi : Fin k → Scheme.{0}} (gi : ∀ i, Xi i ⟶ Spec (CommRingCat.of (C i))) (v : ∀ i, Xi i ⟶ X)
    (hv : ∀ i, IsPullback (v i) (gi i) g (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))))
    (h : ∀ i, LocIsoOnBase (gi i) ((Scheme.Modules.pullback (v i)).obj M) ((Scheme.Modules.pullback (v i)).obj M')) :
    LocIsoOnBase g M M' := by
  classical
  intro s

  let σ : ∀ i, Spec (CommRingCat.of (C i)) ⟶ Spec (CommRingCat.of (∀ i, C i)) := fun i =>
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom C i))
  haveI hσ : ∀ i, IsOpenImmersion (σ i) := fun i =>
    (inferInstance : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (C ·) i))))
  obtain ⟨i, y, hy⟩ : ∃ (i : Fin k) (y : ↥(Spec (CommRingCat.of (C i)))), σ i y = s := by
    let Rf : Fin k → CommRingCat.{0} := fun i => CommRingCat.of (C i)
    obtain ⟨⟨j, x⟩, hx⟩ := (sigmaMk (fun i => Spec (Rf i))).surjective (inv (sigmaSpec Rf) s)
    refine ⟨j, x, ?_⟩
    rw [sigmaMk_mk] at hx
    have e := congrArg (fun φ => φ x) (ι_sigmaSpec Rf j)
    simp only [Scheme.Hom.comp_apply] at e
    change (Spec.map (CommRingCat.ofHom (Pi.evalRingHom C j))) x = s
    rw [← e, hx, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl

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

end S_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi
end P2MW
export P2MW.S_AlgebraicGeometry_Polarisation_locIsoOnBase_of_forall_locIsoOnBase_pullback_of_isPullback_pi (solution)
