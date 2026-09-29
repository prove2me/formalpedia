-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/ce4555c1-a31f-5ab7-b105-70f144fc32b2

import Mathlib
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_ModulesPushforwardRestrict
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_forall_exists_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_pullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pushforward Scheme.Modules.pullback IsAffineOpen.fromSpec_top isPullback_morphismRestrict IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec Spec.map Scheme Scheme.isoSpec_Spec_inv isAffineOpen_top IsAffineOpen Scheme.Modules Scheme.ΓSpecIso Scheme.Modules.IsLocallyFreeOfRank Scheme.TwoAffineOpenCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforward Modules.pullback mk Γ isoSpec_Spec_inv isoSpec Modules Opens ΓSpecIso Modules.IsLocallyFreeOfRank TwoAffineOpenCover"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "pushforwardCongr pushforward pushforwardComp pullback pushforwardId restrictFunctorIsoPullback pullbackCongr pullbackPushforwardAdjunction pullbackComp IsLocallyFreeOfRank pushforwardRestrictIso IsLocallyFreeOfRank.of_forall_exists_opens IsLocallyFreeOfRank.of_iso"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

section iso
variable {Y Y' : Scheme.{u}} (e : Y ≅ Y')

noncomputable def pushforwardIsoEquivalence : Y.Modules ≌ Y'.Modules :=
  CategoryTheory.Equivalence.mk (pushforward e.hom) (pushforward e.inv)
    ((pushforwardId Y).symm ≪≫ pushforwardCongr e.hom_inv_id.symm ≪≫ (pushforwardComp e.hom e.inv).symm)
    (pushforwardComp e.inv e.hom ≪≫ pushforwardCongr e.inv_hom_id ≪≫ pushforwardId Y')

noncomputable def pullbackIsoPushforwardInv : pullback e.hom ≅ pushforward e.inv :=
  (pullbackPushforwardAdjunction e.hom).leftAdjointUniq (pushforwardIsoEquivalence e).symm.toAdjunction

end iso

theorem isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback_aux
    {X T : Scheme.{u}} (π : X ⟶ T) (F : X.Modules) (n : ℕ)
    (h : ∀ y : T, ∃ (W : T.Opens), y ∈ W ∧ ∃ (W' X' : Scheme.{u}) (e : W' ≅ W.toScheme) (π' : X' ⟶ W')
      (g' : X' ⟶ X), IsPullback g' π' π (e.hom ≫ W.ι) ∧
        IsLocallyFreeOfRank n ((pushforward π').obj ((pullback g').obj F))) :
    IsLocallyFreeOfRank n ((pushforward π).obj F) := by
  apply IsLocallyFreeOfRank.of_forall_exists_opens
  intro y
  obtain ⟨W, hy, W', X', e, π', g', hcart₀, hLF⟩ := h y
  have hcart : IsPullback g' (π' ≫ e.hom) π W.ι :=
    hcart₀.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _) (by simp) (by simp) (by simp) (by simp)
  refine ⟨W, hy, ?_⟩

  have hres := isPullback_morphismRestrict π W
  let θ : X' ≅ (π ⁻¹ᵁ W).toScheme := IsPullback.isoIsPullback _ _ hcart hres.flip
  have hθ₁ : θ.hom ≫ (π ⁻¹ᵁ W).ι = g' := IsPullback.isoIsPullback_hom_fst _ _ hcart hres.flip
  have hθ₂ : θ.hom ≫ (π ∣_ W) = π' ≫ e.hom := IsPullback.isoIsPullback_hom_snd _ _ hcart hres.flip

  have h1 : IsLocallyFreeOfRank n ((pushforward (π' ≫ e.hom)).obj ((pullback g').obj F)) := by
    have := hLF.pullback e.inv
    refine IsLocallyFreeOfRank.of_iso ?_ this
    exact ((pullbackIsoPushforwardInv e.symm).app _) ≪≫ ((pushforwardComp π' e.hom).app _)

  have h2 : IsLocallyFreeOfRank n ((pushforward (π ∣_ W)).obj ((pullback (π ⁻¹ᵁ W).ι).obj F)) := by

    have h1' : IsLocallyFreeOfRank n
        ((pushforward (θ.hom ≫ (π ∣_ W))).obj ((pullback (θ.hom ≫ (π ⁻¹ᵁ W).ι)).obj F)) := by
      refine IsLocallyFreeOfRank.of_iso ?_ h1
      exact (pushforwardCongr hθ₂.symm).app _ ≪≫ (pushforward _).mapIso ((pullbackCongr hθ₁.symm).app _)
    refine IsLocallyFreeOfRank.of_iso ?_ h1'
    refine ((pushforwardComp θ.hom (π ∣_ W)).symm.app _) ≪≫ (pushforward (π ∣_ W)).mapIso ?_

    refine (pushforward θ.hom).mapIso ((pullbackComp θ.hom (π ⁻¹ᵁ W).ι).symm.app F) ≪≫ ?_

    haveI : (pullback θ.hom).IsEquivalence := by
      haveI : (pushforward θ.inv).IsEquivalence := (pushforwardIsoEquivalence θ.symm).isEquivalence_functor
      exact Functor.isEquivalence_of_iso (pullbackIsoPushforwardInv θ).symm
    exact (asIso ((pullbackPushforwardAdjunction θ.hom).unit.app ((pullback (π ⁻¹ᵁ W).ι).obj F))).symm

  refine IsLocallyFreeOfRank.of_iso ?_ h2
  exact (pushforward (π ∣_ W)).mapIso ((restrictFunctorIsoPullback (π ⁻¹ᵁ W).ι).symm.app F) ≪≫
    (pushforwardRestrictIso π W).app F ≪≫ (restrictFunctorIsoPullback W.ι).app _

theorem exists_iso_pullback_of_isPullback_aux
    {X T X' W' Z : Scheme.{u}} (π : X ⟶ T) (π' : X' ⟶ W') (g' : X' ⟶ X) (j : W' ⟶ T)
    (hcart : IsPullback g' π' π j) (s : Z ⟶ W') :
    ∃ φ : Limits.pullback π (s ≫ j) ≅ Limits.pullback π' s,
      φ.hom ≫ Limits.pullback.snd π' s = Limits.pullback.snd π (s ≫ j) ∧
      φ.hom ≫ Limits.pullback.fst π' s ≫ g' = Limits.pullback.fst π (s ≫ j) ∧
      ∀ G : X.Modules, Nonempty ((pullback (Limits.pullback.fst π (s ≫ j))).obj G ≅
        (pullback φ.hom).obj ((pullback (Limits.pullback.fst π' s)).obj ((pullback g').obj G))) := by

  have hbig : IsPullback (Limits.pullback.fst π' s ≫ g') (Limits.pullback.snd π' s) π (s ≫ j) :=
    (IsPullback.of_hasPullback π' s).paste_horiz hcart
  let φ : Limits.pullback π (s ≫ j) ≅ Limits.pullback π' s :=
    (IsPullback.of_hasPullback π (s ≫ j)).isoIsPullback _ _ hbig
  have hφ₁ : φ.hom ≫ Limits.pullback.fst π' s ≫ g' = Limits.pullback.fst π (s ≫ j) :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  have hφ₂ : φ.hom ≫ Limits.pullback.snd π' s = Limits.pullback.snd π (s ≫ j) :=
    IsPullback.isoIsPullback_hom_snd _ _ _ _
  refine ⟨φ, hφ₂, hφ₁, fun G => ⟨?_⟩⟩
  exact (pullbackCongr hφ₁.symm).app G ≪≫ (pullbackComp _ _).symm.app G ≪≫
    (pullback φ.hom).mapIso ((pullbackComp _ _).symm.app G)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pushforward Scheme.Modules.pullback IsAffineOpen.fromSpec_top isPullback_morphismRestrict IsAffineOpen.SpecMap_appLE_fromSpec LocallyOfFiniteType Spec Spec.map Scheme Scheme.isoSpec_Spec_inv isAffineOpen_top IsAffineOpen Scheme.Modules Scheme.ΓSpecIso Scheme.Modules.IsLocallyFreeOfRank Scheme.TwoAffineOpenCover"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pushforward Modules.pullback mk Γ isoSpec_Spec_inv isoSpec Modules Opens ΓSpecIso Modules.IsLocallyFreeOfRank TwoAffineOpenCover"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap algebraOfHom pullback mk"
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem exists_isPullback_snd_specMap_algebraOfHom_aux
    {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (.of R)) (t : T ⟶ Spec (.of R))
    (W : T.Opens) (hW : IsAffineOpen W) :
    letI := algebraOfHom t W
    ∃ g' : Limits.pullback c (specMap R Γ(T, W)) ⟶ Limits.pullback c t,
      IsPullback g' (Limits.pullback.snd c (specMap R Γ(T, W))) (Limits.pullback.snd c t) hW.fromSpec ∧
        g' ≫ Limits.pullback.fst c t = Limits.pullback.fst c (specMap R Γ(T, W)) := by
  letI := algebraOfHom t W

  have key : hW.fromSpec ≫ t = specMap R Γ(T, W) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec t (isAffineOpen_top _) hW (le_top (a := W))
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h

    change _ = Spec.map (CommRingCat.ofHom ((Scheme.ΓSpecIso (.of R)).inv ≫ t.appLE ⊤ W le_top).hom)
    rw [CommRingCat.ofHom_hom]
    exact h.symm
  let e₁ : Limits.pullback (Limits.pullback.snd c t) hW.fromSpec ≅ Limits.pullback c (specMap R Γ(T, W)) :=
    pullbackLeftPullbackSndIso c t hW.fromSpec ≪≫ Limits.pullback.congrHom rfl key
  have h1 : IsPullback (Limits.pullback.fst (Limits.pullback.snd c t) hW.fromSpec)
      (Limits.pullback.snd (Limits.pullback.snd c t) hW.fromSpec) (Limits.pullback.snd c t) hW.fromSpec :=
    IsPullback.of_hasPullback _ _
  refine ⟨e₁.inv ≫ Limits.pullback.fst (Limits.pullback.snd c t) hW.fromSpec, ?_, ?_⟩
  swap
  · rw [Category.assoc, Iso.inv_comp_eq]
    simp only [e₁, Iso.trans_hom, Category.assoc, Limits.pullback.congrHom_hom]
    delta CategoryTheory.Limits.pullback.map
    rw [Limits.pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  refine h1.of_iso e₁ (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  simp only [e₁, Iso.trans_hom, Iso.refl_hom, Category.comp_id, Category.assoc, Limits.pullback.congrHom_hom]
  delta CategoryTheory.Limits.pullback.map
  rw [Limits.pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

theorem finiteType_algebraOfHom_aux {R : Type u} [CommRing R] {T : Scheme.{u}} (t : T ⟶ Spec (.of R))
    [LocallyOfFiniteType t] (W : T.Opens) (hW : IsAffineOpen W) :
    letI := algebraOfHom t W
    Algebra.FiniteType R Γ(T, W) := by
  letI := algebraOfHom t W
  have h : (t.appLE ⊤ W le_top).hom.FiniteType :=
    t.finiteType_appLE (isAffineOpen_top _) hW le_top
  have h' : (Scheme.ΓSpecIso (.of R)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.surjective
  rw [← RingHom.finiteType_algebraMap]
  exact h.comp h'

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {X T : Scheme.{u}} (π : X ⟶ T) (F : X.Modules) (n : ℕ)
    (h : ∀ y : T, ∃ (W : T.Opens), y ∈ W ∧ ∃ (W' X' : Scheme.{u}) (e : W' ≅ W.toScheme) (π' : X' ⟶ W')
      (g' : X' ⟶ X), IsPullback g' π' π (e.hom ≫ W.ι) ∧
        Scheme.Modules.IsLocallyFreeOfRank n
          ((Scheme.Modules.pushforward π').obj ((Scheme.Modules.pullback g').obj F))) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) :=
  isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback_aux π F n h

#print axioms solution

end S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback (solution)
