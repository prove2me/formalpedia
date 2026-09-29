-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/fc38f652-4396-558e-8e2b-62faa8c1eb98

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelPicardStageHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry TensorProduct AlgebraicGeometry.Scheme.TwoAffineOpenCover P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.RelPicard.LFP"

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Spec Spec.map Scheme Scheme.Modules.Hom.app Scheme.Hom.preimage_mono Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules Scheme.Hom.comp_preimage Scheme.Modules.map_smul Scheme.Modules.pullbackComp Scheme.ΓSpecIso RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul forget ringCatSheaf Modules.pushforward Modules.pullback Hom.id_app Hom Hom.appLE_comp_appLE Γ Modules.Hom.comp_app Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.Hom.app Hom.preimage_mono Hom.opensRange_of_isIso Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.comp_preimage Modules.map_smul Modules.pullbackComp ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.baseChangeSnd_preimage_U0 TwoAffineOpenCover.baseChangeSnd_preimage_U1 TwoAffineOpenCover.baseChangeSnd_preimage_inf Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul pushforward pullback presheaf restrictAdjunction_unit_app_app Hom.comp_app Hom Hom.id_app Hom.app restrictAdjunction pullbackCongr Hom.isIso_iff_isIso_app pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv map_smul pullbackComp exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace StageTransport
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules"

section Comp

variable {X Y Z : Scheme.{u}} (κ : X ⟶ Y) (f : Y ⟶ Z)

theorem pullbackComp_unit_unit (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    (((pullbackComp κ f).hom.app M).app ((κ ≫ f) ⁻¹ᵁ U))
      ((((pullbackPushforwardAdjunction κ).unit.app ((pullback f).obj M)).app (f ⁻¹ᵁ U))
        ((((pullbackPushforwardAdjunction f).unit.app M).app U) m)) =
    (((pullbackPushforwardAdjunction (κ ≫ f)).unit.app M).app U) m := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction κ))
    (pullbackPushforwardAdjunction (κ ≫ f)) (pullbackComp κ f).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have h3 := congrArg (fun φ => Scheme.Modules.Hom.app φ U m) h
  change ((((pullbackPushforwardAdjunction κ).unit.app ((pullback f).obj M)).app (f ⁻¹ᵁ U))
      ((((pullbackPushforwardAdjunction f).unit.app M).app U) m)) =
    (((pullbackComp κ f).inv.app M).app ((κ ≫ f) ⁻¹ᵁ U))
      ((((pullbackPushforwardAdjunction (κ ≫ f)).unit.app M).app U) m) at h3
  rw [h3, ← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id_app, Hom.id_app]
  rfl

end Comp

section Congr

variable {X Y : Scheme.{u}} {p q : X ⟶ Y} (e : p = q)

theorem pullbackCongr_unit (M : Y.Modules) (U : Y.Opens) (W : X.Opens) (hp : W ≤ p ⁻¹ᵁ U) (hq : W ≤ q ⁻¹ᵁ U)
    (m : Γ(M, U)) :
    ((pullback q).obj M).presheaf.map (homOfLE hp).op
      ((((pullbackCongr e).hom.app M).app (p ⁻¹ᵁ U))
        ((((pullbackPushforwardAdjunction p).unit.app M).app U) m)) =
    ((pullback q).obj M).presheaf.map (homOfLE hq).op
      ((((pullbackPushforwardAdjunction q).unit.app M).app U) m) := by
  subst e
  rfl

end Congr

section IsoUnit

variable {X Y : Scheme.{u}} (κ : X ⟶ Y) [IsIso κ]

theorem isIso_unit_app_of_isIso (N : Y.Modules) : IsIso ((pullbackPushforwardAdjunction κ).unit.app N) := by
  rw [← Adjunction.unit_leftAdjointUniq_hom_app (restrictAdjunction κ) (pullbackPushforwardAdjunction κ) N]
  have : IsIso ((restrictAdjunction κ).unit.app N) := by
    refine Hom.isIso_iff_isIso_app.mpr fun U => ?_
    rw [restrictAdjunction_unit_app_app]
    have hU : κ ''ᵁ κ ⁻¹ᵁ U = U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_of_isIso, top_inf_eq]
    have hiso : IsIso (N.presheaf.map (eqToHom hU).op) := inferInstance
    rw [show homOfLE (κ.image_preimage_le U) = eqToHom hU from Subsingleton.elim _ _]
    exact hiso
  have h2 : IsIso ((pushforward κ).map
      (((restrictAdjunction κ).leftAdjointUniq (pullbackPushforwardAdjunction κ)).hom.app N)) :=
    ((pushforward κ).mapIso (((restrictAdjunction κ).leftAdjointUniq (pullbackPushforwardAdjunction κ)).app N)).isIso_hom
  exact IsIso.comp_isIso' this h2

end IsoUnit

section Scalars

variable {X Y : Scheme.{u}} (κ : X ⟶ Y)

theorem pushforward_smul (P : X.Modules) (V : Y.Opens) (s : Γ(Y, V)) (y : Γ((pushforward κ).obj P, V)) :
    s • y = (show Γ(P, κ ⁻¹ᵁ V) from (κ.app V).hom s • (show Γ(P, κ ⁻¹ᵁ V) from y)) := rfl

theorem appLE_algebraMap_eq' {A : Type u} [CommRing A] (q₀ : Y ⟶ Spec (.of A)) (q' : X ⟶ Spec (.of A))
    (hκ : κ ≫ q₀ = q') (V : Y.Opens) (W : X.Opens) (h : W ≤ κ ⁻¹ᵁ V) (a : A) :
    (κ.appLE V W h).hom (((Scheme.ΓSpecIso (.of A)).inv ≫ q₀.appLE ⊤ V le_top).hom a) =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ q'.appLE ⊤ W le_top).hom a := by
  subst hκ
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE]

end Scalars

end AlgebraicGeometry.Scheme.Modules.StageTransport

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Spec Spec.map Scheme Scheme.Modules.Hom.app Scheme.Hom.preimage_mono Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules Scheme.Hom.comp_preimage Scheme.Modules.map_smul Scheme.Modules.pullbackComp Scheme.ΓSpecIso RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul forget ringCatSheaf Modules.pushforward Modules.pullback Hom.id_app Hom Hom.appLE_comp_appLE Γ Modules.Hom.comp_app Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.Hom.app Hom.preimage_mono Hom.opensRange_of_isIso Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.comp_preimage Modules.map_smul Modules.pullbackComp ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.baseChangeSnd_preimage_U0 TwoAffineOpenCover.baseChangeSnd_preimage_U1 TwoAffineOpenCover.baseChangeSnd_preimage_inf Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul pushforward pullback presheaf restrictAdjunction_unit_app_app Hom.comp_app Hom Hom.id_app Hom.app restrictAdjunction pullbackCongr Hom.isIso_iff_isIso_app pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv map_smul pullbackComp exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace StageTransport
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem unit_app_map {X' X₀ : Scheme.{u}} (σ : X' ⟶ X₀) (M : X₀.Modules) {U V : X₀.Opens} (h : V ≤ U)
    (h' : σ ⁻¹ᵁ V ≤ σ ⁻¹ᵁ U) (m : Γ(M, U)) :
    (((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app V).hom (M.presheaf.map (homOfLE h).op m) =
      ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE h').op
        ((((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app U).hom m) := by
  have hn := ((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).mapPresheaf.naturality (homOfLE h).op
  have hx := ConcreteCategory.congr_hom hn m
  refine hx.trans ?_
  have : ((TopologicalSpace.Opens.map σ.base).map (homOfLE h)) = homOfLE h' := Subsingleton.elim _ _
  change (((Scheme.Modules.pullback σ).obj M).presheaf.map
    ((TopologicalSpace.Opens.map σ.base).map (homOfLE h)).op) _ = _
  rw [this]
  rfl

theorem tmul_eq_smul_one_tmul {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module R N]
    (a : A) (n : N) : a ⊗ₜ[R] n = a • ((1 : A) ⊗ₜ[R] n) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end AlgebraicGeometry.Scheme.Modules.StageTransport

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul Scheme.Modules.pushforward Scheme.Modules.pullback Scheme.Hom Scheme.Hom.appLE_comp_appLE Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme.Hom.image_preimage_eq_opensRange_inf Spec Spec.map Scheme Scheme.Modules.Hom.app Scheme.Hom.preimage_mono Scheme.Hom.opensRange_of_isIso Scheme.Modules.pullbackCongr Scheme.Modules.pullbackPushforwardAdjunction IsAffineOpen Scheme.Modules Scheme.Hom.comp_preimage Scheme.Modules.map_smul Scheme.Modules.pullbackComp Scheme.ΓSpecIso RelPicard.baseChangeSnd Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap RelPicard.LFP.stageHom Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul forget ringCatSheaf Modules.pushforward Modules.pullback Hom.id_app Hom Hom.appLE_comp_appLE Γ Modules.Hom.comp_app Hom.app Modules.Hom Hom.image_preimage_eq_opensRange_inf Modules.Hom.app Hom.preimage_mono Hom.opensRange_of_isIso Hom.comp_app Modules.pullbackCongr Modules.pullbackPushforwardAdjunction Modules Opens Hom.comp_preimage Modules.map_smul Modules.pullbackComp ΓSpecIso TwoAffineOpenCover TwoAffineOpenCover.specMap TwoAffineOpenCover.baseChangeSnd_preimage_U0 TwoAffineOpenCover.baseChangeSnd_preimage_U1 TwoAffineOpenCover.baseChangeSnd_preimage_inf Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial"
namespace TwoAffineOpenCover
p2m_export "AlgebraicGeometry.Scheme.TwoAffineOpenCover" "specMap cover pullback isAffineOpen_U0 isAffineOpen_inf U1 U0 isAffineOpen_U1 moduleSectionsOfHom sectionsOf baseChangeSnd_fst baseChangeSnd_preimage_U0 baseChangeSnd_preimage_U1 baseChangeSnd_preimage_inf"
namespace StageBC
p2m_open "AlgebraicGeometry.Scheme.TwoAffineOpenCover AlgebraicGeometry.Scheme AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial.AlgebraicGeometry.Scheme.Modules.StageTransport"

theorem exists_linearEquiv_transport
    {A' : Type u} [CommRing A'] {X' Z X₀ : Scheme.{u}} (κ : X' ⟶ Z) [IsIso κ] (fZ : Z ⟶ X₀) (σ : X' ⟶ X₀)
    (hκf : κ ≫ fZ = σ) (sZ : Z ⟶ Spec (.of A')) (snd' : X' ⟶ Spec (.of A')) (hκs : κ ≫ sZ = snd')
    (M : X₀.Modules) (U : X₀.Opens) (U' : X'.Opens) (hU' : U' = σ ⁻¹ᵁ U) :
    letI := moduleSectionsOfHom sZ ((Scheme.Modules.pullback fZ).obj M) (fZ ⁻¹ᵁ U)
    letI := moduleSectionsOfHom snd' ((Scheme.Modules.pullback σ).obj M) U'
    ∃ T : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U) ≃ₗ[A'] Γ((Scheme.Modules.pullback σ).obj M, U'),
      ∀ m : Γ(M, U), T ((((Scheme.Modules.pullbackPushforwardAdjunction fZ).unit.app M).app U).hom m) =
        ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hU'.le).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app U).hom m) := by
  letI := moduleSectionsOfHom sZ ((Scheme.Modules.pullback fZ).obj M) (fZ ⁻¹ᵁ U)
  letI := moduleSectionsOfHom snd' ((Scheme.Modules.pullback σ).obj M) U'

  let τ : (Scheme.Modules.pullback fZ).obj M ⟶
      (Scheme.Modules.pushforward κ).obj ((Scheme.Modules.pullback σ).obj M) :=
    (Scheme.Modules.pullbackPushforwardAdjunction κ).unit.app ((Scheme.Modules.pullback fZ).obj M) ≫
      (Scheme.Modules.pushforward κ).map
        ((Scheme.Modules.pullbackComp κ fZ).hom.app M ≫ (Scheme.Modules.pullbackCongr hκf).hom.app M)
  have hτ : IsIso τ := IsIso.comp_isIso' (isIso_unit_app_of_isIso κ _)
    (((Scheme.Modules.pushforward κ).mapIso
      ((Scheme.Modules.pullbackComp κ fZ).app M ≪≫ (Scheme.Modules.pullbackCongr hκf).app M)).isIso_hom)
  have hW' : U' = κ ⁻¹ᵁ (fZ ⁻¹ᵁ U) := by rw [hU', ← Scheme.Hom.comp_preimage, hκf]

  let T₀ : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U) →+ Γ((Scheme.Modules.pullback σ).obj M, U') :=
    (((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op).hom.comp (τ.app (fZ ⁻¹ᵁ U)).hom
  have hT₀ : Function.Bijective T₀ := by
    change Function.Bijective
      ((((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op).hom ∘ (τ.app (fZ ⁻¹ᵁ U)).hom)
    refine Function.Bijective.comp ?_ ?_
    · have hiso : IsIso (((Scheme.Modules.pullback σ).obj M).presheaf.map (eqToHom hW').op) := inferInstance
      rw [show homOfLE hW'.le = eqToHom hW' from Subsingleton.elim _ _]
      exact ((CategoryTheory.forget AddCommGrpCat).mapIso
        (asIso (((Scheme.Modules.pullback σ).obj M).presheaf.map (eqToHom hW').op))).toEquiv.bijective
    · haveI := hτ
      exact ((CategoryTheory.forget AddCommGrpCat).mapIso (asIso (τ.app (fZ ⁻¹ᵁ U)))).toEquiv.bijective

  have hT₀_smul : ∀ (a : A') (n : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U)), T₀ (a • n) = a • T₀ n := by
    intro a n
    change ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op
        ((τ.app (fZ ⁻¹ᵁ U)).hom ((((Scheme.ΓSpecIso (.of A')).inv ≫ sZ.appLE ⊤ (fZ ⁻¹ᵁ U) le_top).hom a) • n)) =
      (((Scheme.ΓSpecIso (.of A')).inv ≫ snd'.appLE ⊤ U' le_top).hom a) •
        ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op ((τ.app (fZ ⁻¹ᵁ U)).hom n)
    rw [← appLE_algebraMap_eq' κ sZ snd' hκs (fZ ⁻¹ᵁ U) U' hW'.le a]
    erw [Scheme.Modules.Hom.app_smul]
    rw [pushforward_smul, Scheme.Modules.map_smul]
    rfl
  let T : Γ((Scheme.Modules.pullback fZ).obj M, fZ ⁻¹ᵁ U) ≃ₗ[A'] Γ((Scheme.Modules.pullback σ).obj M, U') :=
    LinearEquiv.ofBijective
      { toFun := T₀, map_add' := T₀.map_add, map_smul' := hT₀_smul } hT₀
  refine ⟨T, fun m => ?_⟩
  change ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hW'.le).op
    ((((Scheme.Modules.pullbackComp κ fZ).hom.app M ≫ (Scheme.Modules.pullbackCongr hκf).hom.app M).app
      (κ ⁻¹ᵁ (fZ ⁻¹ᵁ U)))
      ((((Scheme.Modules.pullbackPushforwardAdjunction κ).unit.app ((Scheme.Modules.pullback fZ).obj M)).app
        (fZ ⁻¹ᵁ U)) ((((Scheme.Modules.pullbackPushforwardAdjunction fZ).unit.app M).app U) m))) = _
  rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [pullbackComp_unit_unit κ fZ M U m]
  exact pullbackCongr_unit hκf M U U' hW'.le hU'.le m

set_option maxHeartbeats 1600000 in

theorem isIso_lift_stage
    {R A₀ A' : Type u} [CommRing R] [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
    [IsScalarTower R A₀ A'] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
    (σ : Limits.pullback c (specMap R A') ⟶ Limits.pullback c (specMap R A₀))
    (hfst : σ ≫ Limits.pullback.fst c (specMap R A₀) = Limits.pullback.fst c (specMap R A'))
    (hsnd : σ ≫ Limits.pullback.snd c (specMap R A₀) = Limits.pullback.snd c (specMap R A') ≫ specMap A₀ A') :
    IsIso (Limits.pullback.lift σ (Limits.pullback.snd c (specMap R A')) hsnd) := by
  have htower : specMap A₀ A' ≫ specMap R A₀ = specMap R A' := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq R A₀ A']
  have w : (Limits.pullback.fst (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A') ≫
      Limits.pullback.fst c (specMap R A₀)) ≫ c =
      Limits.pullback.snd (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A') ≫ specMap R A' := by
    rw [Category.assoc, Limits.pullback.condition, Limits.pullback.condition_assoc, htower]
  refine ⟨⟨Limits.pullback.lift _ _ w, ?_, ?_⟩⟩
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc, hfst, Category.id_comp]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, Category.id_comp]
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst, Category.id_comp]
      apply Limits.pullback.hom_ext
      · rw [Category.assoc, hfst, Limits.pullback.lift_fst]
      · rw [Category.assoc, hsnd, Limits.pullback.lift_snd_assoc, Limits.pullback.condition]
    · rw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd, Category.id_comp]

theorem exists_linearEquiv_sections_stage
    {R A₀ A' : Type u} [CommRing R] [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A']
    [IsScalarTower R A₀ A'] {X : Scheme.{u}} (c : X ⟶ Spec (.of R))
    (σ : Limits.pullback c (specMap R A') ⟶ Limits.pullback c (specMap R A₀))
    (hfst : σ ≫ Limits.pullback.fst c (specMap R A₀) = Limits.pullback.fst c (specMap R A'))
    (hsnd : σ ≫ Limits.pullback.snd c (specMap R A₀) = Limits.pullback.snd c (specMap R A') ≫ specMap A₀ A')
    (M : (Limits.pullback c (specMap R A₀)).Modules)
    (htriv : ∀ x, ∃ (V : (Limits.pullback c (specMap R A₀)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : (Limits.pullback c (specMap R A₀)).Opens) (hU : IsAffineOpen U)
    (U' : (Limits.pullback c (specMap R A')).Opens) (hU' : U' = σ ⁻¹ᵁ U) :
    letI := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A₀)) M U
    letI := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A')) ((Scheme.Modules.pullback σ).obj M) U'
    ∃ e : A' ⊗[A₀] Γ(M, U) ≃ₗ[A'] Γ((Scheme.Modules.pullback σ).obj M, U'),
      ∀ m : Γ(M, U), e ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback σ).obj M).presheaf.map (homOfLE hU'.le).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction σ).unit.app M).app U).hom m) := by
  letI := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A₀)) M U
  letI := moduleSectionsOfHom (Limits.pullback.snd c (specMap R A')) ((Scheme.Modules.pullback σ).obj M) U'
  haveI := isIso_lift_stage c σ hfst hsnd
  obtain ⟨eZ, heZ⟩ := Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    (Limits.pullback.snd c (specMap R A₀)) M htriv U hU A'
  obtain ⟨T, hT⟩ := exists_linearEquiv_transport (Limits.pullback.lift σ (Limits.pullback.snd c (specMap R A')) hsnd)
    (Limits.pullback.fst (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A')) σ (Limits.pullback.lift_fst _ _ _)
    (Limits.pullback.snd (Limits.pullback.snd c (specMap R A₀)) (specMap A₀ A')) (Limits.pullback.snd c (specMap R A'))
    (Limits.pullback.lift_snd _ _ _) M U U' hU'
  exact ⟨eZ.trans T, fun m => by rw [LinearEquiv.trans_apply, heZ, hT]⟩

end AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC

set_option maxHeartbeats 6400000 in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (.of R))
    (A₀ A' : Type u) [CommRing A₀] [CommRing A'] [Algebra R A₀] [Algebra R A'] [Algebra A₀ A'] [IsScalarTower R A₀ A']
    (M : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Modules)
    (htriv : ∀ x, ∃ (V : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A₀)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf)) :
    ∃ (e0 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M0 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M0)
      (e1 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M1 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M1)
      (e01 : A' ⊗[A₀] ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M01 ≃ₗ[A']
          ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).M01),
      (∀ x, e01 ((((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).r0.baseChange A') x) =
        ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).r0 (e0 x)) ∧
      (∀ x, e01 ((((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).r1.baseChange A') x) =
        ((𝒱.pullback c A').sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))
            ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M)).r1 (e1 x)) ∧
      (∀ m, e0 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U0)).hom m)) ∧
      (∀ m, e1 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U1)).hom m)) ∧
      (∀ m, e01 ((1 : A') ⊗ₜ[A₀] m) =
        ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M).presheaf.map
          (homOfLE (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction (RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A')))).unit.app M).app
            ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)).hom m)) ∧

      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A0)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M0),
        e0 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A0 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U0)
              ((𝒱.pullback c A').U0) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U0 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e0 ((1 : A') ⊗ₜ[A₀] m)) ∧
      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A1)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M1),
        e1 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A1 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE ((𝒱.pullback c A₀).U1)
              ((𝒱.pullback c A').U1) (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_U1 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e1 ((1 : A') ⊗ₜ[A₀] m)) ∧
      (∀ (s : ((𝒱.pullback c A₀).cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀))).A01)
          (m : ((𝒱.pullback c A₀).sectionsOf (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A₀)) M).M01),
        e01 ((1 : A') ⊗ₜ[A₀] (s • m)) =
          (show ((𝒱.pullback c A').cover (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A'))).A01 from
            ((RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).appLE
              ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1)
              (Scheme.TwoAffineOpenCover.baseChangeSnd_preimage_inf 𝒱 c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A₀ A'))).ge).hom s) •
            e01 ((1 : A') ⊗ₜ[A₀] m)) := by
  have hfst : RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')) ≫
      Limits.pullback.fst c (specMap R A₀) = Limits.pullback.fst c (specMap R A') :=
    baseChangeSnd_fst c _
  have hsnd : RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')) ≫
      Limits.pullback.snd c (specMap R A₀) = Limits.pullback.snd c (specMap R A') ≫ specMap A₀ A' :=
    Limits.pullback.lift_snd _ _ _
  obtain ⟨e0, he0⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC.exists_linearEquiv_sections_stage c _ hfst hsnd M htriv
    (𝒱.pullback c A₀).U0 (𝒱.pullback c A₀).isAffineOpen_U0 (𝒱.pullback c A').U0
    (baseChangeSnd_preimage_U0 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))).symm
  obtain ⟨e1, he1⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC.exists_linearEquiv_sections_stage c _ hfst hsnd M htriv
    (𝒱.pullback c A₀).U1 (𝒱.pullback c A₀).isAffineOpen_U1 (𝒱.pullback c A').U1
    (baseChangeSnd_preimage_U1 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))).symm
  obtain ⟨e01, he01⟩ := AlgebraicGeometry.Scheme.TwoAffineOpenCover.StageBC.exists_linearEquiv_sections_stage c _ hfst hsnd M htriv
    ((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1) (𝒱.pullback c A₀).isAffineOpen_inf
    ((𝒱.pullback c A').U0 ⊓ (𝒱.pullback c A').U1)
    (baseChangeSnd_preimage_inf 𝒱 c (stageHom R (IsScalarTower.toAlgHom R A₀ A'))).symm
  refine ⟨e0, e1, e01, ?_, ?_, he0, he1, he01, ?_, ?_, ?_⟩
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, Scheme.Modules.StageTransport.tmul_eq_smul_one_tmul a,
        Scheme.Modules.StageTransport.tmul_eq_smul_one_tmul a m, map_smul, map_smul, map_smul]
      congr 1
      erw [he0, he01]
      erw [Scheme.Modules.StageTransport.unit_app_map _ M inf_le_left
        (Scheme.Hom.preimage_mono _ inf_le_left) m]
      change (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback _).obj M).presheaf.map _) _ =
        (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback _).obj M).presheaf.map _) _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
  · intro x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a m =>
      rw [LinearMap.baseChange_tmul, Scheme.Modules.StageTransport.tmul_eq_smul_one_tmul a,
        Scheme.Modules.StageTransport.tmul_eq_smul_one_tmul a m, map_smul, map_smul, map_smul]
      congr 1
      erw [he1, he01]
      erw [Scheme.Modules.StageTransport.unit_app_map _ M inf_le_right
        (Scheme.Hom.preimage_mono _ inf_le_right) m]
      change (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback _).obj M).presheaf.map _) _ =
        (((Scheme.Modules.pullback _).obj M).presheaf.map _ ≫ ((Scheme.Modules.pullback _).obj M).presheaf.map _) _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
  · intro s m
    erw [he0, he0, Scheme.Modules.Hom.app_smul]
    erw [Scheme.Modules.StageTransport.pushforward_smul (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M) ((𝒱.pullback c A₀).U0) s]
    rw [Scheme.Modules.map_smul]
    rfl
  · intro s m
    erw [he1, he1, Scheme.Modules.Hom.app_smul]
    erw [Scheme.Modules.StageTransport.pushforward_smul (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M) ((𝒱.pullback c A₀).U1) s]
    rw [Scheme.Modules.map_smul]
    rfl
  · intro s m
    erw [he01, he01, Scheme.Modules.Hom.app_smul]
    erw [Scheme.Modules.StageTransport.pushforward_smul (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))
      ((Scheme.Modules.pullback (RelPicard.baseChangeSnd c (stageHom R (IsScalarTower.toAlgHom R A₀ A')))).obj M) (((𝒱.pullback c A₀).U0 ⊓ (𝒱.pullback c A₀).U1)) s]
    rw [Scheme.Modules.map_smul]
    rfl

end

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_stage_sectionsOf_baseChange_equiv_of_locallyTrivial (solution)
