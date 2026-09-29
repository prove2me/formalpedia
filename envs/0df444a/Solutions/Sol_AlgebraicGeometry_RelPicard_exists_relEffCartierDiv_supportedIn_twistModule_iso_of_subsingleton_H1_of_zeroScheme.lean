-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/0acea932-b485-5bae-8152-9c2b31f5ec8c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Theorems.Thm_AlgebraicGeometry_RelPicard_isInvertible_sectionIdeal_of_range_subset
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_rigidify_pullback_tensor_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"

set_option autoImplicit false

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme.Modules.pullback Scheme.Hom LocallyOfFiniteType Spec Scheme IsSeparated Scheme.Modules.pullbackCongr Scheme.Opens.ι_apply Scheme.Modules Scheme.Opens Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.IdealSheafData.module Scheme.IdealSheafData.invModule RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp Scheme.TwoAffineOpenCover RelEffCartierDiv.twistModule_def Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso Scheme.Modules.zeroSchemeIdeal Scheme.Modules.tensorTensorTensorComm Scheme.Modules.pullbackTensorObjIso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "baseChangeSnd rigSection RigidifiedLineBundle fibreAt FibrewiseAlgEquivZero sectionIdeal sectionTwist fibreModule rigSection_snd RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified nonempty_pullback_sectionTwist_iso_of_range_subset isInvertible_sectionIdeal_of_range_subset"
namespace K5bExistSS
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra"

variable (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))

include hεU in

theorem isInvertible_sectionIdeal {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) :
    (sectionIdeal c ε u).IsInvertible :=
  isInvertible_sectionIdeal_of_range_subset c ε U hεU u

include hεU in

theorem isInvertible_sectionTwist {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R)) (n : ℕ) :
    Scheme.Modules.IsInvertible (sectionTwist c ε u n) :=
  ((isInvertible_sectionIdeal R c ε U hεU u).pow n).isInvertible_invModule

include hεU in

theorem nonempty_twistModule_iso
    {g e : ℕ} {V : Scheme.{u}} (u : V ⟶ Spec (CommRingCat.of R))
    (LU : RigidifiedLineBundle c ε u) (DγU : RelEffCartierDiv c e u) (hDγU : DγU.SupportedIn U)
    (D₀ : RelEffCartierDiv c g u) (hD₀U : D₀.SupportedIn U) (D : RelEffCartierDiv c (g + e) u) (hD : D.I = D₀.I * DγU.I)
    (N : V.Modules) (hN : Scheme.Modules.IsInvertible N)
    (e₀ : D₀.lineBundle ≅ (LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) :
    Nonempty (D.twistModule c ε ≅ LU.L) := by
  have hsIr : ((sectionIdeal c ε u) ^ (g + e)).IsInvertible := (isInvertible_sectionIdeal R c ε U hεU u).pow _
  have hD₀ : D₀.I.IsInvertible := D₀.isInvertible_I_of_supportedIn U hD₀U
  have hDγ : DγU.I.IsInvertible := DγU.isInvertible_I_of_supportedIn U hDγU

  have i1 : D.lineBundle ≅ D₀.lineBundle ⊗ DγU.lineBundle :=
    eqToIso (congrArg Scheme.IdealSheafData.invModule hD) ≪≫ (hD₀.nonempty_mul_invModule_iso_tensor hDγ).some

  have cST : sectionTwist c ε u (g + e) ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hsIr.isInvertible_module.dual).2.some
  have cγ : DγU.lineBundle ⊗ DγU.idealModule ≅ 𝟙_ _ :=
    (β_ _ _) ≪≫ (hDγ.isInvertible_module.dual).2.some

  have i3 : (((LU.L ⊗ (sectionTwist c ε u (g + e) ⊗ DγU.idealModule)) ⊗
      (Scheme.Modules.pullback (pullback.snd c u)).obj N) ⊗ DγU.lineBundle) ⊗
        ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    (α_ _ _ _) ≪≫ ((β_ _ _) ⊗ᵢ (β_ _ _)) ≪≫ (α_ _ _ _) ≪≫
      (Iso.refl _ ⊗ᵢ ((α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ
        (Scheme.Modules.tensorTensorTensorComm _ _ _ _ ≪≫ (cST ⊗ᵢ ((β_ _ _) ≪≫ cγ)) ≪≫ (λ_ _))) ≪≫ (ρ_ _)))
  have i4 : D.lineBundle ⊗ ((sectionIdeal c ε u) ^ (g + e)).module ≅
      (Scheme.Modules.pullback (pullback.snd c u)).obj N ⊗ LU.L :=
    ((i1 ≪≫ (e₀ ⊗ᵢ Iso.refl _)) ⊗ᵢ Iso.refl _) ≪≫ i3
  have i5 : Scheme.Modules.rigidify (rigSection c u ε) (pullback.snd c u) LU.L ≅ LU.L :=
    (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified LU).some
  rw [RelEffCartierDiv.twistModule_def]
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ i4 ≪≫
    (Scheme.Modules.IsInvertible.nonempty_rigidify_pullback_tensor_iso (rigSection_snd ε u) hN LU.isInvertible).some ≪≫
    i5⟩

include hεU in

theorem hfib_of_hU
    (r e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1)
    (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ (W : Scheme.{u}))
    (𝒲 : (pullback (pullback.snd c (W.ι ≫ t)) s).TwoAffineOpenCover) :
    Subsingleton (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
        ((L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L ⊗
          (sectionTwist c ε (W.ι ≫ t) r ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule)))).H1 ∧
      Module.finrank k (𝒲.sectionsOf (fibreAt c (W.ι ≫ t) s) (fibreModule c (W.ι ≫ t) s
        ((L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L ⊗
          (sectionTwist c ε (W.ι ≫ t) r ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule)))).H0 = 1 := by

  let ψ : SchemeHomOver (W.ι ≫ t) t := ⟨W.ι, rfl⟩
  set Mt : (pullback c t).Modules :=
    L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule) with hMt
  set Mu : (pullback c (W.ι ≫ t)).Modules := (L.pullbackAlong ψ).L ⊗
    (sectionTwist c ε (W.ι ≫ t) r ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule) with hMu
  have hβ : baseChangeSnd c ψ = pullback.lift (pullback.fst c (W.ι ≫ t) ≫ 𝟙 C) (pullback.snd c (W.ι ≫ t) ≫ W.ι)
      (by simp [pullback.condition]) := rfl

  have hcomp : (Dγ.pullbackAlong t (Category.comp_id t)).pullbackAlong W.ι ψ.2 =
      Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _) :=
    RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _
  have hI : (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I =
      (Dγ.pullbackAlong t (Category.comp_id t)).I.comap (baseChangeSnd c ψ) := by
    rw [← hcomp]; rfl
  have iγ : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (Dγ.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule := by
    haveI := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison (baseChangeSnd c ψ)
      ((Dγ.pullbackAlong t (Category.comp_id t)).isInvertible_I_of_supportedIn U (hDγ.pullbackAlong t _))
      (hI ▸ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).isInvertible_I_of_supportedIn U (hDγ.pullbackAlong _ _))
    exact asIso ((Dγ.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison (baseChangeSnd c ψ)) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm

  have iM : Mu ≅ (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj Mt :=
    (Iso.refl _ ⊗ᵢ ((nonempty_pullback_sectionTwist_iso_of_range_subset R c ε U hεU ψ r).some.symm ⊗ᵢ iγ.symm)) ≪≫
      (Iso.refl _ ⊗ᵢ (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) _ _).symm

  let φ : pullback (pullback.snd c t) (s ≫ W.ι) ≅ pullback (pullback.snd c (W.ι ≫ t)) s :=
    pullbackLeftPullbackSndIso c t (s ≫ W.ι) ≪≫ pullback.congrHom rfl (Category.assoc s W.ι t) ≪≫
      (pullbackLeftPullbackSndIso c (W.ι ≫ t) s).symm
  have hφsnd : φ.hom ≫ fibreAt c (W.ι ≫ t) s = fibreAt c t (s ≫ W.ι) := by
    simp only [φ, fibreAt, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, pullback.lift_snd,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  have hφfst : φ.hom ≫ pullback.fst (pullback.snd c (W.ι ≫ t)) s ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) (s ≫ W.ι) := by
    rw [hβ]
    apply pullback.hom_ext
    · simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullbackLeftPullbackSndIso_hom_fst]
    · simp only [φ, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        pullbackLeftPullbackSndIso_inv_fst_snd_assoc, pullback.congrHom_hom,
        Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]

  have eφ : fibreModule c t (s ≫ W.ι) Mt ≅ (Scheme.Modules.pullback φ.hom).obj (fibreModule c (W.ι ≫ t) s Mu) :=
    ((Scheme.Modules.pullbackCongr hφfst).app Mt).symm ≪≫
    ((Scheme.Modules.pullbackComp φ.hom
      (pullback.fst (pullback.snd c (W.ι ≫ t)) s ≫ baseChangeSnd c ψ)).app Mt).symm ≪≫
    (Scheme.Modules.pullback φ.hom).mapIso
      (((Scheme.Modules.pullbackComp (pullback.fst (pullback.snd c (W.ι ≫ t)) s) (baseChangeSnd c ψ)).app Mt).symm ≪≫
        (Scheme.Modules.pullback _).mapIso iM.symm)

  obtain ⟨𝒱, -, -, ⟨e0⟩, ⟨e1⟩⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
    (fibreAt c t (s ≫ W.ι)) (fibreAt c (W.ι ≫ t) s) φ hφsnd 𝒲 (fibreModule c (W.ι ≫ t) s Mu) (fibreModule c t (s ≫ W.ι) Mt) eφ
  have hrange : Set.range ⇑(s ≫ W.ι) ⊆ (W : Set T) := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
    exact (s x).2
  have h1 : Subsingleton (𝒱.sectionsOf (fibreAt c t (s ≫ W.ι)) (fibreModule c t (s ≫ W.ι) Mt)).H1 := hW k (s ≫ W.ι) hrange 𝒱
  haveI := h1
  refine ⟨e1.symm.toEquiv.subsingleton, ?_⟩
  rw [← hH0one t L hL k (s ≫ W.ι) 𝒱 h1]
  exact e0.symm.finrank_eq

include hεU in
theorem EXIST'
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)
    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)

    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)
    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) ∧
      D₀.SupportedIn U := by
  subst hr
  let ψ : SchemeHomOver (W.ι ≫ t) t := ⟨W.ι, rfl⟩

  have hfib := hfib_of_hU R c ε U hεU (g + e) e Dγ hDγ hH0one t L hL W hW

  have hM : Scheme.Modules.IsInvertible ((L.pullbackAlong ψ).L ⊗
      (sectionTwist c ε (W.ι ≫ t) (g + e) ⊗ (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).idealModule)) :=
    (L.pullbackAlong _).isInvertible.tensor ((isInvertible_sectionTwist R c ε U hεU (W.ι ≫ t) (g + e)).tensor
      ((Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).isInvertible_I_of_supportedIn U
        (hDγ.pullbackAlong _ _)).isInvertible_module)
  obtain ⟨D₀, N, hN, ⟨e₀⟩, -⟩ := hsect (W.ι ≫ t) _ hM hfib (hZfibγ (W.ι ≫ t) (L.pullbackAlong ψ) (hL.pullback ψ))

  have hD₀U : D₀.SupportedIn U := havoid (W.ι ≫ t) (L.pullbackAlong ψ) (hL.pullback ψ) D₀ N hN ⟨e₀⟩
  obtain ⟨D, hD, -⟩ := RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U D₀
    (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)) hD₀U (hDγ.pullbackAlong _ _)
  exact ⟨D, D₀, hD, nonempty_twistModule_iso R c ε U hεU (W.ι ≫ t) _ _ (hDγ.pullbackAlong _ _) D₀ hD₀U D hD N hN e₀, hD₀U⟩

end AlgebraicGeometry.RelPicard.K5bExistSS

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme.AlgebraicGeometry AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme.AlgebraicGeometry.RelPicard NeronModelInfra"

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)] (hεU : Set.range ε.1 ⊆ (U : Set C))
    (g e r : ℕ) (hr : g + e = r) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R)))) (hDγ : Dγ.SupportedIn U)

    (hsect : ∀ ⦃V : Scheme.{u}⦄ (u : V ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType u] (M : (pullback c u).Modules),
      Scheme.Modules.IsInvertible M →
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ V) (𝒲 : (pullback (pullback.snd c u) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H1 ∧
          Module.finrank k (𝒲.sectionsOf (fibreAt c u s) (fibreModule c u s M)).H0 = 1) →
      (∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ V)
        (σ : 𝟙_ (pullback c (x ≫ u)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj M), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ u), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U) →
      ∃ (D₀ : RelEffCartierDiv c g u) (N : V.Modules), Scheme.Modules.IsInvertible N ∧
        Nonempty (D₀.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N) ∧
        ∀ (d' : ℕ) (D' : RelEffCartierDiv c d' u) (N' : V.Modules), Scheme.Modules.IsInvertible N' → D'.SupportedIn U →
          Nonempty (D'.lineBundle ≅ M ⊗ (Scheme.Modules.pullback (pullback.snd c u)).obj N') → D'.I = D₀.I)

    (hZfibγ : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : Spec (CommRingCat.of k) ⟶ T)
        (σ : 𝟙_ (pullback c (x ≫ t)).Modules ⟶ (Scheme.Modules.pullback (mapOnProdOver c x rfl)).obj
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule))), σ ≠ 0 →
        ∃ Dx : RelEffCartierDiv c g (x ≫ t), Dx.I = Scheme.Modules.zeroSchemeIdeal σ ∧ Dx.SupportedIn U)

    (hH0one : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T) (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1 →
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H0 = 1)

    (havoid : ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
      (L : RigidifiedLineBundle c ε t), FibrewiseAlgEquivZero L →
      ∀ (D₀ : RelEffCartierDiv c g t) (N : T.Modules), Scheme.Modules.IsInvertible N →
        Nonempty (D₀.lineBundle ≅
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)) ⊗
            (Scheme.Modules.pullback (pullback.snd c t)).obj N) →
        D₀.SupportedIn U)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType t]
    (L : RigidifiedLineBundle c ε t) (hL : FibrewiseAlgEquivZero L) (W : T.Opens)
    (hW : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T), Set.range ⇑s ⊆ (W : Set T) →
      ∀ (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
        Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s
          (L.L ⊗ (sectionTwist c ε t r ⊗ (Dγ.pullbackAlong t (Category.comp_id t)).idealModule)))).H1) :
    ∃ (D : RelEffCartierDiv c r (W.ι ≫ t)) (D₀ : RelEffCartierDiv c g (W.ι ≫ t)),
      D.I = D₀.I * (Dγ.pullbackAlong (W.ι ≫ t) (Category.comp_id _)).I ∧
      Nonempty (D.twistModule c ε ≅ (L.pullbackAlong (⟨W.ι, rfl⟩ : SchemeHomOver (W.ι ≫ t) t)).L) ∧
      D₀.SupportedIn U :=
  AlgebraicGeometry.RelPicard.K5bExistSS.EXIST' R c ε U hεU g e r hr Dγ hDγ hsect hZfibγ hH0one havoid t L hL W hW

end S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_relEffCartierDiv_supportedIn_twistModule_iso_of_subsingleton_H1_of_zeroScheme (solution)
