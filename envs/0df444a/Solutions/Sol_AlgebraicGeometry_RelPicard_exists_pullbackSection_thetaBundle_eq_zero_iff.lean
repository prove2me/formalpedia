-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.exists_pullbackSection_thetaBundle_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/36431050-9bea-5718-8fa6-5c49948e8395

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_RelCartier
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_of_forall_fibre
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_baseChangeHom_comp_vertical
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullbackSection_dual_det_eq_zero_iff_not_isIso
import Theorems.Thm_AlgebraicGeometry_RelPicard_isPullback_baseChangeSnd
import Theorems.Thm_AlgebraicGeometry_RelPicard_isIso_baseChangeHom_pushforward_of_forall_fibre
import Theorems.Thm_AlgebraicGeometry_RelPicard_isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso
import Theorems.Thm_AlgebraicGeometry_finrank_sections_pushforward_thickening_and_injective_unit_app_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_exists_pullbackSection_thetaBundle_eq_zero_iff
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply exteriorPower.mulₗ_apply_coe AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory AlgebraicGeometry.SmoothProperCurve"

namespace ThetaLocusAux

scoped instance smoothOfRelativeDimension_one_snd {R : Type u} [CommRing R] {C T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension 1 c] :
    SmoothOfRelativeDimension 1 (pullback.snd c t) :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

theorem rigSection_snd {R : Type u} [CommRing R] {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    rigSection c t ε ≫ pullback.snd c t = 𝟙 T :=
  pullback.lift_snd _ _ _

scoped instance isClosedImmersion_rigSection {R : Type u} [CommRing R] {C T : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (t : T ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) [IsSeparated c] :
    IsClosedImmersion (rigSection c t ε) := by
  haveI : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
    rw [rigSection_snd]; infer_instance
  exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)

theorem isPullback_rigSection {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ψ : SchemeHomOver t' t) :
    IsPullback (rigSection c t' ε) ψ.1 (baseChangeSnd c ψ) (rigSection c t ε) := by
  have hbig : IsPullback (rigSection c t' ε ≫ pullback.snd c t') ψ.1 ψ.1 (rigSection c t ε ≫ pullback.snd c t) := by
    rw [rigSection_snd, rigSection_snd]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  exact hbig.of_right (rigSection_baseChangeSnd c ε ψ) (isPullback_baseChangeSnd c ψ).flip

theorem isInvertible_tensor_sectionTwist (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r : ℕ) :
    Scheme.Modules.IsInvertible (M.L ⊗ sectionTwist c ε t r) := by
  have h𝓘 : (sectionIdeal c ε t).IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) (rigSection c t ε) (rigSection_snd c t ε)
  exact M.isInvertible.tensor (Scheme.IdealSheafData.IsInvertible.isInvertible_invModule (h𝓘.pow r))

theorem comap_top {X Y : Scheme.{u}} (f : X ⟶ Y) : (⊤ : Y.IdealSheafData).comap f = ⊤ := by
  haveI : IsEmpty (⊤ : Y.IdealSheafData).subscheme := by
    rw [← (Scheme.Hom.ker_eq_top_iff_isEmpty (⊤ : Y.IdealSheafData).subschemeι)]
    exact Scheme.IdealSheafData.ker_subschemeι _
  haveI : IsEmpty ↥(pullback f (⊤ : Y.IdealSheafData).subschemeι) :=
    Function.isEmpty (pullback.snd f (⊤ : Y.IdealSheafData).subschemeι).base
  exact Scheme.ker_eq_top_of_isEmpty _

theorem comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = I.comap f ^ n := by
  induction n with
  | zero => (have h__af := comap_top f; simp only [pow_zero, Ideal.one_eq_top] at h__af ⊢; exact h__af)
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

theorem comap_sectionIdeal_baseChangeSnd {R : Type u} [CommRing R] {C T T' : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (ψ : SchemeHomOver t' t) :
    (sectionIdeal c ε t).comap (baseChangeSnd c ψ) = (rigSection c t' ε).ker := by
  have H := isPullback_rigSection c ε ψ
  unfold sectionIdeal
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

theorem comap_pow_sectionIdeal_baseChangeSnd (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    ((sectionIdeal c ε t) ^ n).comap (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t)) = ((rigSection c (s ≫ t) ε).ker) ^ n := by
  rw [comap_pow, comap_sectionIdeal_baseChangeSnd]

noncomputable def thickeningMap (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    (((rigSection c (s ≫ t) ε).ker) ^ n).subscheme ⟶ ((sectionIdeal c ε t) ^ n).subscheme :=
  IsClosedImmersion.lift ((sectionIdeal c ε t) ^ n).subschemeι ((((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι ≫ (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))) (by
    rw [Scheme.IdealSheafData.ker_subschemeι]
    refine (Scheme.IdealSheafData.le_map_iff_comap_le).2 ?_
    rw [comap_pow_sectionIdeal_baseChangeSnd])

theorem thickeningMap_comp (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    thickeningMap k c ε t n K s ≫ ((sectionIdeal c ε t) ^ n).subschemeι = (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι ≫ (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t)) :=
  IsClosedImmersion.lift_fac _ _ _

theorem isPullback_thickeningMap (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (n : ℕ) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    IsPullback (thickeningMap k c ε t n K s) (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι ((sectionIdeal c ε t) ^ n).subschemeι (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t)) := by
  have h := AlgebraicGeometry.isPullback_of_isClosedImmersion (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι ((sectionIdeal c ε t) ^ n).subschemeι
    (thickeningMap k c ε t n K s) (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t)) (thickeningMap_comp k c ε t n K s).symm (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
        comap_pow_sectionIdeal_baseChangeSnd])
  exact h.flip

theorem isIso_pullback_map_ev_iff (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) (r n : ℕ) (hfib : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank K (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    IsIso ((Scheme.Modules.pullback s).map ((Scheme.Modules.pushforward (pullback.snd c t)).map ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))) ↔
      IsIso ((Scheme.Modules.pushforward (pullback.snd c (s ≫ t))).map
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))) := by
  have hG := isInvertible_tensor_sectionTwist k c ε M r
  have hbot := isPullback_baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t)
  have htop := isPullback_thickeningMap k c ε t n K s
  have hpaste := htop.paste_vert hbot

  have hβG : IsIso (Scheme.Modules.baseChangeHom hbot.w (M.L ⊗ sectionTwist c ε t r)) :=
    RelPicard.isIso_baseChangeHom_pushforward_of_forall_fibre k c ε h𝔉 (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) _ hG n hfib

  obtain ⟨hfin, -, -, -⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
    (p := pullback.snd c t) (rigSection c t ε) (rigSection_snd c t ε) n
  haveI : IsFinite (((sectionIdeal c ε t) ^ n).subschemeι ≫ pullback.snd c t) := hfin
  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)) := hG.pullback _
  have hβq := Scheme.Modules.isIso_baseChangeHom_of_isAffineHom hpaste _ hN.exists_trivialization
  have hβi := Scheme.Modules.isIso_baseChangeHom_of_isAffineHom htop _ hN.exists_trivialization
  have hvert := Scheme.Modules.baseChangeHom_comp_vertical htop.w hbot.w hpaste.w
    ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))
  have hβF : IsIso (Scheme.Modules.baseChangeHom hbot.w
      ((Scheme.Modules.pushforward ((sectionIdeal c ε t) ^ n).subschemeι).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)))) := by
    rw [hvert] at hβq
    haveI := hβq
    haveI : IsIso (Scheme.Modules.baseChangeHom htop.w ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))) := hβi
    haveI hd : @IsIso _ _ ((Scheme.Modules.pushforward (pullback.snd c (s ≫ t))).obj
        ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).obj ((Scheme.Modules.pullback (thickeningMap k c ε t n K s)).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))))) _
        ((Scheme.Modules.pushforwardComp (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι (pullback.snd c (s ≫ t))).hom.app ((Scheme.Modules.pullback (thickeningMap k c ε t n K s)).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)))) :=
      NatIso.hom_app_isIso _ _
    haveI : IsIso ((Scheme.Modules.pushforward (pullback.snd c (s ≫ t))).map (Scheme.Modules.baseChangeHom htop.w ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))) ≫
      (Scheme.Modules.pushforwardComp (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι (pullback.snd c (s ≫ t))).hom.app ((Scheme.Modules.pullback (thickeningMap k c ε t n K s)).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)))) := IsIso.comp_isIso
    have hbcd : IsIso ((Scheme.Modules.baseChangeHom hbot.w ((Scheme.Modules.pushforward ((sectionIdeal c ε t) ^ n).subschemeι).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)))) ≫
      ((Scheme.Modules.pushforward (pullback.snd c (s ≫ t))).map (Scheme.Modules.baseChangeHom htop.w ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))) ≫
      (Scheme.Modules.pushforwardComp (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι (pullback.snd c (s ≫ t))).hom.app ((Scheme.Modules.pullback (thickeningMap k c ε t n K s)).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))))) :=
      (isIso_comp_left_iff ((Scheme.Modules.pullback s).map
      ((Scheme.Modules.pushforwardComp ((sectionIdeal c ε t) ^ n).subschemeι (pullback.snd c t)).inv.app ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)))) _).1 hβq
    exact (isIso_comp_right_iff (Scheme.Modules.baseChangeHom hbot.w ((Scheme.Modules.pushforward ((sectionIdeal c ε t) ^ n).subschemeι).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))))
      ((Scheme.Modules.pushforward (pullback.snd c (s ≫ t))).map (Scheme.Modules.baseChangeHom htop.w ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))) ≫
      (Scheme.Modules.pushforwardComp (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι (pullback.snd c (s ≫ t))).hom.app ((Scheme.Modules.pullback (thickeningMap k c ε t n K s)).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))))).1 hbcd

  have hnat := Scheme.Modules.baseChangeHom_naturality hbot.w ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r))
  haveI : IsIso (Scheme.Modules.baseChangeHom hbot.w ((𝟭 _).obj (M.L ⊗ sectionTwist c ε t r))) := hβG
  haveI : IsIso (Scheme.Modules.baseChangeHom hbot.w
      ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι ⋙ Scheme.Modules.pushforward ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))) := hβF
  calc IsIso ((Scheme.Modules.pullback s).map ((Scheme.Modules.pushforward (pullback.snd c t)).map ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r))))
      ↔ IsIso ((Scheme.Modules.pullback s).map ((Scheme.Modules.pushforward (pullback.snd c t)).map ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r))) ≫ Scheme.Modules.baseChangeHom hbot.w _) :=
        (isIso_comp_right_iff _ _).symm
    _ ↔ IsIso (Scheme.Modules.baseChangeHom hbot.w _ ≫ (Scheme.Modules.pushforward (pullback.snd c (s ≫ t))).map
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).map ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))) := by
        rw [hnat]
    _ ↔ _ := isIso_comp_left_iff _ _

theorem sections_eq_of_eq_bot {X : Scheme.{u}} (M : X.Modules) {W : X.Opens} (hW : W = ⊥)
    (s t : Γ(M, W)) : s = t := by
  subst hW
  let F : TopCat.Sheaf Ab X.carrier := ⟨M.presheaf, M.isSheaf⟩
  exact F.eq_of_locally_eq' (fun i : Empty => i.elim) ⊥ (fun i => i.elim) bot_le s t (fun i => i.elim)

theorem opens_Spec_field_eq_bot_or_eq_top {K : Type u} [Field K] (U : (Spec (CommRingCat.of K)).Opens) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases hU : IsLocalRing.closedPoint K ∈ U
  · exact Or.inr (eq_top_iff.mpr fun y _ => by
      obtain rfl := Subsingleton.elim y (IsLocalRing.closedPoint K); exact hU)
  · exact Or.inl (eq_bot_iff.mpr fun y hy => hU (by
      obtain rfl := Subsingleton.elim y (IsLocalRing.closedPoint K); exact hy))

theorem isIso_pushforward_map_iff_bijective {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) {A B : X.Modules} (φ : A ⟶ B) :
    IsIso ((Scheme.Modules.pushforward x).map φ) ↔ Function.Bijective (φ.app ⊤) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  constructor
  · intro h
    have h' : IsIso (φ.app (x ⁻¹ᵁ ⊤)) := by
      have := h ⊤
      rwa [Scheme.Modules.pushforward_map_app] at this
    exact (ConcreteCategory.isIso_iff_bijective _).mp h'
  · intro hb U
    rw [Scheme.Modules.pushforward_map_app]
    rcases opens_Spec_field_eq_bot_or_eq_top U with rfl | rfl
    · apply (ConcreteCategory.isIso_iff_bijective _).mpr
      refine ⟨fun a b _ => sections_eq_of_eq_bot A rfl a b, fun b => ⟨0, sections_eq_of_eq_bot B rfl _ _⟩⟩
    · exact (ConcreteCategory.isIso_iff_bijective _).mpr hb

noncomputable def appTopₗ {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) {A B : X.Modules} (φ : A ⟶ B) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x A ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x B ⊤
    Γ(A, ⊤) →ₗ[K] Γ(B, ⊤) :=
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x A ⊤
  letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom x B ⊤
  { toFun := fun m => φ.app ⊤ m
    map_add' := fun a b => map_add _ a b
    map_smul' := fun r m => by
      letI := Scheme.TwoAffineOpenCover.algebraOfHom x ⊤
      show φ.app ⊤ ((algebraMap K Γ(X, ⊤) r) • m) = (algebraMap K Γ(X, ⊤) r) • φ.app ⊤ m
      exact Scheme.Modules.Hom.app_smul φ _ m }

theorem appTopₗ_apply {K : Type u} [Field K] {X : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of K)) {A B : X.Modules} (φ : A ⟶ B) (m : Γ(A, ⊤)) :
    appTopₗ x φ m = φ.app ⊤ m := rfl

theorem injective_iff_bijective_of_finrank_eq {K : Type u} [Field K] {V W : Type u}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [Module.Finite K W]
    (f : V →ₗ[K] W) (h : Module.finrank K V = Module.finrank K W) :
    Function.Injective f ↔ Function.Bijective f := by
  constructor
  · intro hf
    haveI : Module.Finite K V := Module.Finite.of_injective f hf
    exact ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank h).mp hf⟩
  · exact fun hb => hb.1

noncomputable def appTopAddEquiv {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B) [IsIso f] :
    Γ(A, ⊤) ≃+ Γ(B, ⊤) :=
  (asIso (f.app ⊤)).addCommGroupIsoToAddEquiv

theorem appTopAddEquiv_apply {X : Scheme.{u}} {A B : X.Modules} (f : A ⟶ B) [IsIso f] (x : Γ(A, ⊤)) :
    appTopAddEquiv f x = f.app ⊤ x := rfl

noncomputable def appTopAddEquivOfIso {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) :
    Γ(A, ⊤) ≃+ Γ(B, ⊤) :=
  AddEquiv.mk' ⟨fun x => e.hom.app ⊤ x, fun y => e.inv.app ⊤ y,
    fun x => by
      have h := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ x) e.hom_inv_id
      simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, CategoryTheory.comp_apply,
        CategoryTheory.id_apply] using h,
    fun y => by
      have h := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ y) e.inv_hom_id
      simpa only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, CategoryTheory.comp_apply,
        CategoryTheory.id_apply] using h⟩
    (fun a b => by
      show e.hom.app ⊤ (a + b) = e.hom.app ⊤ a + e.hom.app ⊤ b
      exact map_add _ a b)

theorem appTopAddEquivOfIso_apply {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) (x : Γ(A, ⊤)) :
    appTopAddEquivOfIso e x = e.hom.app ⊤ x := rfl

theorem exists_addEquiv_comm_unit (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    ∃ (eS : Γ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj (M.L ⊗ sectionTwist c ε t r), ⊤) ≃+
        Γ(((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule), ⊤))
      (eT : Γ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj
          ((Scheme.Modules.pushforward ((sectionIdeal c ε t) ^ n).subschemeι).obj ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r))), ⊤) ≃+
        Γ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).obj ((Scheme.Modules.pullback (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).obj
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule)), ⊤)),
      ∀ x, eT ((((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))).app ⊤ x) =
        (((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))).app ⊤ (eS x) := by
  have hG := isInvertible_tensor_sectionTwist k c ε M r
  have htop := isPullback_thickeningMap k c ε t n K s
  have hN : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)) := hG.pullback _

  haveI hβi := Scheme.Modules.isIso_baseChangeHom_of_isAffineHom htop _ hN.exists_trivialization

  haveI hτ : IsIso ((Scheme.Modules.pullbackTwoSquare htop.w).natTrans.app (M.L ⊗ sectionTwist c ε t r)) := by
    change IsIso (((Scheme.Modules.pullbackComp _ _).hom ≫ (Scheme.Modules.pullbackCongr _).hom ≫
      (Scheme.Modules.pullbackComp _ _).inv).app _)
    infer_instance

  obtain ⟨eTw⟩ := RelPicard.nonempty_pullback_sectionTwist_iso k c ε (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) r
  let e : (Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj (M.L ⊗ sectionTwist c ε t r) ≅
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule) :=
    Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t)) M.L (sectionTwist c ε t r) ≪≫
      whiskerLeftIso _ eTw

  have hmate := Scheme.Modules.unit_baseChangeHom htop.w (M.L ⊗ sectionTwist c ε t r)
  have hunit := (Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.naturality e.hom
  let eS := appTopAddEquivOfIso e
  let eT := (appTopAddEquiv (Scheme.Modules.baseChangeHom htop.w ((Scheme.Modules.pullback ((sectionIdeal c ε t) ^ n).subschemeι).obj (M.L ⊗ sectionTwist c ε t r)))).trans
      ((appTopAddEquiv (inv ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).map
        ((Scheme.Modules.pullbackTwoSquare htop.w).natTrans.app (M.L ⊗ sectionTwist c ε t r))))).trans
        (appTopAddEquivOfIso ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).mapIso
          ((Scheme.Modules.pullback (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).mapIso e))))
  refine ⟨eS, eT, fun x => ?_⟩
  have h1 := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ x) hmate
  have h2 := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤ x) hunit
  have h3 := congrArg (fun φ => Scheme.Modules.Hom.app φ ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj (M.L ⊗ sectionTwist c ε t r))).app ⊤ x))
    (IsIso.hom_inv_id ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).map
        ((Scheme.Modules.pullbackTwoSquare htop.w).natTrans.app (M.L ⊗ sectionTwist c ε t r))))
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app, CategoryTheory.comp_apply,
    CategoryTheory.id_apply, Functor.id_map, Functor.comp_map] at h1 h2 h3
  have T1 := congrArg (fun z =>
      appTopAddEquivOfIso ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).mapIso
        ((Scheme.Modules.pullback (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).mapIso e))
      (appTopAddEquiv (inv ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).map
        ((Scheme.Modules.pullbackTwoSquare htop.w).natTrans.app (M.L ⊗ sectionTwist c ε t r)))) z)) h1
  have T2 := congrArg (fun z =>
      appTopAddEquivOfIso ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).mapIso
        ((Scheme.Modules.pullback (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).mapIso e)) z) h3
  exact T1.trans (T2.trans h2.symm)

section

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
  (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T)

noncomputable def fibreIso : pullback (pullback.snd c t) s ≅ pullback c (s ≫ t) :=
  (IsPullback.of_hasPullback (pullback.snd c t) s).isoIsPullback _ _
    (isPullback_baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))

theorem fibreIso_hom_fst :
    (fibreIso k c K s).hom ≫ baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) =
      pullback.fst (pullback.snd c t) s :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

theorem fibreIso_hom_snd : (fibreIso k c K s).hom ≫ pullback.snd c (s ≫ t) = fibreAt c t s :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

theorem fibreIso_inv_fst :
    (fibreIso k c K s).inv ≫ pullback.fst (pullback.snd c t) s =
      baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) := by
  rw [← fibreIso_hom_fst k c K s, Iso.inv_hom_id_assoc]

theorem fibreIso_inv_fibreAt : (fibreIso k c K s).inv ≫ fibreAt c t s = pullback.snd c (s ≫ t) := by
  rw [← fibreIso_hom_snd k c K s, Iso.inv_hom_id_assoc]

end

noncomputable def comapCover {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (𝒱 : Y.TwoAffineOpenCover) :
    X.TwoAffineOpenCover where
  U0 := f ⁻¹ᵁ 𝒱.U0
  U1 := f ⁻¹ᵁ 𝒱.U1
  isAffineOpen_U0 := 𝒱.isAffineOpen_U0.preimage f
  isAffineOpen_U1 := 𝒱.isAffineOpen_U1.preimage f
  sup_eq_top := by rw [← Scheme.Hom.preimage_sup, 𝒱.sup_eq_top]; rfl
  isAffineOpen_inf := by rw [← Scheme.Hom.preimage_inf]; exact 𝒱.isAffineOpen_inf.preimage f

theorem nonempty_twoAffineOpenCover_fibre (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    Nonempty ((pullback (pullback.snd c t) s).TwoAffineOpenCover) := by
  obtain ⟨𝔉, -⟩ := h𝔉 0
  haveI : IsAffineHom (pullback.fst c (s ≫ t)) :=
    MorphismProperty.pullback_fst (P := @IsAffineHom) _ _ inferInstance
  haveI : IsAffineHom ((fibreIso k c K s).hom ≫ pullback.fst c (s ≫ t)) := inferInstance
  exact ⟨comapCover ((fibreIso k c K s).hom ≫ pullback.fst c (s ≫ t)) 𝔉.twoAffineOpenCover⟩

theorem nonempty_linearEquiv_H0_fibreModule (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T)
    (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover) (m : ℕ) :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd c (s ≫ t))
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ m).invModule) ⊤
    Nonempty ((𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t m))).H0 ≃ₗ[K]
      Γ(((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ m).invModule), ⊤)) := by

  obtain ⟨e93⟩ := nonempty_pullback_sectionTwist_iso k c ε (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t) m
  let G : (pullback c (s ≫ t)).Modules :=
    (Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
      (((rigSection c (s ≫ t) ε).ker) ^ m).invModule
  let eG : G ≅ (Scheme.Modules.pullback (fibreIso k c K s).inv).obj
      (fibreModule c t s (M.L ⊗ sectionTwist c ε t m)) :=
    ((Scheme.Modules.pullbackComp (fibreIso k c K s).inv (pullback.fst (pullback.snd c t) s)).app _ ≪≫
      (Scheme.Modules.pullbackCongr (fibreIso_inv_fst k c K s)).app _ ≪≫
      Scheme.Modules.pullbackTensorObjIso _ M.L (sectionTwist c ε t m) ≪≫
      whiskerLeftIso _ e93).symm

  obtain ⟨𝒱, -, -, ⟨eH0⟩, -⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso (pullback.snd c (s ≫ t)) (fibreAt c t s)
      (fibreIso k c K s).symm (fibreIso_inv_fibreAt k c K s) 𝒲 (fibreModule c t s (M.L ⊗ sectionTwist c ε t m))
      G eG

  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 (pullback.snd c (s ≫ t)) G
  exact ⟨eH0.symm.trans eΓ.symm⟩

theorem not_isIso_pullback_map_ev_iff (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) (r n d : ℕ) (hd : d + n = r) (hfib : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank K (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n) (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T) :
    ¬ IsIso ((Scheme.Modules.pullback s).map ((Scheme.Modules.pushforward (pullback.snd c t)).map ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))) ↔
      ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
        Nontrivial (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t d))).H0 := by
  classical
  have h1 := isIso_pullback_map_ev_iff k c ε M h𝔉 r n hfib K s
  have h2 := isIso_pushforward_map_iff_bijective (pullback.snd c (s ≫ t))
    ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).map
      ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))
  obtain ⟨eS, eT, hcomm⟩ := exists_addEquiv_comm_unit k c ε M r n K s
  have key : (fun x => (((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))).app ⊤ (eS x)) =
      (fun x => eT ((((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))).app ⊤ x)) := funext fun x => (hcomm x).symm
  have h3 : Function.Bijective ((((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).map
          ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r)))).app ⊤) ↔
      Function.Bijective ((((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))).app ⊤) := by
    constructor
    · intro hf
      have h' := eT.bijective.comp hf
      refine (Function.Bijective.of_comp_iff _ eS.bijective).1 ?_
      change Function.Bijective (fun x => (((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))).app ⊤ (eS x))
      rw [key]
      exact h'
    · intro hf'
      have h' : Function.Bijective (fun x => (((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))).app ⊤ (eS x)) := hf'.comp eS.bijective
      rw [key] at h'
      exact (Function.Bijective.of_comp_iff' eT.bijective _).1 h'

  have hσ' : rigSection c (s ≫ t) ε ≫ pullback.snd c (s ≫ t) = 𝟙 _ := rigSection_snd c (s ≫ t) ε
  have hL' : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L) :=
    M.isInvertible.pullback _
  obtain ⟨⟨hfinT, hrkT⟩, hinj⟩ :=
    AlgebraicGeometry.finrank_sections_pushforward_thickening_and_injective_unit_app_iff
      (pullback.snd c (s ≫ t)) (rigSection c (s ≫ t) ε) hσ'
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L) hL' r n d hd

  obtain ⟨𝒲₀⟩ := nonempty_twoAffineOpenCover_fibre k c ε M h𝔉 K s
  obtain ⟨er⟩ := nonempty_linearEquiv_H0_fibreModule k c ε M K s 𝒲₀ r
  have hsrc :
      (letI := (Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd c (s ≫ t))
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule) ⊤);
        Module.finrank K Γ(((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule), ⊤)) = n := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd c (s ≫ t))
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule) ⊤
    rw [← er.finrank_eq]
    exact (hfib K s 𝒲₀).2
  have h4 : Function.Injective ((((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))).app ⊤) ↔
      Function.Bijective ((((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))).app ⊤) := by
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd c (s ≫ t))
      ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule) ⊤
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom (pullback.snd c (s ≫ t))
      ((Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).obj ((Scheme.Modules.pullback (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).obj
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))) ⊤
    haveI := hfinT
    exact injective_iff_bijective_of_finrank_eq (appTopₗ
      (A := ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule))
      (B := (Scheme.Modules.pushforward (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).obj ((Scheme.Modules.pullback (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).obj
          ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule)))
      (pullback.snd c (s ≫ t))
      (((Scheme.Modules.pullbackPushforwardAdjunction (((rigSection c (s ≫ t) ε).ker) ^ n).subschemeι).unit.app
        ((Scheme.Modules.pullback (baseChangeSnd c (⟨s, rfl⟩ : SchemeHomOver (s ≫ t) t))).obj M.L ⊗
        (((rigSection c (s ≫ t) ε).ker) ^ r).invModule)))) (hsrc.trans hrkT.symm)
  have hA := h1.trans (h2.trans (h3.trans h4.symm))
  have hB := (not_congr (hA.trans hinj)).trans not_subsingleton_iff_nontrivial
  refine hB.trans ⟨fun hnt 𝒲 => ?_, fun h => ?_⟩
  · obtain ⟨ed⟩ := nonempty_linearEquiv_H0_fibreModule k c ε M K s 𝒲 d
    haveI := hnt
    exact ed.toEquiv.nontrivial
  · obtain ⟨ed⟩ := nonempty_linearEquiv_H0_fibreModule k c ε M K s 𝒲₀ d
    haveI := h 𝒲₀
    exact ed.symm.toEquiv.nontrivial

end ThetaLocusAux
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_exists_pullbackSection_thetaBundle_eq_zero_iff.ThetaLocusAux"

open ThetaLocusAux in

theorem solution
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n d : ℕ) (hd : d + n = r)
    (hfib : ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H1 ∧
        Module.finrank K (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t r))).H0 = n) :
    ∃ θ : 𝟙_ T.Modules ⟶ thetaBundle c ε t M r n,
      ∀ (K : Type u) [Field K] (s : Spec (CommRingCat.of K) ⟶ T),
        Scheme.Modules.pullbackSection s θ = 0 ↔
          ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
            Nontrivial (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t d))).H0 := by
  classical
  have hG := isInvertible_tensor_sectionTwist k c ε M r
  have hE : Scheme.Modules.IsLocallyFreeOfRank n
      ((Scheme.Modules.pushforward (pullback.snd c t)).obj (M.L ⊗ sectionTwist c ε t r)) :=
    RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre k c ε h𝔉 t _ hG n hfib
  obtain ⟨hF, hdet⟩ :=
    RelPicard.isLocallyFreeOfRank_pushforward_thickening_sectionTwist_and_nonempty_det_iso k c ε M r n
  obtain ⟨θ, hθ⟩ := Scheme.Modules.exists_pullbackSection_dual_det_eq_zero_iff_not_isIso hE hF
    ((Scheme.Modules.pushforward (pullback.snd c t)).map ((Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t) ^ n).subschemeι).unit.app (M.L ⊗ sectionTwist c ε t r))) hdet
  refine ⟨θ, fun K _ s => (hθ K s).trans ?_⟩
  exact not_isIso_pullback_map_ev_iff k c ε M h𝔉 r n d hd hfib K s

end S_AlgebraicGeometry_RelPicard_exists_pullbackSection_thetaBundle_eq_zero_iff
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_exists_pullbackSection_thetaBundle_eq_zero_iff (solution)
