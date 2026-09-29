-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.shortExact_map_pushforward_thickening
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/bfdb880d-0f76-5367-adc4-f51b3d1707aa

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_ModulesBaseChangeHom
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsLocallyFreeOfRank_of_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_one_iff_isInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_det_succ_iso_det_tensor_of_shortExact
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_exteriorPower_free_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_shortExact_map_pushforward_of_forall_exists_surjective_app
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_shortExact_thickening_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_epi_unit_app_tensor_invModule_pow_and_exists_shortExact
import Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_pullback_sectionTwist_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unit_app_comp_pullbackComp_inv
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_bijective_unit_app_of_le_opensRange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra CategoryTheory.MonoidalCategory Opposite TopologicalSpace TensorProduct"

namespace Ws31X1
open AlgebraicGeometry.Scheme.Modules

noncomputable def restrictTriv {Z : Scheme.{u}} {N : Z.Modules} {U₀ U : Z.Opens} (h : U ≤ U₀)
    (e : (Scheme.Modules.pullback U₀.ι).obj N ≅ 𝟙_ (U₀ : Scheme.{u}).Modules) :
    (Scheme.Modules.pullback U.ι).obj N ≅ 𝟙_ (U : Scheme.{u}).Modules :=
  (pullbackCongr (Z.homOfLE_ι h).symm).app N ≪≫
    ((pullbackComp (Z.homOfLE h) U₀.ι).app N).symm ≪≫
    (Scheme.Modules.pullback (Z.homOfLE h)).mapIso e ≪≫
    pullbackTensorUnitObjIso (Z.homOfLE h)
end Ws31X1

namespace Ws31ThetaF

open AlgebraicGeometry.Scheme.Modules

theorem locallyTrivialOver {Z T : Scheme.{u}} (q : Z ⟶ T) [UniversallyClosed q]
    (hinj : Function.Injective q.base) (hsurj : Function.Surjective q.base)
    (N : Z.Modules) (hN : IsInvertible N) (t : T) :
    ∃ W : T.Opens, t ∈ W ∧
      Nonempty ((Scheme.Modules.pullback (q ⁻¹ᵁ W).ι).obj N ≅ 𝟙_ (↑(q ⁻¹ᵁ W) : Scheme.{u}).Modules) := by
  obtain ⟨z, hz⟩ := hsurj t
  obtain ⟨V, hzV, ⟨eV⟩⟩ := hN.exists_trivialization z
  have hcl : IsClosed (q.base '' ((V : Set Z)ᶜ)) := q.isClosedMap _ (isClosed_compl_iff.mpr V.isOpen)
  let W : T.Opens := ⟨(q.base '' ((V : Set Z)ᶜ))ᶜ, isOpen_compl_iff.mpr hcl⟩
  have htW : t ∈ W := by
    rintro ⟨z', hz'V, hz't⟩
    apply hz'V
    rw [hinj (hz't.trans hz.symm)]
    exact hzV
  have hle : q ⁻¹ᵁ W ≤ V := by
    intro z' hz'
    by_contra h
    exact hz' ⟨z', h, rfl⟩
  exact ⟨W, htW, ⟨Ws31X1.restrictTriv hle eV⟩⟩

section setting

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

lemma rigSection_snd : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _

scoped instance smooth_snd : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c t inferInstance

scoped instance isClosedImmersion_rigSection : IsClosedImmersion (rigSection c t ε) := by
  have : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
    rw [rigSection_snd]; infer_instance
  exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)

lemma isInvertible_sectionIdeal : (sectionIdeal c ε t).IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) (rigSection c t ε) (rigSection_snd k c ε t)

lemma pker (n : ℕ) :
    IsFinite ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) ∧
      (∀ s : T, ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t).finrank s = n) ∧
      Flat ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) ∧
      LocallyOfFinitePresentation ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) :=
  Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id (p := pullback.snd c t)
    (rigSection c t ε) (rigSection_snd k c ε t) n

lemma range_rigSection_eq_support :
    Set.range (rigSection c t ε) = (((sectionIdeal c ε t).support : Closeds ↥(pullback c t)) : Set ↥(pullback c t)) := by
  change _ = (((rigSection c t ε).ker.support : Closeds ↥(pullback c t)) : Set ↥(pullback c t))
  rw [Scheme.Hom.support_ker, (rigSection c t ε).isClosedEmbedding.isClosed_range.closure_eq]

lemma injective_q (n : ℕ) (hn : n ≠ 0) :
    Function.Injective ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t).base := by
  intro z z' h
  have hz : (sectionIdeal c ε t ^ n).subschemeι z ∈ Set.range (rigSection c t ε) := by
    rw [range_rigSection_eq_support, ← Scheme.IdealSheafData.support_pow _ n hn,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  have hz' : (sectionIdeal c ε t ^ n).subschemeι z' ∈ Set.range (rigSection c t ε) := by
    rw [range_rigSection_eq_support, ← Scheme.IdealSheafData.support_pow _ n hn,
      ← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z', rfl⟩
  obtain ⟨s, hs⟩ := hz
  obtain ⟨s', hs'⟩ := hz'
  have e1 : (pullback.snd c t) ((sectionIdeal c ε t ^ n).subschemeι z) = s := by
    rw [← hs, ← Scheme.Hom.comp_apply, rigSection_snd]; rfl
  have e2 : (pullback.snd c t) ((sectionIdeal c ε t ^ n).subschemeι z') = s' := by
    rw [← hs', ← Scheme.Hom.comp_apply, rigSection_snd]; rfl
  have hss : s = s' := by
    rw [← e1, ← e2]
    exact h
  apply (sectionIdeal c ε t ^ n).subschemeι.isClosedEmbedding.injective
  rw [← hs, ← hs', hss]

lemma surjective_q (n : ℕ) (hn : n ≠ 0) :
    Function.Surjective ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t).base := by
  intro s
  have hs : rigSection c t ε s ∈ Set.range ((sectionIdeal c ε t ^ n).subschemeι) := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_pow _ n hn,
      ← range_rigSection_eq_support]
    exact ⟨s, rfl⟩
  obtain ⟨z, hz⟩ := hs
  refine ⟨z, ?_⟩
  change (pullback.snd c t) ((sectionIdeal c ε t ^ n).subschemeι z) = s
  rw [hz, ← Scheme.Hom.comp_apply, rigSection_snd]
  rfl

variable (M : RigidifiedLineBundle c ε t)

lemma isInvertible_G (r : ℕ) : IsInvertible (M.L ⊗ sectionTwist c ε t r) :=
  M.isInvertible.tensor ((isInvertible_sectionIdeal k c ε t).pow r).isInvertible_invModule

theorem lf [LocallyOfFiniteType t] (r n : ℕ) (hn : n ≠ 0) :
    IsLocallyFreeOfRank n
      ((Scheme.Modules.pushforward (pullback.snd c t)).obj
        ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ n).subschemeι)).obj
          ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ n).subschemeι)).obj (M.L ⊗ sectionTwist c ε t r)))) := by
  obtain ⟨hfin, hrk, hflat, hlfp⟩ := pker k c ε t n
  haveI := hfin; haveI := hflat; haveI := hlfp
  have hN := locallyTrivialOver ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t)
    (injective_q k c ε t n hn) (surjective_q k c ε t n hn) _
    ((isInvertible_G k c ε t M r).pullback ((sectionIdeal c ε t ^ n).subschemeι))
  have h := Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver ((sectionIdeal c ε t ^ n).subschemeι ≫ pullback.snd c t) n hrk _ hN
  exact IsLocallyFreeOfRank.of_iso
    ((pushforwardComp ((sectionIdeal c ε t ^ n).subschemeι) (pullback.snd c t)).app _).symm h

end setting

end Ws31ThetaF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF"

noncomputable section

namespace Ws31ThetaF
namespace E6

def isoUnitOfPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (L : Y.Modules)
    (e : (Scheme.Modules.pullback f).obj L ≅ 𝟙_ X.Modules) : L ≅ 𝟙_ Y.Modules :=
  ((Scheme.Modules.pullbackId Y).app L).symm ≪≫
    ((Scheme.Modules.pullbackCongr (IsIso.inv_hom_id f)).app L).symm ≪≫
    ((Scheme.Modules.pullbackComp (inv f) f).app L).symm ≪≫
    (Scheme.Modules.pullback (inv f)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (inv f)

def pushforwardInvIsoPullback {X Y : Scheme.{u}} (e : X ≅ Y) :
    Scheme.Modules.pushforward e.inv ≅ Scheme.Modules.pullback e.hom :=
  Adjunction.leftAdjointUniq
    (CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward e.inv) (Scheme.Modules.pushforward e.hom)
      ((Scheme.Modules.pushforwardId Y).symm ≪≫ (Scheme.Modules.pushforwardCongr e.inv_hom_id).symm ≪≫
        (Scheme.Modules.pushforwardComp e.inv e.hom).symm)
      (Scheme.Modules.pushforwardComp e.hom e.inv ≪≫ Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫
        Scheme.Modules.pushforwardId X)).toAdjunction
    (Scheme.Modules.pullbackPushforwardAdjunction e.hom)

theorem nonempty_iso_unit_of_field {K : Type u} [Field K] (L : (Spec (CommRingCat.of K)).Modules)
    (hL : Scheme.Modules.IsInvertible L) : Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) := by
  obtain ⟨U, hxU, ⟨eU⟩⟩ := hL.exists_trivialization default
  have hU : U = ⊤ := top_le_iff.mp fun y _ => by
    rw [Unique.eq_default y]; exact hxU
  subst hU
  exact ⟨isoUnitOfPullbackIso (Spec (CommRingCat.of K)).topIso.hom L eU⟩

section setting2

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

lemma rigSection_snd : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _

scoped instance smooth_snd : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) c t inferInstance

lemma isInvertible_sectionIdeal : (sectionIdeal c ε t).IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c t) (rigSection c t ε) (rigSection_snd k c ε t)

theorem nonempty_pullback_rigSection_sectionTwist_iso (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (sectionTwist c ε t r) ≅ 𝟙_ T.Modules) := by
  let ψ : SchemeHomOver t (𝟙 (Spec (CommRingCat.of k))) := ⟨t, Category.comp_id t⟩
  obtain ⟨e₁⟩ := AlgebraicGeometry.RelPicard.nonempty_pullback_sectionTwist_iso k c ε ψ r
  have hcomm : rigSection c t ε ≫ baseChangeSnd c ψ = t ≫ rigSection c (𝟙 _) ε :=
    rigSection_baseChangeSnd c ε ψ
  have hL₀ : Scheme.Modules.IsInvertible
      ((Scheme.Modules.pullback (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)).obj
        (sectionTwist c ε (𝟙 (Spec (CommRingCat.of k))) r)) :=
    (((isInvertible_sectionIdeal k c ε (𝟙 _)).pow r).isInvertible_invModule).pullback _
  obtain ⟨e₀⟩ := nonempty_iso_unit_of_field _ hL₀
  exact ⟨(Scheme.Modules.pullback (rigSection c t ε)).mapIso e₁.symm ≪≫
    (Scheme.Modules.pullbackComp (rigSection c t ε) (baseChangeSnd c ψ)).app _ ≪≫
    (Scheme.Modules.pullbackCongr hcomm).app _ ≪≫
    ((Scheme.Modules.pullbackComp t (rigSection c (𝟙 _) ε)).app _).symm ≪≫
    (Scheme.Modules.pullback t).mapIso e₀ ≪≫ Scheme.Modules.pullbackUnitIso t⟩

theorem nonempty_pullback_rigSection_module_iso :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (sectionIdeal c ε t).module ≅ 𝟙_ T.Modules) := by
  obtain ⟨eB⟩ := nonempty_pullback_rigSection_sectionTwist_iso k c ε t 1
  have h1 : sectionTwist c ε t 1 = (sectionIdeal c ε t).invModule := by
    unfold sectionTwist
    rw [pow_one]
  obtain ⟨eLD⟩ := ((isInvertible_sectionIdeal k c ε t).isInvertible_module).dual.2
  let σ := rigSection c t ε
  let A := (Scheme.Modules.pullback σ).obj (sectionIdeal c ε t).module
  let eB' : (Scheme.Modules.pullback σ).obj (sectionIdeal c ε t).invModule ≅ 𝟙_ T.Modules :=
    (Scheme.Modules.pullback σ).mapIso (eqToIso h1.symm) ≪≫ eB
  exact ⟨(ρ_ A).symm ≪≫ whiskerLeftIso A eB'.symm ≪≫
    (Scheme.Modules.pullbackTensorObjIso σ _ _).symm ≪≫
    (Scheme.Modules.pullback σ).mapIso eLD ≪≫ Scheme.Modules.pullbackUnitIso σ⟩

set_option maxHeartbeats 3200000 in
theorem nonempty_pushforward_thickening_one_iso (H : (pullback c t).Modules) :
    Nonempty ((Scheme.Modules.pushforward (pullback.snd c t)).obj
      ((Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H)) ≅
      (Scheme.Modules.pullback (rigSection c t ε)).obj H) := by
  haveI : IsClosedImmersion (rigSection c t ε) := by
    have : IsClosedImmersion (rigSection c t ε ≫ pullback.snd c t) := by
      rw [rigSection_snd]; infer_instance
    exact IsClosedImmersion.of_comp (rigSection c t ε) (pullback.snd c t)

  let i : (sectionIdeal c ε t).subscheme ⟶ pullback c t := (sectionIdeal c ε t).subschemeι
  let e : T ≅ (sectionIdeal c ε t).subscheme := asIso (rigSection c t ε).toImage
  have he : e.hom ≫ i = rigSection c t ε := (rigSection c t ε).toImage_imageι
  have hq : i ≫ pullback.snd c t = e.inv := by
    rw [← cancel_epi e.hom, ← Category.assoc, he, rigSection_snd, e.hom_inv_id]
  let N : (sectionIdeal c ε t).subscheme.Modules := (Scheme.Modules.pullback i).obj H
  let i₁ : (Scheme.Modules.pushforward (pullback.snd c t)).obj ((Scheme.Modules.pushforward i).obj N) ≅
      (Scheme.Modules.pushforward (i ≫ pullback.snd c t)).obj N :=
    (Scheme.Modules.pushforwardComp i (pullback.snd c t)).app N
  let i₂ : (Scheme.Modules.pushforward (i ≫ pullback.snd c t)).obj N ≅ (Scheme.Modules.pushforward e.inv).obj N :=
    (Scheme.Modules.pushforwardCongr hq).app N
  let i₃ : (Scheme.Modules.pushforward e.inv).obj N ≅ (Scheme.Modules.pullback e.hom).obj N :=
    (pushforwardInvIsoPullback e).app N
  let i₄ : (Scheme.Modules.pullback e.hom).obj N ≅ (Scheme.Modules.pullback (e.hom ≫ i)).obj H :=
    (Scheme.Modules.pullbackComp e.hom i).app H
  let i₅ : (Scheme.Modules.pullback (e.hom ≫ i)).obj H ≅ (Scheme.Modules.pullback (rigSection c t ε)).obj H :=
    (Scheme.Modules.pullbackCongr he).app H
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃ ≪≫ i₄ ≪≫ i₅⟩

theorem nonempty_pullback_rigSection_G_iso (M : RigidifiedLineBundle c ε t) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (M.L ⊗ sectionTwist c ε t r) ≅ 𝟙_ T.Modules) := by
  obtain ⟨eM⟩ := M.rigidified
  obtain ⟨eS⟩ := nonempty_pullback_rigSection_sectionTwist_iso k c ε t r
  exact ⟨Scheme.Modules.pullbackTensorObjIso _ _ _ ≪≫ (eM ⊗ᵢ eS) ≪≫ λ_ (𝟙_ T.Modules)⟩

end setting2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF"

end Ws31ThetaF.E6
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

noncomputable section

namespace Ws31ThetaF
namespace E6

lemma surjective_of_comp_of_injective {A B C : Ab.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hg : Function.Injective g) (h : Function.Surjective (f ≫ g)) : Function.Surjective f := by
  intro b
  obtain ⟨a, ha⟩ := h (g b)
  rw [ConcreteCategory.comp_apply] at ha
  exact ⟨a, hg ha⟩

lemma surjective_comp {A B C : Ab.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjective (f ≫ g) := by
  intro c
  obtain ⟨b, rfl⟩ := hg c
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨a, by rw [ConcreteCategory.comp_apply]⟩

lemma unit_app_unit_comp_map_pullbackObjUnitToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (𝟙_ Y.Modules) ≫
        (Scheme.Modules.pushforward f).map (Scheme.Modules.pullbackUnitIso f).hom =
      f.unitToPushforwardUnit := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  exact h

set_option maxHeartbeats 3200000 in

theorem surjective_unit_app_of_isAffineOpen_of_trivial {Z' Z : Scheme.{u}} (k : Z' ⟶ Z) [IsClosedImmersion k]
    (N : Z.Modules) (W : Z.Opens) (hW : IsAffineOpen W)
    (e : (Scheme.Modules.pullback W.ι).obj N ≅ 𝟙_ (↑W : Scheme.{u}).Modules) :
    Function.Surjective (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app N).app W) := by
  have hsq : (k ⁻¹ᵁ W).ι ≫ k = (k ∣_ W) ≫ W.ι := (morphismRestrict_ι k W).symm

  have h1 := Scheme.Modules.unit_app_comp_pullbackComp_inv (k ⁻¹ᵁ W).ι k N W
  have hb1 : Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction (k ⁻¹ᵁ W).ι).unit.app
      ((Scheme.Modules.pullback k).obj N)).app (k ⁻¹ᵁ W)) :=
    Scheme.Modules.bijective_unit_app_of_le_opensRange (k ⁻¹ᵁ W).ι _ _ (Scheme.Opens.opensRange_ι _).ge
  apply surjective_of_comp_of_injective _ _ hb1.1
  rw [← h1]
  refine surjective_comp _ _ ?_ (ConcreteCategory.bijective_of_isIso _).2

  rw [hsq]

  have h3 := Scheme.Modules.unit_app_comp_pullbackComp_inv (k ∣_ W) W.ι N W
  have hb3 : Function.Bijective (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app N).app W) :=
    Scheme.Modules.bijective_unit_app_of_le_opensRange W.ι N W (Scheme.Opens.opensRange_ι W).ge
  apply surjective_of_comp_of_injective _
    (((Scheme.Modules.pullbackComp (k ∣_ W) W.ι).inv.app N).app ((k ∣_ W ≫ W.ι) ⁻¹ᵁ W))
    (ConcreteCategory.bijective_of_isIso _).1
  rw [h3]
  refine surjective_comp _ _ hb3.2 ?_

  have nat := (Scheme.Modules.pullbackPushforwardAdjunction (k ∣_ W)).unit.naturality e.hom
  have nat' := congrArg (fun φ => Scheme.Modules.Hom.app φ (W.ι ⁻¹ᵁ W)) nat
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    Scheme.Modules.Hom.comp_app] at nat'
  apply surjective_of_comp_of_injective _
    (((Scheme.Modules.pushforward (k ∣_ W)).map ((Scheme.Modules.pullback (k ∣_ W)).map e.hom)).app (W.ι ⁻¹ᵁ W))
    (ConcreteCategory.bijective_of_isIso _).1
  rw [← nat']
  refine surjective_comp _ _ (ConcreteCategory.bijective_of_isIso _).2 ?_

  apply surjective_of_comp_of_injective _
    (((Scheme.Modules.pushforward (k ∣_ W)).map
      (Scheme.Modules.pullbackUnitIso (k ∣_ W)).hom).app (W.ι ⁻¹ᵁ W))
    (ConcreteCategory.bijective_of_isIso _).1
  rw [← Scheme.Modules.Hom.comp_app, unit_app_unit_comp_map_pullbackObjUnitToUnit]

  haveI : IsAffine (↑W : Scheme.{u}) := hW
  have hV : IsAffineOpen (W.ι ⁻¹ᵁ W) := by
    rw [Scheme.Opens.ι_preimage_self]
    exact isAffineOpen_top _
  have hsurj : Function.Surjective ((k ∣_ W).app (W.ι ⁻¹ᵁ W)) := (k ∣_ W).app_surjective _ hV
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, hx⟩

end Ws31ThetaF.E6
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

namespace Ws31ThetaF

namespace BaseCase

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace CategoryTheory.MonoidalCategory"
open AlgebraicGeometry.Scheme.Modules

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (N : Z.Modules) (U : Z.Opens) :
    Subsingleton Γ(N, U) := by
  have hU : U = ⊥ := le_bot_iff.mp fun x _ => isEmptyElim x
  let D : TopCat.Sheaf Ab Z.toTopCat := ⟨N.presheaf, N.isSheaf⟩
  have hT : IsTerminal (D.obj.obj (op U)) := D.isTerminalOfEqEmpty hU
  exact AddCommGrpCat.subsingleton_of_isZero hT.isZero

theorem isZero_of_subsingleton {X : Scheme.{u}} (M : X.Modules) (h : ∀ U : X.Opens, Subsingleton Γ(M, U)) :
    IsZero M :=
  (IsZero.iff_id_eq_zero M).mpr (Scheme.Modules.hom_ext _ _ fun U => by
    haveI := h U
    ext x
    exact Subsingleton.elim _ _)

theorem isZero_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (N : Z.Modules) : IsZero N :=
  isZero_of_subsingleton N (subsingleton_sections_of_isEmpty N)

theorem isZero_free_fin_zero (X : Scheme.{u}) :
    IsZero (SheafOfModules.free.{u} (R := X.ringCatSheaf) (ULift.{u} (Fin 0))) :=
  (IsZero.iff_id_eq_zero _).mpr
    ((SheafOfModules.freeHomEquiv (R := X.ringCatSheaf) (SheafOfModules.free.{u} (ULift.{u} (Fin 0)))
      (I := ULift.{u} (Fin 0))).injective (funext fun i => isEmptyElim i))

theorem isLocallyFreeOfRank_zero_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) :
    IsLocallyFreeOfRank 0 F :=
  ⟨fun _ => ⟨⊤, trivial, ⟨((Scheme.Modules.pullback (⊤ : X.Opens).ι).map_isZero hF).iso (isZero_free_fin_zero _)⟩⟩⟩

theorem nonempty_det_zero_iso_of_isZero {X : Scheme.{u}} {F : X.Modules} (hF : IsZero F) :
    Nonempty (Scheme.Modules.det 0 F ≅ SheafOfModules.unit X.ringCatSheaf) := by
  obtain ⟨e⟩ := nonempty_exteriorPower_free_iso_unit X 0
  exact ⟨(exteriorPower X 0).mapIso (hF.iso (isZero_free_fin_zero X)) ≪≫ e⟩

theorem support_pow_zero {X : Scheme.{u}} (I : X.IdealSheafData) : (I ^ 0).support = ⊥ := by
  have h : I ^ 0 = ⊤ := pow_zero I
  rw [h]
  exact Scheme.IdealSheafData.support_top

theorem isEmpty_subscheme_of_support_eq_bot {X : Scheme.{u}} (I : X.IdealSheafData) (hI : I.support = ⊥) :
    IsEmpty I.subscheme := by
  refine ⟨fun z => ?_⟩
  have hz : I.subschemeι z ∈ Set.range I.subschemeι := ⟨z, rfl⟩
  rw [Scheme.IdealSheafData.range_subschemeι, hI] at hz
  simp at hz

end BaseCase
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

end Ws31ThetaF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

namespace Ws31ThetaF

open AlgebraicGeometry.Scheme.Modules

theorem surjective_pushforward_map_app {Z Y : Scheme.{u}} (f : Z ⟶ Y) {M N : Z.Modules} (φ : M ⟶ N) (U : Y.Opens)
    (h : Function.Surjective (φ.app (f ⁻¹ᵁ U))) :
    Function.Surjective (((Scheme.Modules.pushforward f).map φ).app U) := by
  rw [Scheme.Modules.pushforward_map_app]
  exact h

theorem surjective_comp_app {X : Scheme.{u}} {M N P : X.Modules} (a : M ⟶ N) (b : N ⟶ P) (U : X.Opens)
    (ha : Function.Surjective (a.app U)) (hb : Function.Surjective (b.app U)) :
    Function.Surjective ((a ≫ b).app U) := by
  rw [Scheme.Modules.Hom.comp_app]
  intro z
  obtain ⟨y, rfl⟩ := hb z
  obtain ⟨x, rfl⟩ := ha y
  exact ⟨x, rfl⟩

theorem surjective_hom_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Surjective (e.hom.app U) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.hom U)).2

theorem surjective_inv_app {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Function.Surjective (e.inv.app U) :=
  (ConcreteCategory.bijective_of_isIso (Scheme.Modules.Hom.app e.inv U)).2

theorem epi_unit_of_iso {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {A B : C} (φ : A ≅ B) (h : Epi (adj.unit.app A)) : Epi (adj.unit.app B) := by
  have e : adj.unit.app B = φ.inv ≫ adj.unit.app A ≫ (L ⋙ R).map φ.hom := by
    rw [← adj.unit.naturality φ.hom]
    simp
  haveI := h
  rw [e]
  infer_instance

section unitfactor

variable {ZA ZB X : Scheme.{u}} (iA : ZA ⟶ X) (iB : ZB ⟶ X) (k : ZA ⟶ ZB) (hk : k ≫ iB = iA)

noncomputable def cmpIso (H : X.Modules) :
    (Scheme.Modules.pushforward iB).obj ((Scheme.Modules.pushforward k).obj
      ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback iB).obj H))) ≅
      (Scheme.Modules.pushforward iA).obj ((Scheme.Modules.pullback iA).obj H) :=
  (Scheme.Modules.pushforward k ⋙ Scheme.Modules.pushforward iB).mapIso ((pullbackComp k iB).app H) ≪≫
    (pushforwardComp k iB).app ((Scheme.Modules.pullback (k ≫ iB)).obj H) ≪≫
    (Scheme.Modules.pushforward (k ≫ iB)).mapIso ((pullbackCongr hk).app H) ≪≫
    (pushforwardCongr hk).app ((Scheme.Modules.pullback iA).obj H)

theorem unit_app_eq_comp_unit (H : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction iA).unit.app H =
      (Scheme.Modules.pullbackPushforwardAdjunction iB).unit.app H ≫
        (Scheme.Modules.pushforward iB).map
          ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app ((Scheme.Modules.pullback iB).obj H)) ≫
        (cmpIso iA iB k hk H).hom := by
  have u1 := unit_conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (k ≫ iB))
    ((Scheme.Modules.pullbackPushforwardAdjunction iB).comp (Scheme.Modules.pullbackPushforwardAdjunction k))
    (pullbackComp k iB).hom H
  rw [conjugateEquiv_pullbackComp_hom, Adjunction.comp_unit_app, ← Iso.app_inv, Iso.comp_inv_eq] at u1
  have u2 := unit_conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction iA)
    (Scheme.Modules.pullbackPushforwardAdjunction (k ≫ iB)) (pullbackCongr hk).hom H
  rw [conjugateEquiv_pullbackCongr_hom, ← Iso.app_inv, Iso.comp_inv_eq] at u2
  rw [u2, u1]
  simp only [cmpIso, Category.assoc, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Functor.comp_map]


noncomputable def ΦGen (H : X.Modules) :
    (Scheme.Modules.pushforward iB).obj ((Scheme.Modules.pullback iB).obj H) ⟶
      (Scheme.Modules.pushforward iA).obj ((Scheme.Modules.pullback iA).obj H) :=
  (Scheme.Modules.pushforward iB).map
      ((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app ((Scheme.Modules.pullback iB).obj H)) ≫
    (cmpIso iA iB k hk H).hom

theorem unit_app_comp_ΦGen (H : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction iB).unit.app H ≫ ΦGen iA iB k hk H =
      (Scheme.Modules.pullbackPushforwardAdjunction iA).unit.app H := by
  rw [ΦGen]
  exact (unit_app_eq_comp_unit iA iB k hk H).symm

theorem ΦGen_app_surjective (H : X.Modules) (W : X.Opens)
    (h : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app ((Scheme.Modules.pullback iB).obj H)).app
        (iB ⁻¹ᵁ W))) :
    Function.Surjective ((ΦGen iA iB k hk H).app W) := by
  rw [ΦGen]
  exact surjective_comp_app _ _ W (surjective_pushforward_map_app iB _ W h) (surjective_hom_app (cmpIso iA iB k hk H) W)

end unitfactor
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

private theorem _root_.Ws31ThetaF.nonempty_iso_unit_of_field {K : Type u} [Field K] (L : (Spec (CommRingCat.of K)).Modules)
    (hL : IsInvertible L) : Nonempty (L ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) :=
  Ws31ThetaF.E6.nonempty_iso_unit_of_field L hL

p2m_export "Ws31ThetaF" "nonempty_iso_unit_of_field"
section setting2

variable (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
  [IsProper c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
  {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))

private theorem _root_.Ws31ThetaF.nonempty_pullback_rigSection_module_iso :
    Nonempty ((Scheme.Modules.pullback (rigSection c t ε)).obj (sectionIdeal c ε t).module ≅ 𝟙_ T.Modules) :=
  Ws31ThetaF.E6.nonempty_pullback_rigSection_module_iso k c ε t

p2m_export "Ws31ThetaF" "nonempty_pullback_rigSection_module_iso"

private theorem _root_.Ws31ThetaF.nonempty_pushforward_thickening_one_iso (H : (pullback c t).Modules) :
    Nonempty ((Scheme.Modules.pushforward (pullback.snd c t)).obj
      ((Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H)) ≅
      (Scheme.Modules.pullback (rigSection c t ε)).obj H) :=
  Ws31ThetaF.E6.nonempty_pushforward_thickening_one_iso k c ε t H

p2m_export "Ws31ThetaF" "nonempty_pushforward_thickening_one_iso"

noncomputable abbrev Fm (m : ℕ) (H : (pullback c t).Modules) : T.Modules :=
  (Scheme.Modules.pushforward (pullback.snd c t)).obj
    ((Scheme.Modules.pushforward ((sectionIdeal c ε t ^ m).subschemeι)).obj
      ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ m).subschemeι)).obj H))

theorem lf_gen [LocallyOfFiniteType t] (H : (pullback c t).Modules) (hH : IsInvertible H) (m : ℕ) (hm : m ≠ 0) :
    IsLocallyFreeOfRank m (Fm k c ε t m H) := by
  obtain ⟨hfin, hrk, hflat, hlfp⟩ := pker k c ε t m
  haveI := hfin; haveI := hflat; haveI := hlfp
  have hN := locallyTrivialOver ((sectionIdeal c ε t ^ m).subschemeι ≫ pullback.snd c t)
    (injective_q k c ε t m hm) (surjective_q k c ε t m hm) _ (hH.pullback ((sectionIdeal c ε t ^ m).subschemeι))
  have h := Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver ((sectionIdeal c ε t ^ m).subschemeι ≫ pullback.snd c t) m hrk _ hN
  exact IsLocallyFreeOfRank.of_iso
    ((pushforwardComp ((sectionIdeal c ε t ^ m).subschemeι) (pullback.snd c t)).app _).symm h

lemma pow_succ_le (m : ℕ) : sectionIdeal c ε t ^ (m + 1) ≤ sectionIdeal c ε t := by
  rw [pow_succ]
  intro U
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  exact Ideal.mul_le_right

noncomputable def kIncl (m : ℕ) : (sectionIdeal c ε t).subscheme ⟶ (sectionIdeal c ε t ^ (m + 1)).subscheme :=
  (sectionIdeal c ε t).subschemeMap (sectionIdeal c ε t ^ (m + 1)) (𝟙 _)
    (by rw [Scheme.IdealSheafData.map_id]; exact pow_succ_le k c ε t m)

lemma kIncl_comp (m : ℕ) : kIncl k c ε t m ≫ (sectionIdeal c ε t ^ (m + 1)).subschemeι = (sectionIdeal c ε t).subschemeι := by
  rw [kIncl, Scheme.IdealSheafData.subschemeMap_subschemeι, Category.comp_id]

scoped instance (m : ℕ) : IsClosedImmersion (kIncl k c ε t m) := by
  have : IsClosedImmersion (kIncl k c ε t m ≫ (sectionIdeal c ε t ^ (m + 1)).subschemeι) := by
    rw [kIncl_comp]; infer_instance
  exact IsClosedImmersion.of_comp (kIncl k c ε t m) ((sectionIdeal c ε t ^ (m + 1)).subschemeι)

noncomputable def νT (H : (pullback c t).Modules) (m : ℕ) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (kIncl k c ε t m)).unit.app
    ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H)

lemma Φ_app_surjective (H : (pullback c t).Modules) (m : ℕ) (W : (pullback c t).Opens)
    (h : Function.Surjective ((νT k c ε t H m).app (((sectionIdeal c ε t ^ (m + 1)).subschemeι) ⁻¹ᵁ W))) :
    Function.Surjective ((ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι) (kIncl k c ε t m) (kIncl_comp k c ε t m) H).app W) :=
  ΦGen_app_surjective _ _ _ _ H W h
theorem g_eq_of_pin (H : (pullback c t).Modules) (hH : IsInvertible H) (m : ℕ)
    (S : ShortComplex (pullback c t).Modules)
    (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj
        ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H))
    (hpin : (Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).unit.app H ≫
        e₂.inv ≫ S.g ≫ e₃.hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (sectionIdeal c ε t).subschemeι).unit.app H) :
    S.g = e₂.hom ≫ ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι) (kIncl k c ε t m) (kIncl_comp k c ε t m) H ≫ e₃.inv := by
  let iB := (sectionIdeal c ε t ^ (m + 1)).subschemeι
  let N := (Scheme.Modules.pullback iB).obj H
  let ν := (Scheme.Modules.pullbackPushforwardAdjunction (kIncl k c ε t m)).unit.app N
  haveI : Epi ((Scheme.Modules.pullbackPushforwardAdjunction iB).unit.app H) := by
    have hIm := (isInvertible_sectionIdeal k c ε t).pow (m + 1)
    obtain ⟨eLD⟩ := (hIm.isInvertible_module).dual.2
    let φ : (H ⊗ (sectionIdeal c ε t ^ (m + 1)).module) ⊗ (sectionIdeal c ε t ^ (m + 1)).invModule ≅ H :=
      α_ _ _ _ ≪≫ whiskerLeftIso H eLD ≪≫ ρ_ H
    have hepi := (Scheme.IdealSheafData.IsInvertible.epi_unit_app_tensor_invModule_pow_and_exists_shortExact
      (sectionIdeal c ε t) (isInvertible_sectionIdeal k c ε t) (H ⊗ (sectionIdeal c ε t ^ (m + 1)).module)
      (hH.tensor hIm.isInvertible_module) (m + 1) (m + 1) 0 (Nat.zero_add _)).1
    exact epi_unit_of_iso (Scheme.Modules.pullbackPushforwardAdjunction iB) φ hepi
  have h2 := hpin.trans (unit_app_comp_ΦGen _ iB _ (kIncl_comp k c ε t m) H).symm
  have hψ := (cancel_epi _).mp h2
  have hψ' : e₂.inv ≫ S.g ≫ e₃.hom =
      ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι) (kIncl k c ε t m)
        (kIncl_comp k c ε t m) H := hψ
  exact ((Iso.eq_comp_inv e₃).mpr ((Iso.inv_comp_eq e₂).mp hψ')).trans (Category.assoc _ _ _)

set_option maxHeartbeats 1600000 in
theorem shortExact_map_pushforward_thickening [LocallyOfFiniteType t]
    (H : (pullback c t).Modules) (hH : IsInvertible H) (m : ℕ)
    (S : ShortComplex (pullback c t).Modules) (hS : S.ShortExact)
    (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj
        ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H))
    (hpin : (Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).unit.app H ≫
        e₂.inv ≫ S.g ≫ e₃.hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (sectionIdeal c ε t).subschemeι).unit.app H) :
    (S.map (Scheme.Modules.pushforward (pullback.snd c t))).ShortExact := by

  let iB := (sectionIdeal c ε t ^ (m + 1)).subschemeι
  let q := iB ≫ pullback.snd c t
  let N := (Scheme.Modules.pullback iB).obj H
  let ν := (Scheme.Modules.pullbackPushforwardAdjunction (kIncl k c ε t m)).unit.app N

  have hg : S.g = e₂.hom ≫ ΦGen (sectionIdeal c ε t).subschemeι ((sectionIdeal c ε t ^ (m + 1)).subschemeι) (kIncl k c ε t m) (kIncl_comp k c ε t m) H ≫ e₃.inv := g_eq_of_pin k c ε t H hH m S e₂ e₃ hpin

  obtain ⟨hfin, -, -, -⟩ := pker k c ε t (m + 1)
  haveI := hfin
  apply shortExact_map_pushforward_of_forall_exists_surjective_app (pullback.snd c t) S hS
  intro U y hyU
  obtain ⟨W₀, hyW₀, ⟨e₀⟩⟩ := locallyTrivialOver q (injective_q k c ε t (m + 1) (Nat.succ_ne_zero m))
    (surjective_q k c ε t (m + 1) (Nat.succ_ne_zero m)) N (hH.pullback iB) y
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVle⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ U ⊓ W₀ from ⟨hyU, hyW₀⟩) (U ⊓ W₀).isOpen
  refine ⟨V, hyV, fun z hz => (hVle hz).1, ?_⟩

  have hqV : IsAffineOpen (q ⁻¹ᵁ V) := hV.preimage q
  have eV : (Scheme.Modules.pullback (q ⁻¹ᵁ V).ι).obj N ≅ 𝟙_ _ :=
    Ws31X1.restrictTriv (show q ⁻¹ᵁ V ≤ q ⁻¹ᵁ W₀ from fun z hz => (hVle hz).2) e₀
  have hν : Function.Surjective ((νT k c ε t H m).app (iB ⁻¹ᵁ ((pullback.snd c t) ⁻¹ᵁ V))) :=
    Ws31ThetaF.E6.surjective_unit_app_of_isAffineOpen_of_trivial (kIncl k c ε t m) N (q ⁻¹ᵁ V) hqV eV
  rw [hg]
  exact surjective_comp_app _ _ _ (surjective_hom_app e₂ _)
    (surjective_comp_app _ _ _ (Φ_app_surjective k c ε t H m ((pullback.snd c t) ⁻¹ᵁ V) hν)
      (surjective_inv_app e₃ _))

end setting2
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

end Ws31ThetaF
p2m_reactivate "P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening.Ws31ThetaF.E6"

theorem solution
    (k : Type u) [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (H : (pullback c t).Modules) (hH : Scheme.Modules.IsInvertible H) (m : ℕ)
    (S : ShortComplex (pullback c t).Modules) (hS : S.ShortExact)
    (e₂ : S.X₂ ≅ (Scheme.Modules.pushforward ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj
        ((Scheme.Modules.pullback ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).obj H))
    (e₃ : S.X₃ ≅ (Scheme.Modules.pushforward (sectionIdeal c ε t).subschemeι).obj
        ((Scheme.Modules.pullback (sectionIdeal c ε t).subschemeι).obj H))
    (hpin : (Scheme.Modules.pullbackPushforwardAdjunction ((sectionIdeal c ε t ^ (m + 1)).subschemeι)).unit.app H ≫
        e₂.inv ≫ S.g ≫ e₃.hom
      = (Scheme.Modules.pullbackPushforwardAdjunction (sectionIdeal c ε t).subschemeι).unit.app H) :
    (S.map (Scheme.Modules.pushforward (pullback.snd c t))).ShortExact :=
  Ws31ThetaF.shortExact_map_pushforward_thickening k c ε t H hH m S hS e₂ e₃ hpin

end S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_shortExact_map_pushforward_thickening (solution)
