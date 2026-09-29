-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/4fa8d107-07e8-50e2-8ee3-6de00d715a39

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime.AlgebraicGeometry TopologicalSpace Opposite"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.pullback Scheme.Hom QuasiCompact Spec Spec.map Scheme.ΓSpecIso_inv_naturality Scheme QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_appTop Scheme.Modules.pullbackCongr IsAffineOpen isCompact_iff_finite_and_eq_biUnion_affineOpens Scheme.Modules QuasiSeparated Scheme.Modules.map_smul quasiSeparated_iff_quasiSeparatedSpace Scheme.Modules.pullbackComp Scheme.ΓSpecIso Scheme.Modules.IsInvertible isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen Scheme.Hom.appInf Scheme.Hom.appInf_apply Scheme.Hom.appInf_map_left Scheme.Hom.appInf_map_right"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom.id_app Hom Γ ΓSpecIso_inv_naturality Hom.comp_appTop affineOpens Hom.comp_app Modules.pullbackCongr isBasis_affineOpens Modules Opens Modules.map_smul Modules.pullbackComp ΓSpecIso Modules.IsInvertible Modules.pullbackLocalSection Hom.appInf Hom.appInf_apply Hom.appInf_map_left Hom.appInf_map_right"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "hom_ext Hom.app_smul Hom.mapPresheaf pullback presheaf Hom.comp_app Hom Hom.id_app pullbackCongr map_smul pullbackComp IsInvertible IsFrameOn pullbackLocalSection pullbackLocalSection_smul map_homOfLE_pullbackLocalSection exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq exists_isFrameOn_of_pullback_iso_unit"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

variable {X : Scheme.{u}}

lemma presheaf_map_homOfLE_refl' {U : X.Opens} (s : Γ(X, U)) :
    X.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : homOfLE (le_refl U) = 𝟙 U := rfl
  rw [this, op_id, X.presheaf.map_id]; rfl

namespace Hom p2m_export "AlgebraicGeometry.Scheme.Modules.Hom" "app_smul mapPresheaf comp_app id_app app" end Hom
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.Hom" in

lemma Hom.app_map_homOfLE {M N : X.Modules} (φ : M ⟶ N) {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) :
    φ.app W (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app U s) := by
  have := (Hom.mapPresheaf φ).naturality (homOfLE h).op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, W))) this) s)

private def _root_.AlgebraicGeometry.Scheme.Hom.appInf {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) :
    Γ(X, V ⊓ W) ⟶ Γ(Y, π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W) :=
  π.app (V ⊓ W)

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime.AlgebraicGeometry.Scheme.Hom.appInf" "AlgebraicGeometry.Scheme.Hom.appInf"
private lemma _root_.AlgebraicGeometry.Scheme.Hom.appInf_apply {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) (t : Γ(X, V ⊓ W)) :
    π.appInf V W t = π.app (V ⊓ W) t := rfl

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime.AlgebraicGeometry.Scheme.Hom.appInf_apply" "AlgebraicGeometry.Scheme.Hom.appInf_apply"

private lemma _root_.AlgebraicGeometry.Scheme.Hom.appInf_map_left {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) (y : Γ(X, V)) :
    π.appInf V W (X.presheaf.map (homOfLE inf_le_left).op y) =
      Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ V)).op (π.app V y) := by
  have h := congrArg (fun k => (ConcreteCategory.hom k) y) (π.naturality (homOfLE (inf_le_left : V ⊓ W ≤ V)).op)
  simp only [CategoryTheory.comp_apply] at h
  exact h

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime.AlgebraicGeometry.Scheme.Hom.appInf_map_left" "AlgebraicGeometry.Scheme.Hom.appInf_map_left"

private lemma _root_.AlgebraicGeometry.Scheme.Hom.appInf_map_right {Y : Scheme.{u}} (π : Y ⟶ X) (V W : X.Opens) (y : Γ(X, W)) :
    π.appInf V W (X.presheaf.map (homOfLE inf_le_right).op y) =
      Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ V ⊓ π ⁻¹ᵁ W ≤ π ⁻¹ᵁ W)).op (π.app W y) := by
  have h := congrArg (fun k => (ConcreteCategory.hom k) y) (π.naturality (homOfLE (inf_le_right : V ⊓ W ≤ W)).op)
  simp only [CategoryTheory.comp_apply] at h
  exact h

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime.AlgebraicGeometry.Scheme.Hom.appInf_map_right" "AlgebraicGeometry.Scheme.Hom.appInf_map_right"
namespace IsFrameOn p2m_export "AlgebraicGeometry.Scheme.Modules.IsFrameOn" "mono map existsUnique pullbackLocalSection" end IsFrameOn
namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.unit_smul {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V)
    {v : Γ(X, U)} (hv : IsUnit v) : IsFrameOn (v • s) V := by
  intro W hWU hWV
  have e : (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op (v • s)) =
      (fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s) ∘
        (fun g : Γ(X, W) => g * X.presheaf.map (homOfLE hWU).op v) := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.map_smul, mul_smul]
  rw [e]
  exact (hs hWU hWV).comp (Units.mulRight_bijective (hv.map (X.presheaf.map (homOfLE hWU).op).hom).unit)

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.unit_smul"
lemma presheaf_map_homOfLE_refl {M : X.Modules} {U : X.Opens} (s : Γ(M, U)) :
    M.presheaf.map (homOfLE (le_refl U)).op s = s := by
  have : homOfLE (le_refl U) = 𝟙 U := rfl
  rw [this, op_id, M.presheaf.map_id]; rfl

namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.existsUnique_self {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U)
    (x : Γ(M, U)) : ∃! g : Γ(X, U), g • s = x := by
  have := hs.existsUnique le_rfl le_rfl x
  simpa only [presheaf_map_homOfLE_refl] using this

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.existsUnique_self"
namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in
private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.smul_left_cancel {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s U)
    {g g' : Γ(X, U)} (h : g • s = g' • s) : g = g' :=
  (hs.existsUnique_self (g' • s)).unique h rfl

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.smul_left_cancel"
namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.smul_left_cancel' {M : X.Modules} {U V W : X.Opens} {s : Γ(M, U)} (hs : IsFrameOn s V)
    (hWU : W ≤ U) (hWV : W ≤ V) {g g' : Γ(X, W)}
    (h : g • M.presheaf.map (homOfLE hWU).op s = g' • M.presheaf.map (homOfLE hWU).op s) : g = g' :=
  (hs.existsUnique hWU hWV _).unique h rfl

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.smul_left_cancel'"
section Trans

variable {L : X.Modules} {ι : Type*} {U : ι → X.Opens} {s : ∀ k, Γ(L, U k)}

namespace IsFrameOn
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

private def _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.trans (hs : ∀ k, IsFrameOn (s k) (U k)) (i j : ι) : Γ(X, U i ⊓ U j) :=
  ((hs i).existsUnique (inf_le_left : U i ⊓ U j ≤ U i) inf_le_left
    (L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j))).exists.choose

end IsFrameOn
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsFrameOn.trans"
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in
lemma IsFrameOn.trans_spec (hs : ∀ k, IsFrameOn (s k) (U k)) (i j : ι) :
    IsFrameOn.trans hs i j • L.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (s i) =
      L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j) :=
  ((hs i).existsUnique (inf_le_left : U i ⊓ U j ≤ U i) inf_le_left
    (L.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (s j))).exists.choose_spec

p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsFrameOn" in

lemma IsFrameOn.app_trans_smul_pullbackLocalSection {Y : Scheme.{u}} (π : Y ⟶ X)
    (hs : ∀ k, IsFrameOn (s k) (U k)) (i j : ι) :
    π.appInf (U i) (U j) (IsFrameOn.trans hs i j) •
        ((Scheme.Modules.pullback π).obj L).presheaf.map
          (homOfLE (inf_le_left : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U i)).op (Modules.pullbackLocalSection π (s i)) =
      ((Scheme.Modules.pullback π).obj L).presheaf.map
          (homOfLE (inf_le_right : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U j)).op (Modules.pullbackLocalSection π (s j)) := by
  have h₁ := map_homOfLE_pullbackLocalSection π (inf_le_left : U i ⊓ U j ≤ U i) (s i)
  have h₂ := map_homOfLE_pullbackLocalSection π (inf_le_right : U i ⊓ U j ≤ U j) (s j)
  change π.app (U i ⊓ U j) (IsFrameOn.trans hs i j) •
      ((Scheme.Modules.pullback π).obj L).presheaf.map
        (homOfLE (π.preimage_mono (inf_le_left : U i ⊓ U j ≤ U i))).op (Modules.pullbackLocalSection π (s i)) =
    ((Scheme.Modules.pullback π).obj L).presheaf.map
        (homOfLE (π.preimage_mono (inf_le_right : U i ⊓ U j ≤ U j))).op (Modules.pullbackLocalSection π (s j))
  rw [h₁, h₂, ← pullbackLocalSection_smul, IsFrameOn.trans_spec]

end Trans

lemma exists_units_of_iso {Y : Scheme.{u}} (π : Y ⟶ X) {L₁ L₂ : X.Modules} {ι : Type*} {U : ι → X.Opens}
    {a : ∀ k, Γ(L₁, U k)} {b : ∀ k, Γ(L₂, U k)}
    (ha : ∀ k, IsFrameOn (a k) (U k)) (hb : ∀ k, IsFrameOn (b k) (U k))
    (e : (Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂) :
    ∃ u : ∀ k, Γ(Y, π ⁻¹ᵁ U k), (∀ k, IsUnit (u k)) ∧
      ∀ i j, π.appInf (U i) (U j) (IsFrameOn.trans ha i j) *
          Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U i)).op (u i) =
        Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U j)).op (u j) *
          π.appInf (U i) (U j) (IsFrameOn.trans hb i j) := by
  classical
  have hA : ∀ k, IsFrameOn (Modules.pullbackLocalSection π (a k)) (π ⁻¹ᵁ U k) :=
    fun k => (ha k).pullbackLocalSection π
  have hB : ∀ k, IsFrameOn (Modules.pullbackLocalSection π (b k)) (π ⁻¹ᵁ U k) :=
    fun k => (hb k).pullbackLocalSection π
  have hu := fun k => (hB k).existsUnique_self (e.hom.app _ (Modules.pullbackLocalSection π (a k)))
  choose u hu₁ _hu₂ using hu
  have hw := fun k => (hA k).existsUnique_self (e.inv.app _ (Modules.pullbackLocalSection π (b k)))
  choose w hw₁ _hw₂ using hw
  refine ⟨u, fun k => ?_, fun i j => ?_⟩
  · refine IsUnit.of_mul_eq_one (w k) ?_
    apply (hA k).smul_left_cancel
    rw [one_smul, mul_smul, hw₁ k, ← Hom.app_smul, hu₁ k, ← CategoryTheory.comp_apply, ← Hom.comp_app,
      e.hom_inv_id, Hom.id_app]
    rfl
  · apply (hB i).smul_left_cancel' inf_le_left inf_le_left
    rw [mul_smul, mul_smul, IsFrameOn.app_trans_smul_pullbackLocalSection π hb i j,
      ← Scheme.Modules.map_smul, ← Scheme.Modules.map_smul, hu₁ i, hu₁ j,
      ← Hom.app_map_homOfLE, ← Hom.app_map_homOfLE, ← Hom.app_smul]
    erw [IsFrameOn.app_trans_smul_pullbackLocalSection π ha i j]

lemma nonempty_iso_of_units {Y : Scheme.{u}} (π : Y ⟶ X) {L₁ L₂ : X.Modules} {ι : Type u} [LinearOrder ι]
    {U : ι → X.Opens} (hU : ⨆ k, U k = ⊤)
    {a : ∀ k, Γ(L₁, U k)} {b : ∀ k, Γ(L₂, U k)}
    (ha : ∀ k, IsFrameOn (a k) (U k)) (hb : ∀ k, IsFrameOn (b k) (U k))
    (v : ∀ k, Γ(Y, π ⁻¹ᵁ U k)) (hv : ∀ k, IsUnit (v k))
    (hcoc : ∀ i j, π.appInf (U i) (U j) (IsFrameOn.trans ha i j) *
          Y.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U i)).op (v i) =
        Y.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ U i ⊓ π ⁻¹ᵁ U j ≤ π ⁻¹ᵁ U j)).op (v j) *
          π.appInf (U i) (U j) (IsFrameOn.trans hb i j)) :
    Nonempty ((Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂) := by
  have hA : ∀ k, IsFrameOn (Modules.pullbackLocalSection π (a k)) (π ⁻¹ᵁ U k) :=
    fun k => (ha k).pullbackLocalSection π
  have hB : ∀ k, IsFrameOn (v k • Modules.pullbackLocalSection π (b k)) (π ⁻¹ᵁ U k) :=
    fun k => ((hb k).pullbackLocalSection π).unit_smul (hv k)
  obtain ⟨e, -⟩ := exists_iso_app_eq_of_iSup_eq_top_of_forall_smul_eq (fun k => π ⁻¹ᵁ U k)
    (π.iSup_preimage_eq_top hU) _ _ hA hB (fun i j _ g hg => by
      have hg' : g = π.appInf (U i) (U j) (IsFrameOn.trans ha i j) :=
        (hA i).smul_left_cancel' inf_le_left inf_le_left
          (hg.trans (IsFrameOn.app_trans_smul_pullbackLocalSection π ha i j).symm)
      rw [hg', Scheme.Modules.map_smul, Scheme.Modules.map_smul, smul_smul, hcoc i j, mul_smul,
        IsFrameOn.app_trans_smul_pullbackLocalSection π hb i j])
  exact ⟨e⟩

namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback exists_trivialization" end IsInvertible
namespace IsInvertible
p2m_open_scoped "AlgebraicGeometry.Scheme.Modules.IsInvertible" in

private lemma _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_fin_affine_cover_isFrameOn₂ [CompactSpace X] {L₁ L₂ : X.Modules}
    (h₁ : IsInvertible L₁) (h₂ : IsInvertible L₂) :
    ∃ (n : ℕ) (U : Fin n → X.Opens), (∀ k, IsAffineOpen (U k)) ∧ ⨆ k, U k = ⊤ ∧
      ∃ (a : ∀ k, Γ(L₁, U k)) (b : ∀ k, Γ(L₂, U k)),
        (∀ k, IsFrameOn (a k) (U k)) ∧ (∀ k, IsFrameOn (b k) (U k)) := by
  classical
  have key : ∀ x : X, ∃ (W : X.Opens), IsAffineOpen W ∧ x ∈ W ∧
      (∃ s : Γ(L₁, W), IsFrameOn s W) ∧ ∃ s : Γ(L₂, W), IsFrameOn s W := by
    intro x
    obtain ⟨V₁, hx₁, ⟨e₁⟩⟩ := h₁.exists_trivialization x
    obtain ⟨V₂, hx₂, ⟨e₂⟩⟩ := h₂.exists_trivialization x
    obtain ⟨s₁, hs₁⟩ := exists_isFrameOn_of_pullback_iso_unit V₁ e₁
    obtain ⟨s₂, hs₂⟩ := exists_isFrameOn_of_pullback_iso_unit V₂ e₂
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((V₁ ⊓ V₂ : X.Opens) : Set X) from ⟨hx₁, hx₂⟩) (V₁ ⊓ V₂).isOpen
    have h1 : W ≤ V₁ := fun y hy => (hWV hy).1
    have h2 : W ≤ V₂ := fun y hy => (hWV hy).2
    exact ⟨W, hW, hxW, ⟨L₁.presheaf.map (homOfLE h1).op s₁, (hs₁.map _).mono h1⟩,
      ⟨L₂.presheaf.map (homOfLE h2).op s₂, (hs₂.map _).mono h2⟩⟩
  choose W hWaff hxW hfr₁ hfr₂ using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set X)) (fun x => (W x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨t.card, fun k => W (t.equivFin.symm k), fun k => hWaff _, ?_, fun k => (hfr₁ _).choose,
    fun k => (hfr₂ _).choose, fun k => (hfr₁ _).choose_spec, fun k => (hfr₂ _).choose_spec⟩
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨t.equivFin ⟨y, hy⟩, by simpa using hxy⟩

end IsInvertible
p2m_export "AlgebraicGeometry.Scheme.Modules" "IsInvertible.exists_fin_affine_cover_isFrameOn₂"
end AlgebraicGeometry.Scheme.Modules

namespace LimitIso

p2m_open "AlgebraicGeometry.Scheme.Modules P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime.AlgebraicGeometry.Scheme.Modules"

section BaseFun

variable {R : Type u} [CommRing R] {B : Scheme.{u}} (q : B ⟶ Spec (.of R))

def baseFun (V : B.Opens) : R →+* Γ(B, V) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop ≫ B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom

lemma baseFun_apply (V : B.Opens) (r : R) :
    baseFun q V r = B.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (q.appTop ((Scheme.ΓSpecIso (.of R)).inv r)) :=
  rfl

lemma map_baseFun {V W : B.Opens} (h : W ≤ V) (r : R) :
    B.presheaf.map (homOfLE h).op (baseFun q V r) = baseFun q W r := by
  rw [baseFun_apply, baseFun_apply, ← CategoryTheory.comp_apply, ← Functor.map_comp]
  rfl

lemma app_baseFun {B' : Scheme.{u}} (p : B' ⟶ B) (V : B.Opens) (r : R) :
    p.app V (baseFun q V r) = baseFun (p ≫ q) (p ⁻¹ᵁ V) r := by
  rw [baseFun_apply, baseFun_apply, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2 := congrArg (fun k => (ConcreteCategory.hom k) (q.appTop ((Scheme.ΓSpecIso (.of R)).inv r)))
    (p.naturality (homOfLE (le_top : V ≤ ⊤)).op)
  simp only [CategoryTheory.comp_apply] at h2
  rw [h2]
  rfl

lemma isUnit_baseFun {T : Type u} [CommRing T] [Algebra R T]
    (s : B ⟶ Spec (.of T)) (hs : s ≫ Spec.map (CommRingCat.ofHom (algebraMap R T)) = q) (W : B.Opens)
    (r : R) (hr : IsUnit (algebraMap R T r)) : IsUnit (baseFun q W r) := by
  subst hs
  rw [baseFun_apply, Scheme.Hom.comp_appTop, CategoryTheory.comp_apply]
  have h2 := congrArg (fun k => (ConcreteCategory.hom k) r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R T)))
  simp only [CategoryTheory.comp_apply] at h2
  rw [← h2]
  exact ((hr.map _).map _).map _

end BaseFun

section SBC

variable {R : Type u} [CommRing R] (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
  {B : Scheme.{u}} (q : B ⟶ Spec (.of R))

abbrev BC : Scheme.{u} := pullback q (Spec.map (CommRingCat.ofHom (algebraMap R T)))

abbrev pr : BC T q ⟶ B := pullback.fst q (Spec.map (CommRingCat.ofHom (algebraMap R T)))

theorem isLocalization_sections (V : B.Opens) (hV : IsAffineOpen V) :
    letI := ((pr T q).app V).hom.toAlgebra
    IsLocalization (M.map (baseFun q V : R →* Γ(B, V))) Γ(BC T q, pr T q ⁻¹ᵁ V) :=
  AlgebraicGeometry.isLocalization_map_app_pullback_fst_preimage_of_isAffineOpen M T q V hV

lemma isUnit_baseFun_pr (W : (BC T q).Opens) (m : M) : IsUnit (baseFun (pr T q ≫ q) W m) :=
  isUnit_baseFun (pr T q ≫ q) (pullback.snd _ _) pullback.condition.symm W m (IsLocalization.map_units T m)

lemma sbc_surj (V : B.Opens) (hV : IsAffineOpen V) (x : Γ(BC T q, pr T q ⁻¹ᵁ V)) :
    ∃ (y : Γ(B, V)) (m : M), x * baseFun (pr T q ≫ q) (pr T q ⁻¹ᵁ V) m = (pr T q).app V y := by
  letI := ((pr T q).app V).hom.toAlgebra
  haveI := isLocalization_sections M T q V hV
  obtain ⟨⟨y, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := IsLocalization.surj (M.map (baseFun q V : R →* Γ(B, V))) x
  refine ⟨y, ⟨m, hm⟩, ?_⟩
  rw [← app_baseFun]
  exact h

lemma sbc_exists_of_eq (V : B.Opens) (hV : IsAffineOpen V) (y y' : Γ(B, V))
    (h : (pr T q).app V y = (pr T q).app V y') :
    ∃ m : M, baseFun q V m * y = baseFun q V m * y' := by
  letI := ((pr T q).app V).hom.toAlgebra
  haveI := isLocalization_sections M T q V hV
  obtain ⟨⟨_, ⟨m, hm, rfl⟩⟩, hc⟩ := (IsLocalization.eq_iff_exists (M.map (baseFun q V : R →* Γ(B, V))) _).1 h
  exact ⟨⟨m, hm⟩, hc⟩

lemma sbc_exists_of_eq_of_isCompact [QuasiSeparatedSpace B] (W : B.Opens) (hW : IsCompact (W : Set B))
    (y y' : Γ(B, W)) (h : (pr T q).app W y = (pr T q).app W y') :
    ∃ m : M, baseFun q W m * y = baseFun q W m * y' := by
  classical
  obtain ⟨S, hSfin, hWS⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := W)).1 hW
  haveI : Fintype S := hSfin.fintype
  have hle : ∀ V : S, ((V : B.affineOpens) : B.Opens) ≤ W := fun V => by
    rw [hWS]; exact le_iSup₂ (f := fun (i : B.affineOpens) (_ : i ∈ S) => (i : B.Opens)) V.1 V.2
  have key : ∀ V : S, ∃ m : M,
      baseFun q V m * B.presheaf.map (homOfLE (hle V)).op y = baseFun q V m * B.presheaf.map (homOfLE (hle V)).op y' := by
    intro V
    apply sbc_exists_of_eq M T q _ V.1.2
    have nat := fun z => congrArg (fun k => (ConcreteCategory.hom k) z) ((pr T q).naturality (homOfLE (hle V)).op)
    simp only [CategoryTheory.comp_apply] at nat
    rw [nat, nat, h]
  choose m hm using key
  refine ⟨∏ V : S, m V, ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' B.sheaf (fun V : S => ((V : B.affineOpens) : B.Opens)) W
    (fun V => homOfLE (hle V))
  · rw [hWS]; exact iSup₂_le fun V hV => le_iSup (fun V : S => ((V : B.affineOpens) : B.Opens)) ⟨V, hV⟩
  · intro V
    change B.presheaf.map (homOfLE (hle V)).op (baseFun q W ↑(∏ V : S, m V) * y) =
      B.presheaf.map (homOfLE (hle V)).op (baseFun q W ↑(∏ V : S, m V) * y')
    rw [map_mul, map_mul, map_baseFun, ← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ V),
      Submonoid.coe_mul, map_mul, mul_comm (baseFun q _ _) _, mul_assoc, mul_assoc, hm V]

end SBC

section Spread

variable {R : Type u} [CommRing R] (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
  {B : Scheme.{u}} (q : B ⟶ Spec (.of R))

lemma spread [QuasiSeparatedSpace B] {ι : Type} [Finite ι] {U : ι → B.Opens} (hUaff : ∀ k, IsAffineOpen (U k))
    (t₁ t₂ : ∀ i j : ι, Γ(B, U i ⊓ U j))
    (u : ∀ k, Γ(BC T q, pr T q ⁻¹ᵁ U k)) (hu : ∀ k, IsUnit (u k))
    (hcoc : ∀ i j, (pr T q).appInf (U i) (U j) (t₁ i j) *
          (BC T q).presheaf.map (homOfLE (inf_le_left : pr T q ⁻¹ᵁ U i ⊓ pr T q ⁻¹ᵁ U j ≤ _)).op (u i) =
        (BC T q).presheaf.map (homOfLE (inf_le_right : pr T q ⁻¹ᵁ U i ⊓ pr T q ⁻¹ᵁ U j ≤ _)).op (u j) *
          (pr T q).appInf (U i) (U j) (t₂ i j)) :
    ∃ m ∈ M, ∀ (T' : Type u) [CommRing T'] [Algebra R T'], IsUnit (algebraMap R T' m) →
      ∃ v : ∀ k, Γ(BC T' q, pr T' q ⁻¹ᵁ U k), (∀ k, IsUnit (v k)) ∧
        ∀ i j, (pr T' q).appInf (U i) (U j) (t₁ i j) *
            (BC T' q).presheaf.map (homOfLE (inf_le_left : pr T' q ⁻¹ᵁ U i ⊓ pr T' q ⁻¹ᵁ U j ≤ _)).op (v i) =
          (BC T' q).presheaf.map (homOfLE (inf_le_right : pr T' q ⁻¹ᵁ U i ⊓ pr T' q ⁻¹ᵁ U j ≤ _)).op (v j) *
            (pr T' q).appInf (U i) (U j) (t₂ i j) := by
  classical
  haveI := Fintype.ofFinite ι

  have hsurj := fun k => sbc_surj M T q (U k) (hUaff k) (u k)
  choose y m hy using hsurj
  have hsurj' := fun k => sbc_surj M T q (U k) (hUaff k) (↑(hu k).unit⁻¹ : Γ(BC T q, (pr T q) ⁻¹ᵁ U k))
  choose y' m' hy' using hsurj'
  have hyy : ∀ k, (pr T q).app (U k) (y k * y' k) = (pr T q).app (U k) (baseFun q (U k) ((m k * m' k : M) : R)) := by
    intro k
    rw [map_mul, ← hy, ← hy', app_baseFun, Submonoid.coe_mul, map_mul]
    calc u k * baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U k) (m k) * (↑(hu k).unit⁻¹ * baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U k) (m' k))
        = (u k * ↑(hu k).unit⁻¹) * (baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U k) (m k) * baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U k) (m' k)) := by
          ring
      _ = baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U k) (m k) * baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U k) (m' k) := by
          rw [(hu k).mul_val_inv, one_mul]
  have hm'' := fun k => sbc_exists_of_eq M T q (U k) (hUaff k) _ _ (hyy k)
  choose m'' hm'' using hm''

  have hF : ∀ i j, (pr T q).appInf (U i) (U j)
        (t₁ i j * B.presheaf.map (homOfLE inf_le_left).op (y i) * baseFun q _ (m j)) =
      (pr T q).appInf (U i) (U j)
        (B.presheaf.map (homOfLE inf_le_right).op (y j) * t₂ i j * baseFun q _ (m i)) := by
    intro i j
    have hc := hcoc i j
    have nb : ∀ r : R, (pr T q).appInf (U i) (U j) (baseFun q (U i ⊓ U j) r) =
        baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U i ⊓ (pr T q) ⁻¹ᵁ U j) r := fun r => app_baseFun q (pr T q) (U i ⊓ U j) r
    have ri : (BC T q).presheaf.map (homOfLE (inf_le_left : (pr T q) ⁻¹ᵁ U i ⊓ (pr T q) ⁻¹ᵁ U j ≤ (pr T q) ⁻¹ᵁ U i)).op ((pr T q).app (U i) (y i)) =
        (BC T q).presheaf.map (homOfLE inf_le_left).op (u i) * baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U i ⊓ (pr T q) ⁻¹ᵁ U j) (m i) := by
      rw [← hy, map_mul, map_baseFun]
    have rj : (BC T q).presheaf.map (homOfLE (inf_le_right : (pr T q) ⁻¹ᵁ U i ⊓ (pr T q) ⁻¹ᵁ U j ≤ (pr T q) ⁻¹ᵁ U j)).op ((pr T q).app (U j) (y j)) =
        (BC T q).presheaf.map (homOfLE inf_le_right).op (u j) * baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U i ⊓ (pr T q) ⁻¹ᵁ U j) (m j) := by
      rw [← hy, map_mul, map_baseFun]
    simp only [map_mul]
    rw [Scheme.Hom.appInf_map_left, Scheme.Hom.appInf_map_right, nb, nb, ri, rj]
    linear_combination (baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U i ⊓ (pr T q) ⁻¹ᵁ U j) (m i) *
      baseFun ((pr T q) ≫ q) ((pr T q) ⁻¹ᵁ U i ⊓ (pr T q) ⁻¹ᵁ U j) (m j)) * hc
  have hWc : ∀ i j, IsCompact ((U i ⊓ U j : B.Opens) : Set B) := fun i j =>
    QuasiSeparatedSpace.inter_isCompact _ _ (U i).isOpen (hUaff i).isCompact (U j).isOpen (hUaff j).isCompact
  have hmij := fun i j => sbc_exists_of_eq_of_isCompact M T q (U i ⊓ U j) (hWc i j) _ _ (hF i j)
  choose mij hmij using hmij

  let P : R := (∏ k, ((m k : R) * (m' k : R) * (m'' k : R))) * ∏ i, ∏ j, (mij i j : R)
  have hP : P ∈ M :=
    M.mul_mem (M.prod_mem fun k _ => M.mul_mem (M.mul_mem (m k).2 (m' k).2) (m'' k).2)
      (M.prod_mem fun i _ => M.prod_mem fun j _ => (mij i j).2)
  refine ⟨P, hP, ?_⟩
  intro T' _ _ hunit
  have dv : ∀ x : R, x ∣ P → IsUnit (algebraMap R T' x) := fun x hx => isUnit_of_dvd_unit (map_dvd _ hx) hunit
  have hprod : ∀ k, (m k : R) * (m' k : R) * (m'' k : R) ∣ P := fun k =>
    Dvd.dvd.mul_right (Finset.dvd_prod_of_mem (fun k => (m k : R) * (m' k : R) * (m'' k : R)) (Finset.mem_univ k)) _
  have hmU : ∀ k, IsUnit (algebraMap R T' (m k)) := fun k =>
    dv _ (dvd_trans (Dvd.dvd.mul_right (dvd_mul_right _ _) _) (hprod k))
  have hm'U : ∀ k, IsUnit (algebraMap R T' (m' k)) := fun k =>
    dv _ (dvd_trans (Dvd.dvd.mul_right (dvd_mul_left _ _) _) (hprod k))
  have hm''U : ∀ k, IsUnit (algebraMap R T' (m'' k)) := fun k =>
    dv _ (dvd_trans (dvd_mul_left _ _) (hprod k))
  have hmijU : ∀ i j, IsUnit (algebraMap R T' (mij i j)) := fun i j =>
    dv _ (Dvd.dvd.mul_left (dvd_trans (Finset.dvd_prod_of_mem (fun j => (mij i j : R)) (Finset.mem_univ j))
      (Finset.dvd_prod_of_mem (fun i => ∏ j, (mij i j : R)) (Finset.mem_univ i))) _)
  have cU : ∀ (W : (BC T' q).Opens) (r : R), IsUnit (algebraMap R T' r) → IsUnit (baseFun ((pr T' q) ≫ q) W r) :=
    fun W r hr => isUnit_baseFun _ _ pullback.condition.symm W r hr

  refine ⟨fun k => (pr T' q).app (U k) (y k) * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m k) (hmU k)).unit⁻¹, fun k => ?_, fun i j => ?_⟩
  · refine IsUnit.of_mul_eq_one ((pr T' q).app (U k) (y' k) * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m' k) (hm'U k)).unit⁻¹) ?_
    have h3 := congrArg ((pr T' q).app (U k)) (hm'' k)
    simp only [map_mul, app_baseFun, Submonoid.coe_mul] at h3
    have h4 := (cU _ (m'' k) (hm''U k)).mul_left_cancel h3
    calc (pr T' q).app (U k) (y k) * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m k) (hmU k)).unit⁻¹ *
          ((pr T' q).app (U k) (y' k) * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m' k) (hm'U k)).unit⁻¹)
        = ((pr T' q).app (U k) (y k) * (pr T' q).app (U k) (y' k)) *
          (↑(cU ((pr T' q) ⁻¹ᵁ U k) (m k) (hmU k)).unit⁻¹ * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m' k) (hm'U k)).unit⁻¹) := by ring
      _ = (baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U k) (m k) * baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U k) (m' k)) *
          (↑(cU ((pr T' q) ⁻¹ᵁ U k) (m k) (hmU k)).unit⁻¹ * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m' k) (hm'U k)).unit⁻¹) := by rw [h4]
      _ = (baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U k) (m k) * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m k) (hmU k)).unit⁻¹) *
          (baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U k) (m' k) * ↑(cU ((pr T' q) ⁻¹ᵁ U k) (m' k) (hm'U k)).unit⁻¹) := by ring
      _ = 1 := by rw [IsUnit.mul_val_inv, IsUnit.mul_val_inv, one_mul]
  ·
    have h5 := congrArg ((pr T' q).appInf (U i) (U j)) (hmij i j)
    have nb' : ∀ r : R, (pr T' q).appInf (U i) (U j) (baseFun q (U i ⊓ U j) r) =
        baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j) r := fun r => app_baseFun q (pr T' q) (U i ⊓ U j) r
    simp only [map_mul, nb', Scheme.Hom.appInf_map_left, Scheme.Hom.appInf_map_right] at h5
    have h6 := (cU _ (mij i j) (hmijU i j)).mul_left_cancel h5

    have vi : (BC T' q).presheaf.map (homOfLE (inf_le_left : (pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j ≤ (pr T' q) ⁻¹ᵁ U i)).op
          ((pr T' q).app (U i) (y i) * ↑(cU ((pr T' q) ⁻¹ᵁ U i) (m i) (hmU i)).unit⁻¹) *
        baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j) (m i) =
        (BC T' q).presheaf.map (homOfLE inf_le_left).op ((pr T' q).app (U i) (y i)) := by
      rw [← map_baseFun ((pr T' q) ≫ q) (inf_le_left : (pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j ≤ (pr T' q) ⁻¹ᵁ U i), ← map_mul,
        mul_assoc, IsUnit.val_inv_mul, mul_one]
    have vj : (BC T' q).presheaf.map (homOfLE (inf_le_right : (pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j ≤ (pr T' q) ⁻¹ᵁ U j)).op
          ((pr T' q).app (U j) (y j) * ↑(cU ((pr T' q) ⁻¹ᵁ U j) (m j) (hmU j)).unit⁻¹) *
        baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j) (m j) =
        (BC T' q).presheaf.map (homOfLE inf_le_right).op ((pr T' q).app (U j) (y j)) := by
      rw [← map_baseFun ((pr T' q) ≫ q) (inf_le_right : (pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j ≤ (pr T' q) ⁻¹ᵁ U j), ← map_mul,
        mul_assoc, IsUnit.val_inv_mul, mul_one]
    have hcc : IsUnit (baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j) (m i) *
        baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j) (m j)) := (cU _ _ (hmU i)).mul (cU _ _ (hmU j))
    refine hcc.mul_right_cancel ?_
    linear_combination (baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j) (m j) *
        (pr T' q).appInf (U i) (U j) (t₁ i j)) * vi -
      (baseFun ((pr T' q) ≫ q) ((pr T' q) ⁻¹ᵁ U i ⊓ (pr T' q) ⁻¹ᵁ U j) (m i) * (pr T' q).appInf (U i) (U j) (t₂ i j)) * vj + h6

end Spread

theorem core {R : Type u} [CommRing R] {B : Scheme.{u}} (q : B ⟶ Spec (.of R))
    [CompactSpace B] [QuasiSeparatedSpace B]
    (M : Submonoid R) (T : Type u) [CommRing T] [Algebra R T] [IsLocalization M T]
    (L₁ L₂ : B.Modules) (h₁ : IsInvertible L₁) (h₂ : IsInvertible L₂)
    (e : (Scheme.Modules.pullback (pr T q)).obj L₁ ≅ (Scheme.Modules.pullback (pr T q)).obj L₂) :
    ∃ m ∈ M, ∀ (T' : Type u) [CommRing T'] [Algebra R T'], IsUnit (algebraMap R T' m) →
      Nonempty ((Scheme.Modules.pullback (pr T' q)).obj L₁ ≅ (Scheme.Modules.pullback (pr T' q)).obj L₂) := by
  obtain ⟨n, U, hUaff, hUcov, a, b, ha, hb⟩ := h₁.exists_fin_affine_cover_isFrameOn₂ h₂
  obtain ⟨u, hu, hcoc⟩ := exists_units_of_iso (pr T q) ha hb e
  obtain ⟨m, hm, H⟩ := spread M T q hUaff (IsFrameOn.trans ha) (IsFrameOn.trans hb) u hu hcoc
  refine ⟨m, hm, fun T' _ _ hmT' => ?_⟩
  obtain ⟨v, hv, hvcoc⟩ := H T' hmT'

  refine nonempty_iso_of_units (pr T' q) (ι := ULift.{u} (Fin n)) (U := fun k => U k.down) ?_
    (a := fun k => a k.down) (b := fun k => b k.down) (fun k => ha k.down) (fun k => hb k.down)
    (fun k => v k.down) (fun k => hv k.down) (fun i j => hvcoc i.down j.down)
  rw [← hUcov, iSup_ulift]

lemma nonempty_iso_pullback_of_fac {X Y Z : Scheme.{u}} (h : X ⟶ Y) (π : Y ⟶ Z) (p : X ⟶ Z) (hp : h ≫ π = p)
    (L₁ L₂ : Z.Modules)
    (e : Nonempty ((Scheme.Modules.pullback π).obj L₁ ≅ (Scheme.Modules.pullback π).obj L₂)) :
    Nonempty ((Scheme.Modules.pullback p).obj L₁ ≅ (Scheme.Modules.pullback p).obj L₂) := by
  obtain ⟨e⟩ := e
  exact ⟨((Scheme.Modules.pullbackComp h π).app L₁ ≪≫ (Scheme.Modules.pullbackCongr hp).app L₁).symm ≪≫
    (Scheme.Modules.pullback h).mapIso e ≪≫
    ((Scheme.Modules.pullbackComp h π).app L₂ ≪≫ (Scheme.Modules.pullbackCongr hp).app L₂)⟩

end LimitIso

theorem solution
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S))
    [QuasiCompact f] [QuasiSeparated f]
    (𝔭 : Ideal S) [𝔭.IsPrime] (r₀ : S) (hr₀ : r₀ ∉ 𝔭)
    (ψ : Localization.Away r₀ →+* Localization.AtPrime 𝔭)
    (hψ : ψ.comp (algebraMap S (Localization.Away r₀)) = algebraMap S (Localization.AtPrime 𝔭))
    (𝓛₁ 𝓛₂ : (Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀))))).Modules)
    (h₁ : Scheme.Modules.IsInvertible 𝓛₁) (h₂ : Scheme.Modules.IsInvertible 𝓛₂)
    (hiso : Nonempty
      ((Scheme.Modules.pullback
          (Limits.pullback.lift
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
            (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
              Spec.map (CommRingCat.ofHom ψ))
            (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) :
            Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ⟶
              Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀)))))).obj 𝓛₁ ≅
       (Scheme.Modules.pullback
          (Limits.pullback.lift
            (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
            (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
              Spec.map (CommRingCat.ofHom ψ))
            (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]))).obj 𝓛₂)) :
    ∃ (r : S) (_ : r ∉ 𝔭) (ψr : Localization.Away r₀ →+* Localization.Away r)
      (hψr : ψr.comp (algebraMap S (Localization.Away r₀)) = algebraMap S (Localization.Away r)),
      Nonempty
        ((Scheme.Modules.pullback
            (Limits.pullback.lift
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))))
              (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) ≫
                Spec.map (CommRingCat.ofHom ψr))
              (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψr]) :
              Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) ⟶
                Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀)))))).obj 𝓛₁ ≅
         (Scheme.Modules.pullback
            (Limits.pullback.lift
              (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))))
              (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r)))) ≫
                Spec.map (CommRingCat.ofHom ψr))
              (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψr]))).obj 𝓛₂) := by
  classical

  haveI : CompactSpace ↥(Spec (CommRingCat.of (Localization.Away r₀))) :=
    (inferInstance : CompactSpace (PrimeSpectrum (Localization.Away r₀)))
  haveI : CompactSpace
      ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀))))) :=
    QuasiCompact.compactSpace_of_compactSpace
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀)))))
  haveI : QuasiSeparatedSpace
      ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀))))) :=
    (quasiSeparated_iff_quasiSeparatedSpace
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀)))))).mp inferInstance

  letI algRT : Algebra (Localization.Away r₀) (Localization.AtPrime 𝔭) := ψ.toAlgebra
  haveI : IsScalarTower S (Localization.Away r₀) (Localization.AtPrime 𝔭) :=
    IsScalarTower.of_algebraMap_eq (fun x => (congrArg (fun g : S →+* Localization.AtPrime 𝔭 => g x) hψ).symm)
  haveI hM : IsLocalization ((𝔭.primeCompl).map (algebraMap S (Localization.Away r₀))) (Localization.AtPrime 𝔭) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away r₀) (Localization.AtPrime 𝔭)
      (Submonoid.powers r₀) 𝔭.primeCompl (Submonoid.powers_le.2 (show r₀ ∈ 𝔭.primeCompl from hr₀))

  let hcmp : LimitIso.BC (Localization.AtPrime 𝔭)
        (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀))))) ⟶
      Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) :=
    Limits.pullback.lift
      (LimitIso.pr (Localization.AtPrime 𝔭) (Limits.pullback.snd f _) ≫ Limits.pullback.fst f _)
      (Limits.pullback.snd _ _)
      (by
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, Limits.pullback.condition, Category.assoc,
          ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact congrArg CommRingCat.ofHom hψ)
  have hfac : hcmp ≫ Limits.pullback.lift
      (Limits.pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))))
      (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.AtPrime 𝔭)))) ≫
        Spec.map (CommRingCat.ofHom ψ))
      (by rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]) =
      LimitIso.pr (Localization.AtPrime 𝔭) (Limits.pullback.snd f _) := by
    apply Limits.pullback.hom_ext
    · simp only [hcmp, Category.assoc, Limits.pullback.lift_fst]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, Limits.pullback.lift_snd,
        Limits.pullback.condition]
  obtain ⟨e⟩ := LimitIso.nonempty_iso_pullback_of_fac hcmp _ _ hfac 𝓛₁ 𝓛₂ hiso
  obtain ⟨m, hm, H⟩ := LimitIso.core
    (Limits.pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r₀)))))
    ((𝔭.primeCompl).map (algebraMap S (Localization.Away r₀))) (Localization.AtPrime 𝔭) 𝓛₁ 𝓛₂ h₁ h₂ e
  obtain ⟨s, hs, rfl⟩ := Submonoid.mem_map.1 hm
  have hr : r₀ * s ∉ 𝔭 := fun h => (‹𝔭.IsPrime›.mem_or_mem h).elim hr₀ hs

  have hunit₀ : IsUnit (algebraMap S (Localization.Away (r₀ * s)) r₀) :=
    IsLocalization.Away.isUnit_of_dvd (x := r₀ * s) (dvd_mul_right r₀ s)
  let ψr : Localization.Away r₀ →+* Localization.Away (r₀ * s) := IsLocalization.Away.lift r₀ hunit₀
  have hψr : ψr.comp (algebraMap S (Localization.Away r₀)) = algebraMap S (Localization.Away (r₀ * s)) :=
    IsLocalization.Away.lift_comp r₀ hunit₀
  letI algRT' : Algebra (Localization.Away r₀) (Localization.Away (r₀ * s)) := ψr.toAlgebra
  have hunit : IsUnit (algebraMap (Localization.Away r₀) (Localization.Away (r₀ * s))
      (algebraMap S (Localization.Away r₀) s)) := by
    change IsUnit (ψr (algebraMap S (Localization.Away r₀) s))
    rw [IsLocalization.Away.lift_eq]
    exact IsLocalization.Away.isUnit_of_dvd (x := r₀ * s) (dvd_mul_left s r₀)
  obtain ⟨e'⟩ := H (Localization.Away (r₀ * s)) hunit
  refine ⟨r₀ * s, hr, ψr, hψr, ?_⟩
  refine LimitIso.nonempty_iso_pullback_of_fac (Limits.pullback.lift _ (Limits.pullback.snd f _) ?_)
    (LimitIso.pr (Localization.Away (r₀ * s)) (Limits.pullback.snd f _)) _ (Limits.pullback.lift_fst _ _ _)
    𝓛₁ 𝓛₂ ⟨e'⟩
  rw [Limits.pullback.lift_snd]

end

end S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_nonempty_iso_pullback_away_of_nonempty_iso_pullback_atPrime (solution)
