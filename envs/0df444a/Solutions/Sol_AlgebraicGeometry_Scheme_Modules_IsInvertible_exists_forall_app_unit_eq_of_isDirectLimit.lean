-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_forall_app_unit_eq_of_isDirectLimit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/66af495d-5df1-5049-bfcb-b87e7d9160a7

import Mathlib
import Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isAffineOpen_iSup_eq_top_isFrameOn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Modules.Hom.app_smul quasiSeparatedSpace_of_quasiSeparated Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom.comp_app Scheme.Modules.Hom QuasiCompact Spec Spec.map Scheme Scheme.Modules.Hom.id_app Scheme.Modules.Hom.app QuasiCompact.compactSpace_of_compactSpace Scheme.Hom.comp_app Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules QuasiSeparated Scheme.Modules.conjugateEquiv_pullbackComp_inv Scheme.Modules.map_smul Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.IsFrameOn Scheme.Modules.pullbackLocalSection Scheme.Modules.map_pullbackLocalSection Scheme.Modules.IsFrameOn.pullbackLocalSection Scheme.exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback Scheme.exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback Scheme.Modules.IsInvertible.exists_isAffineOpen_iSup_eq_top_isFrameOn"
namespace Scheme
p2m_export "AlgebraicGeometry.Scheme" "Modules.Hom.app_smul Modules.pullback Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app Hom.comp_app Modules.pullbackPushforwardAdjunction Modules Opens Modules.conjugateEquiv_pullbackComp_inv Modules.map_smul Modules.pullbackComp Modules.IsInvertible Modules.IsFrameOn Modules.pullbackLocalSection Modules.map_pullbackLocalSection Modules.IsFrameOn.pullbackLocalSection exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback Modules.IsInvertible.exists_isAffineOpen_iSup_eq_top_isFrameOn"
namespace Modules
p2m_export "AlgebraicGeometry.Scheme.Modules" "Hom.app_smul pushforwardComp pullback presheaf Hom.comp_app Hom pushforward_map_app Hom.id_app Hom.app isSheaf pullbackPushforwardAdjunction conjugateEquiv_pullbackComp_inv map_smul pullbackComp IsInvertible IsFrameOn pullbackLocalSection pullbackLocalSection_smul map_pullbackLocalSection IsFrameOn.pullbackLocalSection IsInvertible.exists_isAffineOpen_iSup_eq_top_isFrameOn"
p2m_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

theorem pullbackComp_inv_app_app_pullbackLocalSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).inv.app M).app ((f ≫ g) ⁻¹ᵁ U) (pullbackLocalSection (f ≫ g) m) =
      pullbackLocalSection f (pullbackLocalSection g m) := by
  have h1 := CategoryTheory.unit_conjugateEquiv
    ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
    (pullbackPushforwardAdjunction (f ≫ g)) (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h1
  have h2 := congrArg (fun k => Scheme.Modules.Hom.app k U m) h1
  dsimp only at h2
  erw [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.comp_app] at h2
  erw [CategoryTheory.comp_apply, CategoryTheory.comp_apply, CategoryTheory.comp_apply] at h2

  exact h2.symm

theorem pullbackComp_hom_app_app_pullbackLocalSection {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp f g).hom.app M).app (f ⁻¹ᵁ (g ⁻¹ᵁ U))
        (pullbackLocalSection f (pullbackLocalSection g m)) =
      pullbackLocalSection (f ≫ g) m := by
  rw [← pullbackComp_inv_app_app_pullbackLocalSection]
  change (((Scheme.Modules.pullbackComp f g).inv.app M) ≫ ((Scheme.Modules.pullbackComp f g).hom.app M)).app
    ((f ≫ g) ⁻¹ᵁ U) (pullbackLocalSection (f ≫ g) m) = _
  rw [Iso.inv_hom_id_app, Scheme.Modules.Hom.id_app]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace SecSpread17

section Res
variable {Y : Scheme.{u}} (N : Y.Modules)

noncomputable abbrev res {U V : Y.Opens} (h : V ≤ U) (x : Γ(N, U)) : Γ(N, V) := N.presheaf.map (homOfLE h).op x

noncomputable abbrev resF {U V : Y.Opens} (h : V ≤ U) (x : Γ(Y, U)) : Γ(Y, V) := Y.presheaf.map (homOfLE h).op x

theorem res_res {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(N, U)) :
    res N h₂ (res N h₁ x) = res N (h₂.trans h₁) x := by
  simp only [res, ← CategoryTheory.comp_apply, ← N.presheaf.map_comp]; rfl

theorem resF_resF {U V W : Y.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(Y, U)) :
    resF (Y := Y) h₂ (resF h₁ x) = resF (h₂.trans h₁) x := by
  simp only [resF, ← CategoryTheory.comp_apply, ← Y.presheaf.map_comp]; rfl

theorem res_rfl {U : Y.Opens} (x : Γ(N, U)) : res N (le_refl U) x = x := by
  simp only [res]
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [this, N.presheaf.map_id]; rfl

theorem res_smul {U V : Y.Opens} (h : V ≤ U) (g : Γ(Y, U)) (x : Γ(N, U)) :
    res N h (g • x) = resF h g • res N h x :=
  Scheme.Modules.map_smul N _ g x

theorem resF_mul {U V : Y.Opens} (h : V ≤ U) (g g' : Γ(Y, U)) : resF (Y := Y) h (g * g') = resF h g * resF h g' :=
  map_mul _ g g'

theorem app_res {N' : Y.Modules} (θ : N ⟶ N') {U V : Y.Opens} (h : V ≤ U) (x : Γ(N, U)) :
    θ.app V (res N h x) = res N' h (θ.app U x) := by
  have := (θ.mapPresheaf).naturality (homOfLE h).op
  exact congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(N, U) → Γ(N', V))) this) x

end Res

theorem appF_resF {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) {U V : Y.Opens} (h : V ≤ U) (x : Γ(Y, U)) :
    f.app V (resF h x) = resF (f.preimage_mono h) (f.app U x) := by
  have := f.naturality (homOfLE h).op
  exact congrFun (congrArg (fun k => (ConcreteCategory.hom k : Γ(Y, U) → Γ(Y', f ⁻¹ᵁ V))) this) x

theorem res_pullbackLocalSection {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) {L : Y.Modules} {U V : Y.Opens} (h : V ≤ U) (x : Γ(L, U)) :
    res ((Scheme.Modules.pullback f).obj L) (f.preimage_mono h) (Scheme.Modules.pullbackLocalSection f x) =
      Scheme.Modules.pullbackLocalSection f (res L h x) :=
  Scheme.Modules.map_pullbackLocalSection f (homOfLE h) x

section Coeff
variable {Y : Scheme.{u}} (N : Y.Modules)

theorem exists_coeff {V : Y.Opens} (m : Γ(N, V)) (hm : Scheme.Modules.IsFrameOn m V) (σ : Γ(N, ⊤)) :
    ∃ a : Γ(Y, V), a • m = res N le_top σ := by
  obtain ⟨a, ha, -⟩ := hm.existsUnique le_rfl le_rfl (res N le_top σ)
  refine ⟨a, ?_⟩
  rw [← ha]
  show a • m = a • res N (le_refl V) m
  rw [res_rfl]

theorem coeff_unique {U V : Y.Opens} (m : Γ(N, U)) (hm : Scheme.Modules.IsFrameOn m U) (h : V ≤ U)
    (a b : Γ(Y, V)) (hab : a • res N h m = b • res N h m) : a = b :=
  (hm.bijective h h).1 hab

end Coeff

end SecSpread17

namespace SecSpread17

theorem mapF_eq {Y : Scheme.{u}} {U V : Y.Opens} (f f' : op U ⟶ op V) (x : Γ(Y, U)) :
    Y.presheaf.map f x = Y.presheaf.map f' x := by
  have : f = f' := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this]

theorem mapM_eq {Y : Scheme.{u}} (N : Y.Modules) {U V : Y.Opens} (f f' : op U ⟶ op V) (x : Γ(N, U)) :
    N.presheaf.map f x = N.presheaf.map f' x := by
  have : f = f' := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [this]

theorem appF_resF_eq {Y Y' : Scheme.{u}} (f : Y' ⟶ Y) {U U' : Y.Opens} (h : U' ≤ U) (h' : U ≤ U') (x : Γ(Y, U)) :
    f.app U' (resF h x) = resF (f.preimage_mono h) (f.app U x) :=
  appF_resF f h x

theorem comp_appF {X Y Z : Scheme.{u}} (c : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (x : Γ(Z, U)) :
    (c ≫ g).app U x = c.app (g ⁻¹ᵁ U) (g.app U x) := by
  rw [Scheme.Hom.comp_app]; rfl

theorem resF_rfl {Y : Scheme.{u}} {U : Y.Opens} (x : Γ(Y, U)) : resF (le_refl U) x = x := by
  simp only [resF]
  have : (homOfLE (le_refl U)).op = 𝟙 (op U) := rfl
  rw [this, Y.presheaf.map_id]; rfl

theorem appF_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f') (U : Y.Opens) (x : Γ(Y, U)) :
    f.app U x = resF (by subst e; exact le_rfl) (f'.app U x) := by
  subst e
  exact (resF_rfl _).symm

theorem mapF_eqToHom {Y : Scheme.{u}} {U V : Y.Opens} (e : U = V) (y : Γ(Y, V)) :
    Y.presheaf.map (eqToHom e).op y = resF e.le y :=
  mapF_eq _ _ y

theorem appF_congr' {X Y : Scheme.{u}} {f f' : X ⟶ Y} (e : f = f') (U : Y.Opens) (x : Γ(Y, U))
    (h : f ⁻¹ᵁ U ≤ f' ⁻¹ᵁ U) : f.app U x = resF h (f'.app U x) := by
  subst e
  exact (resF_rfl _).symm

end SecSpread17

namespace SecSpread17

open _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit.AlgebraicGeometry.Scheme.Modules in

theorem final_piece {XR X₂ X : Scheme.{u}} (c : XR ⟶ X₂) (P : X₂ ⟶ X) (M : X.Modules) (U : X.Opens) (V : X₂.Opens)
    (hV : V ≤ P ⁻¹ᵁ U) (m : Γ(M, U)) (τb : Γ(X₂, V))
    (tk : Γ((Scheme.Modules.pullback P).obj M, ⊤))
    (ht : res ((Scheme.Modules.pullback P).obj M) le_top tk = τb • res _ hV (pullbackLocalSection P m))
    (ak : Γ(XR, (c ≫ P) ⁻¹ᵁ U)) (hak : c.app V τb = resF (c.preimage_mono hV) ak)
    (sk : Γ((Scheme.Modules.pullback (c ≫ P)).obj M, ⊤))
    (ha : ak • pullbackLocalSection (c ≫ P) m = res _ le_top sk) :
    res ((Scheme.Modules.pullback (c ≫ P)).obj M) (le_top : c ⁻¹ᵁ V ≤ ⊤)
        (((Scheme.Modules.pullbackComp c P).app M).hom.app ⊤ (pullbackLocalSection c tk)) =
      res ((Scheme.Modules.pullback (c ≫ P)).obj M) (le_top : c ⁻¹ᵁ V ≤ ⊤) sk := by
  have s1 := app_res ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback P).obj M))
    ((Scheme.Modules.pullbackComp c P).app M).hom (le_top : c ⁻¹ᵁ V ≤ ⊤) (pullbackLocalSection c tk)
  have s2 : res ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback P).obj M)) (le_top : c ⁻¹ᵁ V ≤ ⊤)
      (pullbackLocalSection c tk) = pullbackLocalSection c (res _ (le_top : V ≤ ⊤) tk) :=
    res_pullbackLocalSection c le_top tk
  have s3 : pullbackLocalSection c (res ((Scheme.Modules.pullback P).obj M) hV (pullbackLocalSection P m)) =
      res _ (c.preimage_mono hV) (pullbackLocalSection c (pullbackLocalSection P m)) :=
    (res_pullbackLocalSection c hV _).symm
  have s4 : ((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ (P ⁻¹ᵁ U))
      (pullbackLocalSection c (pullbackLocalSection P m)) = pullbackLocalSection (c ≫ P) m :=
    Scheme.Modules.pullbackComp_hom_app_app_pullbackLocalSection c P M U m
  have s5 : res ((Scheme.Modules.pullback (c ≫ P)).obj M) (le_top : c ⁻¹ᵁ V ≤ ⊤) sk =
      res _ (c.preimage_mono hV) (res _ le_top sk) := (res_res _ _ _ _).symm
  calc _ = ((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ V)
          (res ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback P).obj M)) (le_top : c ⁻¹ᵁ V ≤ ⊤)
            (pullbackLocalSection c tk)) := s1.symm
    _ = ((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ V)
          (pullbackLocalSection c (res _ (le_top : V ≤ ⊤) tk)) := by rw [s2]
    _ = ((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ V)
          (pullbackLocalSection c (τb • res _ hV (pullbackLocalSection P m))) := by rw [ht]
    _ = ((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ V)
          (c.app V τb • pullbackLocalSection c (res _ hV (pullbackLocalSection P m))) := by rw [pullbackLocalSection_smul]
    _ = c.app V τb • ((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ V)
          (pullbackLocalSection c (res _ hV (pullbackLocalSection P m))) := Scheme.Modules.Hom.app_smul _ _ _
    _ = c.app V τb • ((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ V)
          (res _ (c.preimage_mono hV) (pullbackLocalSection c (pullbackLocalSection P m))) := by rw [s3]; rfl
    _ = c.app V τb • res _ (c.preimage_mono hV)
          (((Scheme.Modules.pullbackComp c P).app M).hom.app (c ⁻¹ᵁ (P ⁻¹ᵁ U))
            (pullbackLocalSection c (pullbackLocalSection P m))) := by rw [app_res]
    _ = c.app V τb • res _ (c.preimage_mono hV) (pullbackLocalSection (c ≫ P) m) := by rw [s4]
    _ = resF (c.preimage_mono hV) ak • res _ (c.preimage_mono hV) (pullbackLocalSection (c ≫ P) m) := by rw [hak]
    _ = res _ (c.preimage_mono hV) (ak • pullbackLocalSection (c ≫ P) m) := (res_smul _ _ _ _).symm
    _ = res _ (c.preimage_mono hV) (res _ le_top sk) := by rw [ha]; rfl
    _ = _ := res_res _ _ _ _

end SecSpread17

open SecSpread17 _root_.AlgebraicGeometry.Scheme.Modules _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit.AlgebraicGeometry.Scheme.Modules in
theorem solution
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
    {G : ι → Type u} [∀ i, CommRing (G i)] (φ : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(φ i j h)]
    {R : Type u} [CommRing R] (g : ∀ i, G i →+* R)
    (hR : IsDirectLimit (fun i j h => ⇑(φ i j h)) fun i => ⇑(g i))
    (i : ι) {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of (G i))) [QuasiCompact fX] [QuasiSeparated fX]
    {XR : Scheme.{u}} (p : XR ⟶ X) (q : XR ⟶ Spec (CommRingCat.of R))
    (hp : IsPullback p q fX (Spec.map (CommRingCat.ofHom (g i))))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    {κ : Type u} [Finite κ] (s : κ → Γ((Scheme.Modules.pullback p).obj M, ⊤)) :
    ∃ (j : ι) (hij : i ≤ j)
      (t : κ → Γ((Scheme.Modules.pullback
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj M, ⊤)),
      ∀ (c : XR ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j hij)))),
        c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = p →
        c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j hij))) = q ≫ Spec.map (CommRingCat.ofHom (g j)) →
        ∃ e : (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback
              (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j hij))))).obj M) ≅
            (Scheme.Modules.pullback p).obj M,
          ∀ k, e.hom.app ⊤ ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app _).app ⊤) (t k)) = s k := by
  classical
  haveI : CompactSpace ↥X := QuasiCompact.compactSpace_of_compactSpace fX
  haveI : QuasiSeparatedSpace ↥X := quasiSeparatedSpace_of_quasiSeparated fX

  obtain ⟨n, W, hWaff, hWcov, m, hm⟩ :=
    AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isAffineOpen_iSup_eq_top_isFrameOn M hM
  have hWc : ∀ l, IsCompact (W l : Set X) := fun l => (hWaff l).isCompact
  have hWWc : ∀ l l', IsCompact ((W l ⊓ W l' : X.Opens) : Set X) := fun l l' =>
    QuasiSeparatedSpace.inter_isCompact _ _ (W l).2 (hWc l) (W l').2 (hWc l')

  have htrans : ∀ l l', ∃ u : Γ(X, W l ⊓ W l'), u • res M inf_le_left (m l) = res M inf_le_right (m l') := fun l l' => by
    obtain ⟨v, hv, -⟩ := (hm l).existsUnique inf_le_left inf_le_left (res M inf_le_right (m l'))
    exact ⟨v, hv⟩
  choose u hu using htrans

  have hmR : ∀ l, IsFrameOn (pullbackLocalSection p (m l)) (p ⁻¹ᵁ W l) := fun l =>
    AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection p (hm l)
  have hcoef : ∀ k l, ∃ a : Γ(XR, p ⁻¹ᵁ W l),
      a • pullbackLocalSection p (m l) = res ((Scheme.Modules.pullback p).obj M) le_top (s k) := fun k l =>
    exists_coeff _ _ (hmR l) (s k)
  choose a ha using hcoef

  have hcocR : ∀ k l l',
      resF (p.preimage_mono (inf_le_left : W l ⊓ W l' ≤ W l)) (a k l) =
        resF (p.preimage_mono (inf_le_right : W l ⊓ W l' ≤ W l')) (a k l') * p.app (W l ⊓ W l') (u l l') := by
    intro k l l'
    apply coeff_unique _ _ (hmR l) (p.preimage_mono inf_le_left)
    have e1 : res ((Scheme.Modules.pullback p).obj M) (p.preimage_mono (inf_le_left : W l ⊓ W l' ≤ W l))
        (pullbackLocalSection p (m l)) = pullbackLocalSection p (res M inf_le_left (m l)) :=
      res_pullbackLocalSection p inf_le_left (m l)
    have e2 : res ((Scheme.Modules.pullback p).obj M) (p.preimage_mono (inf_le_right : W l ⊓ W l' ≤ W l'))
        (pullbackLocalSection p (m l')) = pullbackLocalSection p (res M inf_le_right (m l')) :=
      res_pullbackLocalSection p inf_le_right (m l')
    rw [← res_smul, ha, res_res, mul_smul, e1, ← pullbackLocalSection_smul, hu, ← e2, ← res_smul, ha, res_res]

  obtain ⟨j₁, hij₁, b, hb⟩ :=
    AlgebraicGeometry.Scheme.exists_forall_app_eq_of_isCompact_of_isDirectLimit_of_isPullback φ g hR i fX p q hp
      (κ := κ × ULift.{u} (Fin n)) (fun kl => W kl.2) (fun kl => hWc kl.2) (fun kl => a kl.1 kl.2)

  have hagree : ∀ (c : XR ⟶ Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))),
      c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁))) = p →
      c ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁))) = q ≫ Spec.map (CommRingCat.ofHom (g j₁)) →
      ∀ kll : κ × ULift.{u} (Fin n) × ULift.{u} (Fin n),
        c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ (W kll.2.1 ⊓ W kll.2.2))
          (resF ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))).preimage_mono inf_le_left) (b (kll.1, kll.2.1))) =
        c.app ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ (W kll.2.1 ⊓ W kll.2.2))
          (resF ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))).preimage_mono inf_le_right) (b (kll.1, kll.2.2)) *
            (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))).app (W kll.2.1 ⊓ W kll.2.2) (u kll.2.1 kll.2.2)) := by
    intro c hc1 hc2 kll
    obtain ⟨k, l, l'⟩ := kll
    dsimp only
    subst hc1
    have hb1 : c.app _ (b (k, l)) = a k l := by
      rw [← hb c rfl hc2 (k, l) rfl, mapF_eqToHom]; exact (resF_rfl _).symm
    have hb2 : c.app _ (b (k, l')) = a k l' := by
      rw [← hb c rfl hc2 (k, l') rfl, mapF_eqToHom]; exact (resF_rfl _).symm
    rw [map_mul, appF_resF, appF_resF, ← comp_appF, hb1, hb2]
    exact hcocR k l l'
  obtain ⟨j₂, hj₁j₂, hcoc₂⟩ :=
    AlgebraicGeometry.Scheme.exists_forall_app_eq_app_of_isCompact_of_isDirectLimit_of_isPullback φ g hR i fX p q hp j₁ hij₁
      (κ := κ × ULift.{u} (Fin n) × ULift.{u} (Fin n)) (fun kll => W kll.2.1 ⊓ W kll.2.2) (fun kll => hWWc kll.2.1 kll.2.2)
      (fun kll => resF ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))).preimage_mono inf_le_left)
        (b (kll.1, kll.2.1)))
      (fun kll => resF ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))).preimage_mono inf_le_right)
        (b (kll.1, kll.2.2)) *
        (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))).app (W kll.2.1 ⊓ W kll.2.2) (u kll.2.1 kll.2.2))
      hagree
  have hij₂ : i ≤ j₂ := hij₁.trans hj₁j₂

  have hφ : (φ j₁ j₂ hj₁j₂).comp (φ i j₁ hij₁) = φ i j₂ hij₂ :=
    RingHom.ext fun x => DirectedSystem.map_map (f := fun i j h => ⇑(φ i j h)) hij₁ hj₁j₂ x
  obtain ⟨τ, hτ1, hτ2⟩ : ∃ τ : Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))) ⟶
      Limits.pullback fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁))),
      τ ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁))) =
        Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))) ∧
      τ ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁))) =
        Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))) ≫ Spec.map (CommRingCat.ofHom (φ j₁ j₂ hj₁j₂)) := by
    refine ⟨Limits.pullback.lift (Limits.pullback.fst _ _)
      (Limits.pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (φ j₁ j₂ hj₁j₂))) ?_,
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
    rw [Limits.pullback.condition, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have hcocτ := hcoc₂ τ hτ1 hτ2

  have hV : ∀ l, τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l) ≤ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ W l := fun l =>
    (congrArg (fun f => f ⁻¹ᵁ W l) hτ1 : (τ ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l = (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ W l).le
  have hVV : ∀ l l', τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l) ⊓ τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l') ≤ τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ (W l ⊓ W l')) :=
    fun l l' x hx => hx
  have hVV2 : ∀ l l', τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l) ⊓ τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l') ≤ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ (W l ⊓ W l') :=
    fun l l' => (hVV l l').trans ((congrArg (fun f => f ⁻¹ᵁ (W l ⊓ W l')) hτ1 :
      (τ ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ (W l ⊓ W l') = (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ (W l ⊓ W l')).le)
  have hVcov : (⨆ l, τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l)) = ⊤ :=
    τ.iSup_preimage_eq_top ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))).iSup_preimage_eq_top hWcov)

  have hcoc2 : ∀ k l l',
      resF inf_le_left (τ.app _ (b (k, l))) =
        resF inf_le_right (τ.app _ (b (k, l'))) * resF (hVV2 l l') ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))).app (W l ⊓ W l') (u l l')) := by
    intro k l l'
    have h0 := hcocτ (k, l, l')
    dsimp only at h0
    have hτV : τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ (W l ⊓ W l')) ≤ (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ (W l ⊓ W l') :=
      (congrArg (fun f => f ⁻¹ᵁ (W l ⊓ W l')) hτ1 : (τ ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ (W l ⊓ W l') = (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ (W l ⊓ W l')).le
    rw [map_mul, appF_resF, appF_resF, ← comp_appF,
      appF_congr' hτ1 (W l ⊓ W l') (u l l') hτV] at h0
    have h1 := congrArg (resF (hVV l l')) h0
    have h2 : resF (hVV l l') (resF hτV ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))).app (W l ⊓ W l') (u l l'))) =
        resF (hVV2 l l') ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))).app (W l ⊓ W l') (u l l')) := resF_resF _ _ _
    simp only [resF_mul, resF_resF] at h1
    exact h1.trans (congrArg (HMul.hMul _) h2)

  have hfr : ∀ l l',
      res ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M) ((inf_le_right).trans (hV l'))
          (pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (m l')) =
        resF (hVV2 l l') ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))).app (W l ⊓ W l') (u l l')) •
          res ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M) ((inf_le_left).trans (hV l))
            (pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (m l)) := by
    intro l l'
    rw [← res_res _ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))).preimage_mono inf_le_right) (hVV2 l l'),
      res_pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (inf_le_right : W l ⊓ W l' ≤ W l') (m l'), ← hu,
      pullbackLocalSection_smul, res_smul, ← res_pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (inf_le_left : W l ⊓ W l' ≤ W l) (m l), res_res]

  have hcompat : ∀ k, TopCat.Presheaf.IsCompatible ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M).presheaf
      (fun l => τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l))
      (fun l => τ.app _ (b (k, l)) •
        res ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M) (hV l) (pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (m l))) := by
    intro k l l'
    show res _ inf_le_left (τ.app _ (b (k, l)) • res _ (hV l) (pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (m l))) =
      res _ inf_le_right (τ.app _ (b (k, l')) • res _ (hV l') (pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (m l')))
    rw [res_smul, res_smul, res_res, res_res, hfr, ← mul_smul, ← hcoc2]

  have hglue : ∀ k, ∃ tk : Γ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M, ⊤),
      ∀ l, res _ le_top tk = τ.app _ (b (k, l)) •
        res ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M) (hV l) (pullbackLocalSection (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) (m l)) := by
    intro k
    obtain ⟨tk, htk, -⟩ := TopCat.Sheaf.existsUnique_gluing'
      (⟨((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M).presheaf, ((Scheme.Modules.pullback (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M).isSheaf⟩ : TopCat.Sheaf Ab _)
      (fun l => τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l)) ⊤ (fun l => homOfLE le_top) (by rw [hVcov]) _ (hcompat k)
    exact ⟨tk, htk⟩
  choose t ht using hglue

  refine ⟨j₂, hij₂, t, ?_⟩
  intro c hc1 hc2
  subst hc1
  refine ⟨(Scheme.Modules.pullbackComp c (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).app M, fun k => ?_⟩
  have hg : (g j₂).comp (φ j₁ j₂ hj₁j₂) = g j₁ := RingHom.ext fun x => hR.compatibility _ _ hj₁j₂ x
  have H1 : (c ≫ τ) ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁))) = c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))) := by rw [Category.assoc, hτ1]
  have H2 : (c ≫ τ) ≫ Limits.pullback.snd fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁))) =
      q ≫ Spec.map (CommRingCat.ofHom (g j₁)) := by
    rw [Category.assoc, hτ2, ← Category.assoc, hc2, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]

  have hcoefR : ∀ l, c.app _ (τ.app _ (b (k, l))) =
      resF (show c ⁻¹ᵁ (τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l)) ≤ (c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ W l from
        c.preimage_mono (hV l)) (a k l) := by
    intro l
    have e : (c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) ⁻¹ᵁ W l = (c ≫ τ) ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l) :=
      (congrArg (fun f => f ⁻¹ᵁ W l) H1).symm
    have h0 := hb (c ≫ τ) H1 H2 (k, l) e
    rw [mapF_eqToHom, comp_appF] at h0
    rw [← h0, resF_resF]
    exact (resF_rfl _).symm

  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨((Scheme.Modules.pullback (c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M).presheaf,
      ((Scheme.Modules.pullback (c ≫ Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂))))).obj M).isSheaf⟩ : TopCat.Sheaf Ab _)
    (fun l => c ⁻¹ᵁ (τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l))) ⊤ (fun l => homOfLE le_top) (by rw [c.iSup_preimage_eq_top hVcov])
  intro l
  exact final_piece c (Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₂ hij₂)))) M (W l) (τ ⁻¹ᵁ ((Limits.pullback.fst fX (Spec.map (CommRingCat.ofHom (φ i j₁ hij₁)))) ⁻¹ᵁ W l)) (hV l) (m l) (τ.app _ (b (k, l))) (t k) (ht k l)
    (a k l) (hcoefR l) (s k) (ha k l)

end S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_forall_app_unit_eq_of_isDirectLimit (solution)
