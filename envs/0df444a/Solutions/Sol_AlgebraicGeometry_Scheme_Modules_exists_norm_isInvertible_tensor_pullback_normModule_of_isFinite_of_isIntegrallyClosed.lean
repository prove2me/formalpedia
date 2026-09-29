-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/8caa8794-b91e-5938-8a03-93032aee9900

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Definitions.Def_AlgebraicGeometry_ModulesGlueOfCocycle
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isInvertible_glueOfCocycle
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_twist_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_mul_iso_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_glueOfCocycle_trivial_iso_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_pullback_glueOfCocycle_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_iso_glueOfCocycle_app_eq_glueFrame
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_unitCocycle_map_eq_smul_of_isFrameOn
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_mem_and_nonempty_pullback_preimage_iso_unit_of_isFinite
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_normModule_forall_map_eq_norm_smul_of_isFrameOn_preimage
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_isFrameOn_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_exists_isUnit_smul_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_tensorSections
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_refinement_isFrameOn_normModule_map_eq_normFun_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry TopologicalSpace Opposite"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Surjective morphismRestrict_ι Scheme.Modules.pullback Scheme.Hom IsFinite isPullback_morphismRestrict IsIntegral Scheme Flat isIntegral_of_isOpenImmersion Scheme.Hom.preimage_mono Scheme.isBasis_affineOpens IsAffineOpen Scheme.Modules LocallyOfFinitePresentation Scheme.Hom.comp_preimage Scheme.Modules.map_smul Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit Scheme.Modules.normModule Scheme.Modules.tensorSections Scheme.Modules.tensorSections_smul_left Scheme.Modules.tensorSections_smul_right Scheme.Modules.map_homOfLE_tensorSections Scheme.Modules.UnitCocycle Scheme.Modules.isInvertible_glueOfCocycle Scheme.Modules.exists_glueOfCocycle_twist_iso Scheme.Modules.exists_glueOfCocycle_mul_iso_tensor Scheme.Modules.exists_pullback_glueOfCocycle_iso Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame Scheme.Modules.exists_unitCocycle_map_eq_smul_of_isFrameOn Scheme.Modules.IsInvertible.exists_mem_and_nonempty_pullback_preimage_iso_unit_of_isFinite Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit Scheme.Modules.exists_refinement_isFrameOn_normModule_map_eq_normFun_smul Scheme.Modules.UnitCocycle.restrict Scheme.Modules.UnitCocycle.restrict_u Scheme.Modules.UnitCocycle.reindexRestrict Scheme.Modules.UnitCocycle.reindexRestrict_u Scheme.Modules.UnitCocycle.refine"
namespace NormNormal
p2m_open "AlgebraicGeometry"

p2m_open "AlgebraicGeometry.Scheme.Modules"

noncomputable def Nf : ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) (W : Y.Opens), Γ(X, π ⁻¹ᵁ W) → Γ(Y, W) :=
  Classical.choose AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed.{u}

theorem Nf_spec {X Y : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y]
    (hN : ∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) :

    (∀ W : Y.Opens, Nf π W 1 = 1 ∧ ∀ a b : Γ(X, π ⁻¹ᵁ W), Nf π W (a * b) = Nf π W a * Nf π W b) ∧

    (∀ (W W' : Y.Opens) (h : W' ≤ W) (a : Γ(X, π ⁻¹ᵁ W)),
      Nf π W' (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π h)).op a) =
        Y.presheaf.map (homOfLE h).op (Nf π W a)) ∧

    (∀ (W : Y.Opens), IsAffineOpen W →
      letI : Algebra Γ(Y, W) Γ(X, π ⁻¹ᵁ W) := (π.app W).hom.toAlgebra
      ∀ [Module.Free Γ(Y, W) Γ(X, π ⁻¹ᵁ W)] [Module.Finite Γ(Y, W) Γ(X, π ⁻¹ᵁ W)],
      ∀ a : Γ(X, π ⁻¹ᵁ W), Nf π W a = Algebra.norm Γ(Y, W) a) ∧

    (∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g),
      ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
      (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
      ∀ (W : Y.Opens) (a : Γ(X, π ⁻¹ᵁ W)),
        Nf π' (g ⁻¹ᵁ W) (X'.presheaf.map (eqToHom (show π' ⁻¹ᵁ (g ⁻¹ᵁ W) = g' ⁻¹ᵁ (π ⁻¹ᵁ W) by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])).op
          ((g'.app (π ⁻¹ᵁ W)).hom a)) =
        (g.app W).hom (Nf π W a)) :=
  Classical.choose_spec
    AlgebraicGeometry.Scheme.exists_normSections_mul_map_eq_norm_of_isFinite_of_isIntegrallyClosed.{u} π hN

structure Qual {X Y : Scheme.{u}} (π : X ⟶ Y) (L : X.Modules) : Prop where
  intX : IsIntegral X
  intY : IsIntegral Y
  fin : IsFinite π
  surj : Surjective π
  normal : ∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)
  inv : IsInvertible L

variable {X Y : Scheme.{u}} {π : X ⟶ Y} {L : X.Modules}

theorem exists_cover (h : Qual π L) :
    ∃ U : ↥Y → Y.Opens, (∀ y, y ∈ U y) ∧ (∀ y, IsAffineOpen (U y)) ∧
      ∀ y, ∃ s : Γ(L, π ⁻¹ᵁ U y), IsFrameOn s (π ⁻¹ᵁ U y) := by
  haveI := h.fin
  have key : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ IsAffineOpen U ∧ ∃ s : Γ(L, π ⁻¹ᵁ U), IsFrameOn s (π ⁻¹ᵁ U) := by
    intro y
    obtain ⟨V, hyV, ⟨eV⟩⟩ :=
      Scheme.Modules.IsInvertible.exists_mem_and_nonempty_pullback_preimage_iso_unit_of_isFinite π h.inv y
    obtain ⟨U, hUaff, hyU, hUV⟩ := (Opens.isBasis_iff_nbhd.mp (Scheme.isBasis_affineOpens Y)) hyV
    obtain ⟨s, hs⟩ := Scheme.Modules.exists_isFrameOn_of_pullback_iso_unit (M := L) (π ⁻¹ᵁ V) eV
    refine ⟨U, hyU, hUaff, L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hUV)).op s, ?_⟩
    exact (hs.map (homOfLE (Scheme.Hom.preimage_mono π hUV))).mono (Scheme.Hom.preimage_mono π hUV)
  choose U hyU hUaff hs using key
  exact ⟨U, hyU, hUaff, hs⟩

noncomputable def cover (h : Qual π L) : ↥Y → Y.Opens := Classical.choose (exists_cover h)

theorem mem_cover (h : Qual π L) (y : Y) : y ∈ cover h y := (Classical.choose_spec (exists_cover h)).1 y
theorem isAffineOpen_cover (h : Qual π L) (y : Y) : IsAffineOpen (cover h y) :=
  (Classical.choose_spec (exists_cover h)).2.1 y
theorem iSup_cover (h : Qual π L) : ⨆ y, cover h y = ⊤ :=
  top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ⟨y, mem_cover h y⟩
theorem iSup_preimage_cover (h : Qual π L) : ⨆ y, π ⁻¹ᵁ cover h y = ⊤ :=
  top_le_iff.mp fun x _ => Opens.mem_iSup.mpr ⟨π x, mem_cover h (π x)⟩

theorem exists_frames (h : Qual π L) :
    ∃ e : ∀ y : Y, Γ(L, π ⁻¹ᵁ cover h y), ∀ y, IsFrameOn (e y) (π ⁻¹ᵁ cover h y) := by
  choose e he using (Classical.choose_spec (exists_cover h)).2.2
  exact ⟨e, he⟩

noncomputable def frames (h : Qual π L) : ∀ y : Y, Γ(L, π ⁻¹ᵁ cover h y) := Classical.choose (exists_frames h)
theorem isFrameOn_frames (h : Qual π L) (y : Y) : IsFrameOn (frames h y) (π ⁻¹ᵁ cover h y) :=
  Classical.choose_spec (exists_frames h) y

noncomputable def frameCocycle (h : Qual π L) : UnitCocycle (fun y : Y => π ⁻¹ᵁ cover h y) :=
  Classical.choose (Scheme.Modules.exists_unitCocycle_map_eq_smul_of_isFrameOn (frames h) (isFrameOn_frames h))

theorem frameCocycle_spec (h : Qual π L) (y y' : Y) :
    L.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ cover h y ⊓ π ⁻¹ᵁ cover h y' ≤ π ⁻¹ᵁ cover h y')).op (frames h y') =
      (frameCocycle h).u y y' •
        L.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ cover h y ⊓ π ⁻¹ᵁ cover h y' ≤ π ⁻¹ᵁ cover h y)).op (frames h y) :=
  Classical.choose_spec (Scheme.Modules.exists_unitCocycle_map_eq_smul_of_isFrameOn (frames h) (isFrameOn_frames h)) y y'

theorem preimage_inf (A B : Y.Opens) : π ⁻¹ᵁ (A ⊓ B) = π ⁻¹ᵁ A ⊓ π ⁻¹ᵁ B := rfl

noncomputable def normCocycle (h : Qual π L) : UnitCocycle (cover h) where
  u y y' := Nf π (cover h y ⊓ cover h y')
    (show Γ(X, π ⁻¹ᵁ (cover h y ⊓ cover h y')) from (frameCocycle h).u y y')
  refl y := by
    haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
    have h1 := ((Nf_spec π h.normal).1 (cover h y ⊓ cover h y)).1

    show Nf π (cover h y ⊓ cover h y) (show Γ(X, π ⁻¹ᵁ (cover h y ⊓ cover h y)) from (frameCocycle h).u y y) = 1
    rw [(frameCocycle h).refl y]
    exact h1
  cocycle y y' y'' := by
    haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
    obtain ⟨h1, h2, -, -⟩ := Nf_spec π h.normal

    let W : Y.Opens := cover h y ⊓ cover h y' ⊓ cover h y''
    have l1 : W ≤ cover h y ⊓ cover h y' := le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right)
    have l2 : W ≤ cover h y' ⊓ cover h y'' := le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have l3 : W ≤ cover h y ⊓ cover h y'' := le_inf (inf_le_left.trans inf_le_left) inf_le_right
    have r : ∀ {A : Y.Opens} (hle : W ≤ A) (a : Γ(X, π ⁻¹ᵁ A)),
        GlueOfCocycle.rO hle (Nf π A a) = Nf π W (X.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π hle)).op a) :=
      fun hle a => (h2 _ _ hle a).symm
    show GlueOfCocycle.rO l1 (Nf π _ _) * GlueOfCocycle.rO l2 (Nf π _ _) = GlueOfCocycle.rO l3 (Nf π _ _)
    rw [r l1, r l2, r l3, ← (h1 W).2]
    congr 1
    exact (frameCocycle h).cocycle y y' y''

open Classical in

noncomputable def Nm : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → X.Modules → Y.Modules :=
  fun _ Y π L => if h : Qual π L then glueOfCocycle (normCocycle h) else 𝟙_ Y.Modules

theorem Nm_eq (h : Qual π L) : Nm π L = glueOfCocycle (normCocycle h) := by
  classical
  show (if h : Qual π L then glueOfCocycle (normCocycle h) else 𝟙_ Y.Modules) = _
  rw [dif_pos h]

section helpers

variable {Z : Scheme.{u}} {ι : Type u}

theorem map_smul' {M : Z.Modules} {A B : Z.Opens} (hBA : B ≤ A) (r : Γ(Z, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hBA).op (r • m) = GlueOfCocycle.rO hBA r • M.presheaf.map (homOfLE hBA).op m :=
  M.val.map_smul (homOfLE hBA).op r m

private noncomputable def _root_.AlgebraicGeometry.Scheme.Modules.UnitCocycle.restrict {U : ι → Z.Opens}
    (c : UnitCocycle U) (W : ι → Z.Opens) (hW : ∀ i, W i ≤ U i) : UnitCocycle W where
  u i j := GlueOfCocycle.rO (inf_le_inf (hW i) (hW j)) (c.u i j)
  refl i := by rw [c.refl, map_one]
  cocycle i j k := by
    simp only [GlueOfCocycle.rO_rO]
    exact c.cocycle_le i j k _ _ _

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.Scheme.Modules.UnitCocycle.restrict" "AlgebraicGeometry.Scheme.Modules.UnitCocycle.restrict"
@[scoped simp] private theorem _root_.AlgebraicGeometry.Scheme.Modules.UnitCocycle.restrict_u {U : ι → Z.Opens}
    (c : UnitCocycle U) (W : ι → Z.Opens) (hW : ∀ i, W i ≤ U i) (i j : ι) :
    (c.restrict W hW).u i j = GlueOfCocycle.rO (inf_le_inf (hW i) (hW j)) (c.u i j) := rfl

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.Scheme.Modules.UnitCocycle.restrict_u" "AlgebraicGeometry.Scheme.Modules.UnitCocycle.restrict_u"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle"

theorem transitions_restrict {U : ι → Z.Opens} (c : UnitCocycle U) {M : Z.Modules} (e : ∀ i, Γ(M, U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i))
    (W : ι → Z.Opens) (hW : ∀ i, W i ≤ U i) (i j : ι) :
    M.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (M.presheaf.map (homOfLE (hW j)).op (e j)) =
      (c.restrict W hW).u i j •
        M.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (M.presheaf.map (homOfLE (hW i)).op (e i)) := by
  have hle : W i ⊓ W j ≤ U i ⊓ U j := inf_le_inf (hW i) (hW j)
  have := congrArg (M.presheaf.map (homOfLE hle).op) (htrans i j)
  rw [map_smul'] at this

  have cj : M.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (M.presheaf.map (homOfLE (hW j)).op (e j)) =
      M.presheaf.map (homOfLE hle).op (M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j)) := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) (e j) = (M.presheaf.map _ ≫ M.presheaf.map _) (e j)
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  have ci : M.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (M.presheaf.map (homOfLE (hW i)).op (e i)) =
      M.presheaf.map (homOfLE hle).op (M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i)) := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) (e i) = (M.presheaf.map _ ≫ M.presheaf.map _) (e i)
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  rw [cj, ci, this]
  rfl

theorem transitions_smul {U : ι → Z.Opens} (c : UnitCocycle U) {M : Z.Modules} (e : ∀ i, Γ(M, U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i))
    (h : ∀ i, Γ(Z, U i)ˣ) (i j : ι) :
    M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op ((h j : Γ(Z, U j)) • e j) =
      (c.twist (fun i => (h i)⁻¹)).u i j •
        M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op ((h i : Γ(Z, U i)) • e i) := by
  rw [map_smul', map_smul', htrans i j, smul_smul, smul_smul]
  congr 1

  show GlueOfCocycle.rO inf_le_right (h j : Γ(Z, U j)) * c.u i j =
    GlueOfCocycle.rO inf_le_left (((h i)⁻¹ : Γ(Z, U i)ˣ) : Γ(Z, U i)) * c.u i j *
      GlueOfCocycle.rO inf_le_right ((((h j)⁻¹)⁻¹ : Γ(Z, U j)ˣ) : Γ(Z, U j)) * GlueOfCocycle.rO inf_le_left (h i : Γ(Z, U i))
  rw [inv_inv]
  have hi : GlueOfCocycle.rO (inf_le_left : U i ⊓ U j ≤ U i) (((h i)⁻¹ : Γ(Z, U i)ˣ) : Γ(Z, U i)) *
      GlueOfCocycle.rO inf_le_left (h i : Γ(Z, U i)) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc GlueOfCocycle.rO inf_le_right (h j : Γ(Z, U j)) * c.u i j
      = GlueOfCocycle.rO inf_le_right (h j : Γ(Z, U j)) * c.u i j * 1 := by rw [mul_one]
    _ = _ := by rw [← hi]; ring

theorem nonempty_iso_of_framed_of_twist {U : ι → Z.Opens} (hU : ⨆ i, U i = ⊤) (c : UnitCocycle U)
    {M M' : Z.Modules} (e : ∀ i, Γ(M, U i)) (he : ∀ i, IsFrameOn (e i) (U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i))
    (h : ∀ i, Γ(Z, U i)ˣ)
    (e' : ∀ i, Γ(M', U i)) (he' : ∀ i, IsFrameOn (e' i) (U i))
    (htrans' : ∀ i j, M'.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e' j) =
      (c.twist h).u i j • M'.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e' i)) :
    Nonempty (M ≅ M') := by
  obtain ⟨φ, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hU c e he htrans
  obtain ⟨ψ, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hU (c.twist h) e' he' htrans'
  obtain ⟨τ, -⟩ := Scheme.Modules.exists_glueOfCocycle_twist_iso hU c h
  exact ⟨φ ≪≫ τ.symm ≪≫ ψ.symm⟩

end helpers
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle"

section helpers2

variable {Z : Scheme.{u}} {ι : Type u}

theorem isInvertible_of_iso {M M' : Z.Modules} (φ : M ≅ M') (hM : IsInvertible M) : IsInvertible M' := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hx, ⟨e⟩⟩ := hM.1 x
  exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso φ.symm ≪≫ e⟩⟩

theorem app_map {M M' : Z.Modules} (φ : M ⟶ M') {A B : Z.Opens} (h : B ≤ A) (m : Γ(M, A)) :
    φ.app B (M.presheaf.map (homOfLE h).op m) = M'.presheaf.map (homOfLE h).op (φ.app A m) :=
  PresheafOfModules.naturality_apply φ.val (homOfLE h).op m

theorem app_smul {M M' : Z.Modules} (φ : M ⟶ M') {A : Z.Opens} (r : Γ(Z, A)) (m : Γ(M, A)) :
    φ.app A (r • m) = r • φ.app A m :=
  (φ.val.app (op A)).hom.map_smul r m

theorem app_hom_inv {M M' : Z.Modules} (φ : M ≅ M') {A : Z.Opens} (m : Γ(M', A)) :
    φ.hom.app A (φ.inv.app A m) = m := by
  change ((φ.inv ≫ φ.hom).app A) m = m
  rw [φ.inv_hom_id]; rfl

theorem app_inv_hom {M M' : Z.Modules} (φ : M ≅ M') {A : Z.Opens} (m : Γ(M, A)) :
    φ.inv.app A (φ.hom.app A m) = m := by
  change ((φ.hom ≫ φ.inv).app A) m = m
  rw [φ.hom_inv_id]; rfl

theorem isFrameOn_app_of_iso {M M' : Z.Modules} (φ : M ≅ M') {A V : Z.Opens} {s : Γ(M, A)} (hs : IsFrameOn s V) :
    IsFrameOn (φ.hom.app A s) V := by
  intro W hWA hWV
  have hcomp : (fun g : Γ(Z, W) => g • M'.presheaf.map (homOfLE hWA).op (φ.hom.app A s)) =
      (fun m => φ.hom.app W m) ∘ (fun g : Γ(Z, W) => g • M.presheaf.map (homOfLE hWA).op s) := by
    funext g
    simp only [Function.comp_apply, app_smul, app_map]
  rw [hcomp]
  refine Function.Bijective.comp ?_ (hs hWA hWV)
  exact ⟨fun a b hab => by simpa [app_inv_hom] using congrArg (φ.inv.app W) hab,
    fun m => ⟨φ.inv.app W m, app_hom_inv φ m⟩⟩

theorem transition_unique {M : Z.Modules} {A B W : Z.Opens} (hWA : W ≤ A) (hWB : W ≤ B)
    {s : Γ(M, A)} {t : Γ(M, B)} {V : Z.Opens} (hs : IsFrameOn s V) (hWV : W ≤ V) (u u' : Γ(Z, W))
    (hu : M.presheaf.map (homOfLE hWB).op t = u • M.presheaf.map (homOfLE hWA).op s)
    (hu' : M.presheaf.map (homOfLE hWB).op t = u' • M.presheaf.map (homOfLE hWA).op s) : u = u' :=
  (hs hWA hWV).1 (hu.symm.trans hu')

theorem transitions_app {M M' : Z.Modules} (φ : M ⟶ M') {U : ι → Z.Opens} (c : UnitCocycle U) (e : ∀ i, Γ(M, U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i)) (i j : ι) :
    M'.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (φ.app (U j) (e j)) =
      c.u i j • M'.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (φ.app (U i) (e i)) := by
  rw [← app_map, ← app_map, htrans, app_smul]

end helpers2
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle"

section kit
variable {M : X.Modules}

theorem map_smul'' {A B : X.Opens} (hBA : B ≤ A) (r : Γ(X, A)) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hBA).op (r • m) = X.presheaf.map (homOfLE hBA).op r • M.presheaf.map (homOfLE hBA).op m :=
  Scheme.Modules.map_smul M _ r m

theorem map_map {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (m : Γ(M, A)) :
    M.presheaf.map (homOfLE hCB).op (M.presheaf.map (homOfLE hBA).op m) = M.presheaf.map (homOfLE (hCB.trans hBA)).op m := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]; rfl

theorem map_refl {A : X.Opens} (m : Γ(M, A)) : M.presheaf.map (homOfLE (le_refl A)).op m = m := by
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, M.presheaf.map_id]; rfl

theorem isFrameOn_unit_smul_map {A W : X.Opens} (hW : W ≤ A) {s : Γ(M, A)} (hs : IsFrameOn s A)
    (g : Γ(X, W)) (hg : IsUnit g) : IsFrameOn (g • M.presheaf.map (homOfLE hW).op s) W := by
  intro W' hW'W _
  have hg' : IsUnit (X.presheaf.map (homOfLE hW'W).op g) := hg.map _
  obtain ⟨v, hv⟩ := hg'
  have hb := hs (hW'W.trans hW) (hW'W.trans hW)
  have hcomp : (fun a : Γ(X, W') => a • M.presheaf.map (homOfLE hW'W).op (g • M.presheaf.map (homOfLE hW).op s)) =
      (fun a : Γ(X, W') => a • M.presheaf.map (homOfLE (hW'W.trans hW)).op s) ∘ (fun a => a * ↑v) := by
    funext a
    simp only [Function.comp_apply, map_smul'', map_map, ← hv, smul_smul]
  rw [hcomp]
  exact hb.comp (Units.mulRight_bijective v)

end kit
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle"

section kitD

variable {Z : Scheme.{u}} {ι κ : Type u}

private noncomputable def _root_.AlgebraicGeometry.Scheme.Modules.UnitCocycle.reindexRestrict {U : ι → Z.Opens}
    (c : UnitCocycle U) (f : κ → ι) (W : κ → Z.Opens) (hW : ∀ k, W k ≤ U (f k)) : UnitCocycle W where
  u k l := GlueOfCocycle.rO (inf_le_inf (hW k) (hW l)) (c.u (f k) (f l))
  refl k := by rw [c.refl, map_one]
  cocycle k l m := by
    simp only [GlueOfCocycle.rO_rO]
    exact c.cocycle_le (f k) (f l) (f m) _ _ _

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.Scheme.Modules.UnitCocycle.reindexRestrict" "AlgebraicGeometry.Scheme.Modules.UnitCocycle.reindexRestrict"
@[scoped simp] private theorem _root_.AlgebraicGeometry.Scheme.Modules.UnitCocycle.reindexRestrict_u {U : ι → Z.Opens}
    (c : UnitCocycle U) (f : κ → ι) (W : κ → Z.Opens) (hW : ∀ k, W k ≤ U (f k)) (k l : κ) :
    (c.reindexRestrict f W hW).u k l = GlueOfCocycle.rO (inf_le_inf (hW k) (hW l)) (c.u (f k) (f l)) := rfl

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.Scheme.Modules.UnitCocycle.reindexRestrict_u" "AlgebraicGeometry.Scheme.Modules.UnitCocycle.reindexRestrict_u"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle"

theorem transitions_reindexRestrict {U : ι → Z.Opens} (c : UnitCocycle U) {M : Z.Modules} (e : ∀ i, Γ(M, U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i))
    (f : κ → ι) (W : κ → Z.Opens) (hW : ∀ k, W k ≤ U (f k)) (k l : κ) :
    M.presheaf.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op (M.presheaf.map (homOfLE (hW l)).op (e (f l))) =
      (c.reindexRestrict f W hW).u k l •
        M.presheaf.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op (M.presheaf.map (homOfLE (hW k)).op (e (f k))) := by
  have hle : W k ⊓ W l ≤ U (f k) ⊓ U (f l) := inf_le_inf (hW k) (hW l)
  have := congrArg (M.presheaf.map (homOfLE hle).op) (htrans (f k) (f l))
  rw [map_smul'] at this
  have cj : M.presheaf.map (homOfLE (inf_le_right : W k ⊓ W l ≤ W l)).op (M.presheaf.map (homOfLE (hW l)).op (e (f l))) =
      M.presheaf.map (homOfLE hle).op (M.presheaf.map (homOfLE (inf_le_right : U (f k) ⊓ U (f l) ≤ U (f l))).op (e (f l))) := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) (e (f l)) = (M.presheaf.map _ ≫ M.presheaf.map _) (e (f l))
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  have ci : M.presheaf.map (homOfLE (inf_le_left : W k ⊓ W l ≤ W k)).op (M.presheaf.map (homOfLE (hW k)).op (e (f k))) =
      M.presheaf.map (homOfLE hle).op (M.presheaf.map (homOfLE (inf_le_left : U (f k) ⊓ U (f l) ≤ U (f k))).op (e (f k))) := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) (e (f k)) = (M.presheaf.map _ ≫ M.presheaf.map _) (e (f k))
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  rw [cj, ci, this]
  rfl

theorem map_irrel' {A B : (Z.Opens)ᵒᵖ} (f f' : A ⟶ B) (x : Γ(Z, A.unop)) :
    Z.presheaf.map f x = Z.presheaf.map f' x := by
  have hf : f = f' := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hf]

theorem map_op_irrel {A B : Z.Opens} (f f' : B ⟶ A) (x : Γ(Z, A)) :
    Z.presheaf.map f.op x = Z.presheaf.map f'.op x := by
  rw [Subsingleton.elim f f']

theorem transitions_pullback_glueFrame {Z' : Scheme.{u}} (g : Z' ⟶ Z) {U : ι → Z.Opens} (c : UnitCocycle U) (i j : ι) :
    ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map
        (homOfLE (inf_le_right : g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j ≤ g ⁻¹ᵁ U j)).op
        (pullbackLocalSection g (glueFrame c j)) =
      (c.comap g).u i j •
        ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map
          (homOfLE (inf_le_left : g ⁻¹ᵁ U i ⊓ g ⁻¹ᵁ U j ≤ g ⁻¹ᵁ U i)).op (pullbackLocalSection g (glueFrame c i)) := by
  have e := congrArg (pullbackLocalSection g) (map_glueFrame_eq_smul c i j)
  rw [pullbackLocalSection_smul, ← map_homOfLE_pullbackLocalSection, ← map_homOfLE_pullbackLocalSection] at e
  exact e

end kitD
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle"

theorem clause0 (h : Qual π L) : IsInvertible (Nm π L) := by
  rw [Nm_eq h]
  exact Scheme.Modules.isInvertible_glueOfCocycle (iSup_cover h) (normCocycle h)

theorem map_le_refl {Z : Scheme.{u}} {M : Z.Modules} {A : Z.Opens} (m : Γ(M, A)) :
    M.presheaf.map (homOfLE (le_refl A)).op m = m := by
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, M.presheaf.map_id]; rfl

noncomputable def nfUnit (h : Qual π L) (W : Y.Opens) (g : Γ(X, π ⁻¹ᵁ W)ˣ) : Γ(Y, W)ˣ where
  val := Nf π W (g : Γ(X, π ⁻¹ᵁ W))
  inv := Nf π W ((g⁻¹ : Γ(X, π ⁻¹ᵁ W)ˣ) : Γ(X, π ⁻¹ᵁ W))
  val_inv := by
    haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
    rw [← ((Nf_spec π h.normal).1 W).2, Units.mul_inv, ((Nf_spec π h.normal).1 W).1]
  inv_val := by
    haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
    rw [← ((Nf_spec π h.normal).1 W).2, Units.inv_mul, ((Nf_spec π h.normal).1 W).1]

theorem glue_framed_restrict (h : Qual π L) (W : ↥Y → Y.Opens) (hW : ∀ y, W y ≤ cover h y) :
    (∀ y, IsFrameOn ((glueOfCocycle (normCocycle h)).presheaf.map (homOfLE (hW y)).op
      (glueFrame (normCocycle h) y)) (W y)) ∧
    ∀ y y', (glueOfCocycle (normCocycle h)).presheaf.map (homOfLE (inf_le_right : W y ⊓ W y' ≤ W y')).op
        ((glueOfCocycle (normCocycle h)).presheaf.map (homOfLE (hW y')).op (glueFrame (normCocycle h) y')) =
      ((normCocycle h).restrict W hW).u y y' •
        (glueOfCocycle (normCocycle h)).presheaf.map (homOfLE (inf_le_left : W y ⊓ W y' ≤ W y)).op
          ((glueOfCocycle (normCocycle h)).presheaf.map (homOfLE (hW y)).op (glueFrame (normCocycle h) y)) :=
  ⟨fun y => ((isFrameOn_glueFrame (normCocycle h) y).map (homOfLE (hW y))).mono (hW y),
    transitions_restrict (normCocycle h) _ (map_glueFrame_eq_smul (normCocycle h)) W hW⟩

theorem glue_iso_of_upstairs_units (h : Qual π L) {L' : X.Modules} (h' : Qual π L')
    (g : ∀ y : Y, Γ(X, π ⁻¹ᵁ (cover h y ⊓ cover h' y))ˣ)
    (hrel : ∀ y y',
      ((frameCocycle h').restrict (fun y => π ⁻¹ᵁ (cover h y ⊓ cover h' y))
          (fun y => Scheme.Hom.preimage_mono π inf_le_right)).u y y' =
        (((frameCocycle h).restrict (fun y => π ⁻¹ᵁ (cover h y ⊓ cover h' y))
          (fun y => Scheme.Hom.preimage_mono π inf_le_left)).twist g).u y y') :
    Nonempty (glueOfCocycle (normCocycle h) ≅ glueOfCocycle (normCocycle h')) := by
  haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
  obtain ⟨N1, N2, -, -⟩ := Nf_spec π h.normal
  let W : ↥Y → Y.Opens := fun y => cover h y ⊓ cover h' y
  have hW : ∀ y, W y ≤ cover h y := fun y => inf_le_left
  have hW' : ∀ y, W y ≤ cover h' y := fun y => inf_le_right
  have hWtop : ⨆ y, W y = ⊤ :=
    top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ⟨y, ⟨mem_cover h y, mem_cover h' y⟩⟩
  obtain ⟨hfr, htr⟩ := glue_framed_restrict h W hW
  obtain ⟨hfr', htr'⟩ := glue_framed_restrict h' W hW'

  let k : ∀ y, Γ(Y, W y)ˣ := fun y => nfUnit h (W y) (g y)
  refine nonempty_iso_of_framed_of_twist hWtop ((normCocycle h).restrict W hW) _ hfr htr k _ hfr' (fun y y' => ?_)
  rw [htr' y y']
  congr 1

  have e1 : ((normCocycle h').restrict W hW').u y y' =
      Nf π (W y ⊓ W y') (((frameCocycle h').restrict (fun y => π ⁻¹ᵁ W y)
        (fun y => Scheme.Hom.preimage_mono π (hW' y))).u y y') := by
    show GlueOfCocycle.rO _ (Nf π _ _) = _
    exact (N2 _ _ (inf_le_inf (hW' y) (hW' y')) _).symm
  have e2 : ((normCocycle h).restrict W hW).u y y' =
      Nf π (W y ⊓ W y') (((frameCocycle h).restrict (fun y => π ⁻¹ᵁ W y)
        (fun y => Scheme.Hom.preimage_mono π (hW y))).u y y') := by
    show GlueOfCocycle.rO _ (Nf π _ _) = _
    exact (N2 _ _ (inf_le_inf (hW y) (hW y')) _).symm
  rw [e1, hrel y y']
  show Nf π (W y ⊓ W y') (GlueOfCocycle.rO inf_le_left ((g y : Γ(X, π ⁻¹ᵁ W y))) *
      ((frameCocycle h).restrict (fun y => π ⁻¹ᵁ W y) (fun y => Scheme.Hom.preimage_mono π (hW y))).u y y' *
      GlueOfCocycle.rO inf_le_right (((g y')⁻¹ : Γ(X, π ⁻¹ᵁ W y')ˣ) : Γ(X, π ⁻¹ᵁ W y'))) =
    GlueOfCocycle.rO inf_le_left (k y : Γ(Y, W y)) * ((normCocycle h).restrict W hW).u y y' *
      GlueOfCocycle.rO inf_le_right (((k y')⁻¹ : Γ(Y, W y')ˣ) : Γ(Y, W y'))
  have m1 := (N1 (W y ⊓ W y')).2
  erw [m1, m1, e2]
  congr 1
  · congr 1
    exact N2 _ _ (inf_le_left : W y ⊓ W y' ≤ W y) _
  · exact N2 _ _ (inf_le_right : W y ⊓ W y' ≤ W y') _

theorem clauseA (h : Qual π L) {L' : X.Modules} (φ : L ≅ L') : Nonempty (Nm π L ≅ Nm π L') := by
  haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
  have h' : Qual π L' := ⟨h.intX, h.intY, h.fin, h.surj, h.normal, isInvertible_of_iso φ h.inv⟩
  rw [Nm_eq h, Nm_eq h']
  let W : ↥Y → Y.Opens := fun y => cover h y ⊓ cover h' y
  have hW : ∀ y, W y ≤ cover h y := fun y => inf_le_left
  have hW' : ∀ y, W y ≤ cover h' y := fun y => inf_le_right

  let f : ∀ y, Γ(L', π ⁻¹ᵁ W y) := fun y =>
    L'.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π (hW y))).op (φ.hom.app _ (frames h y))
  let f' : ∀ y, Γ(L', π ⁻¹ᵁ W y) := fun y =>
    L'.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π (hW' y))).op (frames h' y)
  have hf : ∀ y, IsFrameOn (f y) (π ⁻¹ᵁ W y) := fun y =>
    ((isFrameOn_app_of_iso φ (isFrameOn_frames h y)).map (homOfLE (Scheme.Hom.preimage_mono π (hW y)))).mono
      (Scheme.Hom.preimage_mono π (hW y))
  have hf' : ∀ y, IsFrameOn (f' y) (π ⁻¹ᵁ W y) := fun y =>
    ((isFrameOn_frames h' y).map (homOfLE (Scheme.Hom.preimage_mono π (hW' y)))).mono
      (Scheme.Hom.preimage_mono π (hW' y))

  have hcf : ∀ y y', L'.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ W y ⊓ π ⁻¹ᵁ W y' ≤ π ⁻¹ᵁ W y')).op (f y') =
      ((frameCocycle h).restrict (fun y => π ⁻¹ᵁ W y) (fun y => Scheme.Hom.preimage_mono π (hW y))).u y y' •
        L'.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ W y ⊓ π ⁻¹ᵁ W y' ≤ π ⁻¹ᵁ W y)).op (f y) :=
    transitions_restrict (frameCocycle h) _ (transitions_app φ.hom (frameCocycle h) (frames h) (frameCocycle_spec h))
      (fun y => π ⁻¹ᵁ W y) (fun y => Scheme.Hom.preimage_mono π (hW y))
  have hcf' : ∀ y y', L'.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ W y ⊓ π ⁻¹ᵁ W y' ≤ π ⁻¹ᵁ W y')).op (f' y') =
      ((frameCocycle h').restrict (fun y => π ⁻¹ᵁ W y) (fun y => Scheme.Hom.preimage_mono π (hW' y))).u y y' •
        L'.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ W y ⊓ π ⁻¹ᵁ W y' ≤ π ⁻¹ᵁ W y)).op (f' y) :=
    transitions_restrict (frameCocycle h') _ (frameCocycle_spec h')
      (fun y => π ⁻¹ᵁ W y) (fun y => Scheme.Hom.preimage_mono π (hW' y))

  have hg : ∀ y, ∃ g : Γ(X, π ⁻¹ᵁ W y), IsUnit g ∧ g • f y = f' y := by
    intro y
    obtain ⟨g, hgu, hgeq⟩ := (hf y).exists_isUnit_smul_eq (hf' y) le_rfl le_rfl
    rw [map_le_refl, map_le_refl] at hgeq
    exact ⟨g, hgu, hgeq⟩
  choose g hgU hgeq using hg
  let gu : ∀ y, Γ(X, π ⁻¹ᵁ W y)ˣ := fun y => (hgU y).unit
  have hgu : ∀ y, f' y = (gu y : Γ(X, π ⁻¹ᵁ W y)) • f y := fun y => (hgeq y).symm

  refine glue_iso_of_upstairs_units h h' (fun y => (gu y)⁻¹) (fun y y' => ?_)
  apply transition_unique (M := L') inf_le_left inf_le_right (hf' y) inf_le_left
  · exact hcf' y y'
  · rw [hgu y, hgu y']
    exact transitions_smul _ f hcf (fun y => gu y) y y'

theorem clauseB (h : Qual π L) {L' : X.Modules} (h' : Qual π L') (hh : Qual π (L ⊗ L')) :
    Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L') := by
  haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
  obtain ⟨N1, N2, -, -⟩ := Nf_spec π h.normal
  rw [Nm_eq hh, Nm_eq h, Nm_eq h']

  let W : ↥Y → Y.Opens := fun y => cover h y ⊓ cover h' y ⊓ cover hh y
  have hW : ∀ y, W y ≤ cover h y := fun y => inf_le_left.trans inf_le_left
  have hW' : ∀ y, W y ≤ cover h' y := fun y => inf_le_left.trans inf_le_right
  have hWh : ∀ y, W y ≤ cover hh y := fun y => inf_le_right
  have hWtop : ⨆ y, W y = ⊤ :=
    top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ⟨y, ⟨⟨mem_cover h y, mem_cover h' y⟩, mem_cover hh y⟩⟩
  let r := (normCocycle h).restrict W hW
  let r' := (normCocycle h').restrict W hW'

  obtain ⟨hfr, htr⟩ := glue_framed_restrict h W hW
  obtain ⟨hfr', htr'⟩ := glue_framed_restrict h' W hW'
  obtain ⟨hfrh, htrh⟩ := glue_framed_restrict hh W hWh
  obtain ⟨α, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hWtop r _ hfr htr
  obtain ⟨β, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hWtop r' _ hfr' htr'

  obtain ⟨τ, -⟩ := Scheme.Modules.exists_glueOfCocycle_mul_iso_tensor hWtop r r'

  let PW : ↥Y → X.Opens := fun y => π ⁻¹ᵁ W y
  let fh : ∀ y, Γ(L, PW y) := fun y => L.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π (hW y))).op (frames h y)
  let fh' : ∀ y, Γ(L', PW y) := fun y => L'.presheaf.map (homOfLE (Scheme.Hom.preimage_mono π (hW' y))).op (frames h' y)
  let s : ∀ y, Γ(L ⊗ L', PW y) := fun y =>
    (L ⊗ L').presheaf.map (homOfLE (Scheme.Hom.preimage_mono π (hWh y))).op (frames hh y)
  let t : ∀ y, Γ(L ⊗ L', PW y) := fun y => Scheme.Modules.tensorSections (fh y) (fh' y)
  have hfh : ∀ y, IsFrameOn (fh y) (PW y) := fun y =>
    ((isFrameOn_frames h y).map (homOfLE (Scheme.Hom.preimage_mono π (hW y)))).mono (Scheme.Hom.preimage_mono π (hW y))
  have hfh' : ∀ y, IsFrameOn (fh' y) (PW y) := fun y =>
    ((isFrameOn_frames h' y).map (homOfLE (Scheme.Hom.preimage_mono π (hW' y)))).mono (Scheme.Hom.preimage_mono π (hW' y))
  have hs : ∀ y, IsFrameOn (s y) (PW y) := fun y =>
    ((isFrameOn_frames hh y).map (homOfLE (Scheme.Hom.preimage_mono π (hWh y)))).mono (Scheme.Hom.preimage_mono π (hWh y))
  have ht : ∀ y, IsFrameOn (t y) (PW y) := fun y => (hfh y).tensorSections (hfh' y)

  let c := (frameCocycle h).restrict PW (fun y => Scheme.Hom.preimage_mono π (hW y))
  let c' := (frameCocycle h').restrict PW (fun y => Scheme.Hom.preimage_mono π (hW' y))
  let ch := (frameCocycle hh).restrict PW (fun y => Scheme.Hom.preimage_mono π (hWh y))
  have hcf : ∀ y y', L.presheaf.map (homOfLE (inf_le_right : PW y ⊓ PW y' ≤ PW y')).op (fh y') =
      c.u y y' • L.presheaf.map (homOfLE (inf_le_left : PW y ⊓ PW y' ≤ PW y)).op (fh y) :=
    transitions_restrict (frameCocycle h) _ (frameCocycle_spec h) PW _
  have hcf' : ∀ y y', L'.presheaf.map (homOfLE (inf_le_right : PW y ⊓ PW y' ≤ PW y')).op (fh' y') =
      c'.u y y' • L'.presheaf.map (homOfLE (inf_le_left : PW y ⊓ PW y' ≤ PW y)).op (fh' y) :=
    transitions_restrict (frameCocycle h') _ (frameCocycle_spec h') PW _
  have hcs : ∀ y y', (L ⊗ L').presheaf.map (homOfLE (inf_le_right : PW y ⊓ PW y' ≤ PW y')).op (s y') =
      ch.u y y' • (L ⊗ L').presheaf.map (homOfLE (inf_le_left : PW y ⊓ PW y' ≤ PW y)).op (s y) :=
    transitions_restrict (frameCocycle hh) _ (frameCocycle_spec hh) PW _
  have hct : ∀ y y', (L ⊗ L').presheaf.map (homOfLE (inf_le_right : PW y ⊓ PW y' ≤ PW y')).op (t y') =
      (c.mul c').u y y' • (L ⊗ L').presheaf.map (homOfLE (inf_le_left : PW y ⊓ PW y' ≤ PW y)).op (t y) := by
    intro y y'
    show (L ⊗ L').presheaf.map (homOfLE inf_le_right).op (Scheme.Modules.tensorSections (fh y') (fh' y')) =
      (c.u y y' * c'.u y y') • (L ⊗ L').presheaf.map (homOfLE inf_le_left).op (Scheme.Modules.tensorSections (fh y) (fh' y))
    rw [Scheme.Modules.map_homOfLE_tensorSections, Scheme.Modules.map_homOfLE_tensorSections, hcf, hcf',
      Scheme.Modules.tensorSections_smul_left, Scheme.Modules.tensorSections_smul_right, smul_smul]

  have hg : ∀ y, ∃ g : Γ(X, PW y), IsUnit g ∧ g • t y = s y := by
    intro y
    obtain ⟨g, hgu, hgeq⟩ := (ht y).exists_isUnit_smul_eq (hs y) le_rfl le_rfl
    rw [map_le_refl, map_le_refl] at hgeq
    exact ⟨g, hgu, hgeq⟩
  choose g hgU hgeq using hg
  let gu : ∀ y, Γ(X, PW y)ˣ := fun y => (hgU y).unit
  have hgu : ∀ y, s y = (gu y : Γ(X, PW y)) • t y := fun y => (hgeq y).symm
  have hrel : ∀ y y', ch.u y y' = ((c.mul c').twist (fun y => (gu y)⁻¹)).u y y' := by
    intro y y'
    apply transition_unique (M := L ⊗ L') inf_le_left inf_le_right (hs y) inf_le_left
    · exact hcs y y'
    · rw [hgu y, hgu y']
      exact transitions_smul _ t hct (fun y => gu y) y y'

  let k : ∀ y, Γ(Y, W y)ˣ := fun y => nfUnit hh (W y) (gu y)⁻¹
  have key : ∀ y y', ((normCocycle hh).restrict W hWh).u y y' = ((r.mul r').twist k).u y y' := by
    intro y y'
    have eh : ((normCocycle hh).restrict W hWh).u y y' = Nf π (W y ⊓ W y') (ch.u y y') := by
      show GlueOfCocycle.rO _ (Nf π _ _) = _
      exact (N2 _ _ (inf_le_inf (hWh y) (hWh y')) _).symm
    have e1 : r.u y y' = Nf π (W y ⊓ W y') (c.u y y') := by
      show GlueOfCocycle.rO _ (Nf π _ _) = _
      exact (N2 _ _ (inf_le_inf (hW y) (hW y')) _).symm
    have e2 : r'.u y y' = Nf π (W y ⊓ W y') (c'.u y y') := by
      show GlueOfCocycle.rO _ (Nf π _ _) = _
      exact (N2 _ _ (inf_le_inf (hW' y) (hW' y')) _).symm
    rw [eh, hrel y y']
    show Nf π (W y ⊓ W y') (GlueOfCocycle.rO inf_le_left ((((gu y)⁻¹ : Γ(X, PW y)ˣ) : Γ(X, PW y))) *
        (c.u y y' * c'.u y y') *
        GlueOfCocycle.rO inf_le_right ((((gu y')⁻¹)⁻¹ : Γ(X, PW y')ˣ) : Γ(X, PW y'))) =
      GlueOfCocycle.rO inf_le_left (k y : Γ(Y, W y)) * (r.u y y' * r'.u y y') *
        GlueOfCocycle.rO inf_le_right (((k y')⁻¹ : Γ(Y, W y')ˣ) : Γ(Y, W y'))
    have m1 := (N1 (W y ⊓ W y')).2
    erw [m1, m1, m1, e1, e2]
    congr 1
    · congr 1
      exact N2 _ _ (inf_le_left : W y ⊓ W y' ≤ W y) _
    · rw [inv_inv]
      exact N2 _ _ (inf_le_right : W y ⊓ W y' ≤ W y') _
  have hγ : Nonempty (glueOfCocycle (r.mul r') ≅ glueOfCocycle (normCocycle hh)) :=
    nonempty_iso_of_framed_of_twist hWtop (r.mul r') (glueFrame (r.mul r')) (isFrameOn_glueFrame (r.mul r'))
      (map_glueFrame_eq_smul (r.mul r')) k _ hfrh (fun y y' => by rw [htrh y y', key y y'])
  obtain ⟨γ⟩ := hγ
  exact ⟨γ.symm ≪≫ τ ≪≫ (α.symm ⊗ᵢ β.symm)⟩

theorem clauseC (h : Qual π (𝟙_ X.Modules)) : Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) := by
  haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
  obtain ⟨h1, h2, -, -⟩ := Nf_spec π h.normal

  have hv : ∀ y : Y, ∃ v : Γ(X, π ⁻¹ᵁ cover h y), IsUnit v ∧ v • unitSection (π ⁻¹ᵁ cover h y) = frames h y := by
    intro y
    obtain ⟨v, hvu, hv⟩ := (isFrameOn_unitSection (U := π ⁻¹ᵁ cover h y) (π ⁻¹ᵁ cover h y)).exists_isUnit_smul_eq
      (isFrameOn_frames h y) le_rfl le_rfl
    refine ⟨v, hvu, ?_⟩
    rwa [map_refl, map_refl] at hv
  choose v hvu hv using hv

  have hu : ∀ y y', (frameCocycle h).u y y' *
      X.presheaf.map (homOfLE (inf_le_left : π ⁻¹ᵁ cover h y ⊓ π ⁻¹ᵁ cover h y' ≤ _)).op (v y) =
        X.presheaf.map (homOfLE (inf_le_right : π ⁻¹ᵁ cover h y ⊓ π ⁻¹ᵁ cover h y' ≤ _)).op (v y') := by
    intro y y'
    have e := frameCocycle_spec h y y'
    rw [← hv y, ← hv y', map_smul'', map_smul'', map_unitSection, map_unitSection, smul_smul] at e
    exact (smul_unitSection_bijective.1 e).symm

  have hsU : ∀ y, IsUnit (Nf π (cover h y) (v y)) := fun y => by
    obtain ⟨w, hw⟩ := (hvu y).exists_right_inv
    exact isUnit_iff_exists_inv.mpr ⟨Nf π (cover h y) w, by rw [← (h1 _).2, hw, (h1 _).1]⟩

  have hn : ∀ y y', (normCocycle h).u y y' *
      Y.presheaf.map (homOfLE (inf_le_left : cover h y ⊓ cover h y' ≤ _)).op (Nf π (cover h y) (v y)) =
        Y.presheaf.map (homOfLE (inf_le_right : cover h y ⊓ cover h y' ≤ _)).op (Nf π (cover h y') (v y')) := by
    intro y y'
    change Nf π (cover h y ⊓ cover h y') _ * _ = _
    rw [← h2 _ _ inf_le_left (v y), ← h2 _ _ inf_le_right (v y'), ← (h1 _).2]
    congr 1
    exact hu y y'

  obtain ⟨φ, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame (iSup_cover h) (normCocycle h)
    (M := 𝟙_ Y.Modules) (fun y => Nf π (cover h y) (v y) • unitSection (cover h y))
    (fun y => by
      have := isFrameOn_unit_smul_map (M := 𝟙_ Y.Modules) le_rfl
        (isFrameOn_unitSection (U := cover h y) (cover h y)) _ (hsU y)
      rwa [map_unitSection] at this)
    (fun y y' => by
      rw [map_smul'', map_smul'', map_unitSection, map_unitSection, smul_smul, hn y y'])
  rw [Nm_eq h]
  exact ⟨φ.symm⟩

theorem clauseD (h : Qual π L) {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X)
    (sq : IsPullback g' π' π g) [Flat g] (h' : Qual π' ((Scheme.Modules.pullback g').obj L)) :
    Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅ Nm π' ((Scheme.Modules.pullback g').obj L)) := by
  haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
  haveI := h'.intX; haveI := h'.intY; haveI := h'.fin; haveI := h'.surj
  obtain ⟨h1, h2, -, h4⟩ := Nf_spec π h.normal
  obtain ⟨h1', h2', -, -⟩ := Nf_spec π' h'.normal

  set L' := (Scheme.Modules.pullback g').obj L with hL'
  set c := normCocycle h with hc
  set c' := normCocycle h' with hc'

  let W : ↥Y' → Y'.Opens := fun y' => g ⁻¹ᵁ cover h (g.base y') ⊓ cover h' y'
  have hWM : ∀ y', W y' ≤ g ⁻¹ᵁ cover h (g.base y') := fun y' => inf_le_left
  have hWM' : ∀ y', W y' ≤ cover h' y' := fun y' => inf_le_right
  have hW : ⨆ y', W y' = ⊤ :=
    top_le_iff.mp fun y' _ => Opens.mem_iSup.mpr ⟨y', ⟨mem_cover h (g.base y'), mem_cover h' y'⟩⟩

  let cW : UnitCocycle W := (c.comap g).reindexRestrict g.base W hWM

  have hM : ∀ y₁ y₂ : Y',
      ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map (homOfLE (inf_le_right : W y₁ ⊓ W y₂ ≤ W y₂)).op
        (((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map (homOfLE (hWM y₂)).op
          (pullbackLocalSection g (glueFrame c (g.base y₂)))) =
      cW.u y₁ y₂ • ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map
        (homOfLE (inf_le_left : W y₁ ⊓ W y₂ ≤ W y₁)).op
        (((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map (homOfLE (hWM y₁)).op
          (pullbackLocalSection g (glueFrame c (g.base y₁)))) :=
    fun y₁ y₂ => transitions_reindexRestrict (c.comap g) _ (transitions_pullback_glueFrame g c) g.base W hWM y₁ y₂

  obtain ⟨hh, hkey⟩ : ∃ hh : ∀ y' : Y', Γ(Y', W y')ˣ, ∀ y₁ y₂ : Y',
      (c'.restrict W hWM').u y₁ y₂ = (cW.twist hh).u y₁ y₂ := by

    have heq : ∀ V : Y.Opens, g' ⁻¹ᵁ (π ⁻¹ᵁ V) = π' ⁻¹ᵁ (g ⁻¹ᵁ V) := fun V => by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w]
    let T : ↥Y' → X'.Opens := fun y' => π' ⁻¹ᵁ W y'
    have hTA : ∀ y', T y' ≤ g' ⁻¹ᵁ (π ⁻¹ᵁ cover h (g.base y')) := fun y' =>
      (Scheme.Hom.preimage_mono π' (hWM y')).trans (le_of_eq (heq _).symm)
    have hTB : ∀ y', T y' ≤ π' ⁻¹ᵁ cover h' y' := fun y' => Scheme.Hom.preimage_mono π' (hWM' y')

    let A : ∀ y' : Y', Γ(L', T y') := fun y' =>
      L'.presheaf.map (homOfLE (hTA y')).op (pullbackLocalSection g' (frames h (g.base y')))
    let B : ∀ y' : Y', Γ(L', T y') := fun y' => L'.presheaf.map (homOfLE (hTB y')).op (frames h' y')
    have hA : ∀ y', IsFrameOn (A y') (T y') := fun y' =>
      (((isFrameOn_frames h (g.base y')).pullbackLocalSection g').map (homOfLE (hTA y'))).mono (hTA y')
    have hB : ∀ y', IsFrameOn (B y') (T y') := fun y' =>
      ((isFrameOn_frames h' y').map (homOfLE (hTB y'))).mono (hTB y')

    have hρ : ∀ y', ∃ ρ : Γ(X', T y'), IsUnit ρ ∧ ρ • A y' = B y' := fun y' => by
      obtain ⟨ρ, hρu, hρ⟩ := (hA y').exists_isUnit_smul_eq (hB y') le_rfl le_rfl
      refine ⟨ρ, hρu, ?_⟩
      rwa [map_refl, map_refl] at hρ
    choose ρ hρu hρ using hρ

    have hBt : ∀ y₁ y₂, L'.presheaf.map (homOfLE (inf_le_right : T y₁ ⊓ T y₂ ≤ T y₂)).op (B y₂) =
        (GlueOfCocycle.rO (inf_le_inf (hTB y₁) (hTB y₂)) ((frameCocycle h').u y₁ y₂)) •
          L'.presheaf.map (homOfLE (inf_le_left : T y₁ ⊓ T y₂ ≤ T y₁)).op (B y₁) := fun y₁ y₂ =>
      transitions_restrict (frameCocycle h') _ (frameCocycle_spec h') T hTB y₁ y₂
    have hAt : ∀ y₁ y₂, L'.presheaf.map (homOfLE (inf_le_right : T y₁ ⊓ T y₂ ≤ T y₂)).op (A y₂) =
        (GlueOfCocycle.rO (inf_le_inf (hTA y₁) (hTA y₂)) (((frameCocycle h).comap g').u (g.base y₁) (g.base y₂))) •
          L'.presheaf.map (homOfLE (inf_le_left : T y₁ ⊓ T y₂ ≤ T y₁)).op (A y₁) := fun y₁ y₂ => by
      refine transitions_reindexRestrict ((frameCocycle h).comap g') (fun i => pullbackLocalSection g' (frames h i))
        (fun i j => ?_) g.base T hTA y₁ y₂

      have e := congrArg (pullbackLocalSection g') (frameCocycle_spec h i j)
      rw [pullbackLocalSection_smul, ← map_homOfLE_pullbackLocalSection, ← map_homOfLE_pullbackLocalSection] at e
      exact e

    have hup : ∀ y₁ y₂,
        GlueOfCocycle.rO (inf_le_right : T y₁ ⊓ T y₂ ≤ T y₂) (ρ y₂) *
          GlueOfCocycle.rO (inf_le_inf (hTA y₁) (hTA y₂)) (((frameCocycle h).comap g').u (g.base y₁) (g.base y₂)) =
        GlueOfCocycle.rO (inf_le_inf (hTB y₁) (hTB y₂)) ((frameCocycle h').u y₁ y₂) *
          GlueOfCocycle.rO (inf_le_left : T y₁ ⊓ T y₂ ≤ T y₁) (ρ y₁) := fun y₁ y₂ => by
      apply ((hA y₁).bijective (inf_le_left : T y₁ ⊓ T y₂ ≤ T y₁) inf_le_left).1
      change (_ * _) • _ = (_ * _) • _
      rw [← smul_smul, ← hAt, ← map_smul', hρ y₂, hBt, ← hρ y₁, map_smul', smul_smul]

    have hsU : ∀ y', IsUnit (Nf π' (W y') (ρ y')) := fun y' => by
      obtain ⟨w, hw⟩ := (hρu y').exists_right_inv
      exact isUnit_iff_exists_inv.mpr ⟨Nf π' (W y') w, by rw [← (h1' _).2, hw, (h1' _).1]⟩
    refine ⟨fun y' => ((hsU y').unit)⁻¹, fun y₁ y₂ => ?_⟩

    have m1 := (h1' (W y₁ ⊓ W y₂)).2 (GlueOfCocycle.rO (inf_le_right : T y₁ ⊓ T y₂ ≤ T y₂) (ρ y₂))
      (GlueOfCocycle.rO (inf_le_inf (hTA y₁) (hTA y₂)) (((frameCocycle h).comap g').u (g.base y₁) (g.base y₂)))
    have m2 := (h1' (W y₁ ⊓ W y₂)).2 (GlueOfCocycle.rO (inf_le_inf (hTB y₁) (hTB y₂)) ((frameCocycle h').u y₁ y₂))
      (GlueOfCocycle.rO (inf_le_left : T y₁ ⊓ T y₂ ≤ T y₁) (ρ y₁))
    have eN := m1.symm.trans ((congrArg (Nf π' (W y₁ ⊓ W y₂)) (hup y₁ y₂)).trans m2)

    have n1 : Nf π' (W y₁ ⊓ W y₂) (GlueOfCocycle.rO (inf_le_right : T y₁ ⊓ T y₂ ≤ T y₂) (ρ y₂)) =
        GlueOfCocycle.rO inf_le_right (Nf π' (W y₂) (ρ y₂)) := (h2' _ _ inf_le_right (ρ y₂))
    have n4 : Nf π' (W y₁ ⊓ W y₂) (GlueOfCocycle.rO (inf_le_left : T y₁ ⊓ T y₂ ≤ T y₁) (ρ y₁)) =
        GlueOfCocycle.rO inf_le_left (Nf π' (W y₁) (ρ y₁)) := (h2' _ _ inf_le_left (ρ y₁))
    have n3 : Nf π' (W y₁ ⊓ W y₂) (GlueOfCocycle.rO (inf_le_inf (hTB y₁) (hTB y₂)) ((frameCocycle h').u y₁ y₂)) =
        (c'.restrict W hWM').u y₁ y₂ :=
      h2' _ _ (inf_le_inf (hWM' y₁) (hWM' y₂)) _
    have n2 : Nf π' (W y₁ ⊓ W y₂)
        (GlueOfCocycle.rO (inf_le_inf (hTA y₁) (hTA y₂)) (((frameCocycle h).comap g').u (g.base y₁) (g.base y₂))) =
        cW.u y₁ y₂ := by

      have e4 := h4 g π' g' sq h'.normal (cover h (g.base y₁) ⊓ cover h (g.base y₂))
        (show Γ(X, π ⁻¹ᵁ (cover h (g.base y₁) ⊓ cover h (g.base y₂))) from (frameCocycle h).u (g.base y₁) (g.base y₂))
      have e2 := h2' (g ⁻¹ᵁ (cover h (g.base y₁) ⊓ cover h (g.base y₂))) (W y₁ ⊓ W y₂)
        (inf_le_inf (hWM y₁) (hWM y₂)) (X'.presheaf.map (eqToHom (by
            rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w])).op
          ((g'.app (π ⁻¹ᵁ (cover h (g.base y₁) ⊓ cover h (g.base y₂)))).hom
            (show Γ(X, π ⁻¹ᵁ (cover h (g.base y₁) ⊓ cover h (g.base y₂))) from (frameCocycle h).u (g.base y₁) (g.base y₂))))
      rw [e4] at e2

      refine Eq.trans ?_ e2
      congr 1
      conv_rhs => rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
      exact map_irrel' _ _ _
    rw [n1, n2, n3, n4] at eN

    show (c'.restrict W hWM').u y₁ y₂ =
      GlueOfCocycle.rO inf_le_left (((hsU y₁).unit⁻¹ : Γ(Y', W y₁)ˣ) : Γ(Y', W y₁)) * cW.u y₁ y₂ *
        GlueOfCocycle.rO inf_le_right ((((hsU y₂).unit⁻¹)⁻¹ : Γ(Y', W y₂)ˣ) : Γ(Y', W y₂))
    rw [inv_inv, IsUnit.unit_spec]
    have hinv : GlueOfCocycle.rO (inf_le_left : W y₁ ⊓ W y₂ ≤ W y₁) (((hsU y₁).unit⁻¹ : Γ(Y', W y₁)ˣ) : Γ(Y', W y₁)) *
        GlueOfCocycle.rO inf_le_left (Nf π' (W y₁) (ρ y₁)) = 1 := by
      rw [← map_mul, IsUnit.val_inv_mul, map_one]
    calc (c'.restrict W hWM').u y₁ y₂
        = (c'.restrict W hWM').u y₁ y₂ * 1 := (mul_one _).symm
      _ = (c'.restrict W hWM').u y₁ y₂ * (GlueOfCocycle.rO (inf_le_left : W y₁ ⊓ W y₂ ≤ W y₁)
            (((hsU y₁).unit⁻¹ : Γ(Y', W y₁)ˣ) : Γ(Y', W y₁)) * GlueOfCocycle.rO inf_le_left (Nf π' (W y₁) (ρ y₁))) := by
          rw [hinv]
      _ = GlueOfCocycle.rO (inf_le_left : W y₁ ⊓ W y₂ ≤ W y₁) (((hsU y₁).unit⁻¹ : Γ(Y', W y₁)ˣ) : Γ(Y', W y₁)) *
            ((c'.restrict W hWM').u y₁ y₂ * GlueOfCocycle.rO inf_le_left (Nf π' (W y₁) (ρ y₁))) := by ring
      _ = _ := by rw [← eN]; ring

  have hM' : ∀ y₁ y₂ : Y',
      (glueOfCocycle c').presheaf.map (homOfLE (inf_le_right : W y₁ ⊓ W y₂ ≤ W y₂)).op
        ((glueOfCocycle c').presheaf.map (homOfLE (hWM' y₂)).op (glueFrame c' y₂)) =
      (cW.twist hh).u y₁ y₂ • (glueOfCocycle c').presheaf.map (homOfLE (inf_le_left : W y₁ ⊓ W y₂ ≤ W y₁)).op
        ((glueOfCocycle c').presheaf.map (homOfLE (hWM' y₁)).op (glueFrame c' y₁)) := fun y₁ y₂ => by
    rw [← hkey]
    exact transitions_restrict c' _ (map_glueFrame_eq_smul c') W hWM' y₁ y₂
  rw [Nm_eq h, Nm_eq h']
  exact nonempty_iso_of_framed_of_twist hW cW
    (fun y' => ((Scheme.Modules.pullback g).obj (glueOfCocycle c)).presheaf.map (homOfLE (hWM y')).op
      (pullbackLocalSection g (glueFrame c (g.base y'))))
    (fun y' => (((isFrameOn_glueFrame c (g.base y')).pullbackLocalSection g).map (homOfLE (hWM y'))).mono (hWM y'))
    hM hh
    (fun y' => (glueOfCocycle c').presheaf.map (homOfLE (hWM' y')).op (glueFrame c' y'))
    (fun y' => ((isFrameOn_glueFrame c' y').map (homOfLE (hWM' y'))).mono (hWM' y'))
    hM'

private noncomputable def _root_.AlgebraicGeometry.Scheme.Modules.UnitCocycle.refine {Z : Scheme.{u}} {ι κ : Type u}
    {U : ι → Z.Opens} (c : UnitCocycle U) (T : κ → Z.Opens) (r : κ → ι) (hT : ∀ k, T k ≤ U (r k)) : UnitCocycle T where
  u k l := GlueOfCocycle.rO (inf_le_inf (hT k) (hT l)) (c.u (r k) (r l))
  refl k := by rw [c.refl, map_one]
  cocycle k l m := by
    simp only [GlueOfCocycle.rO_rO]
    exact c.cocycle_le (r k) (r l) (r m) _ _ _

p2m_alias "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.Scheme.Modules.UnitCocycle.refine" "AlgebraicGeometry.Scheme.Modules.UnitCocycle.refine"

theorem transitions_refine {Z : Scheme.{u}} {ι κ : Type u} {U : ι → Z.Opens} (c : UnitCocycle U) {M : Z.Modules}
    (e : ∀ i, Γ(M, U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i))
    (T : κ → Z.Opens) (r : κ → ι) (hT : ∀ k, T k ≤ U (r k)) (k l : κ) :
    M.presheaf.map (homOfLE (inf_le_right : T k ⊓ T l ≤ T l)).op (M.presheaf.map (homOfLE (hT l)).op (e (r l))) =
      (c.refine T r hT).u k l •
        M.presheaf.map (homOfLE (inf_le_left : T k ⊓ T l ≤ T k)).op (M.presheaf.map (homOfLE (hT k)).op (e (r k))) := by
  have hle : T k ⊓ T l ≤ U (r k) ⊓ U (r l) := inf_le_inf (hT k) (hT l)
  have := congrArg (M.presheaf.map (homOfLE hle).op) (htrans (r k) (r l))
  rw [map_smul'] at this
  have cj : M.presheaf.map (homOfLE (inf_le_right : T k ⊓ T l ≤ T l)).op (M.presheaf.map (homOfLE (hT l)).op (e (r l))) =
      M.presheaf.map (homOfLE hle).op (M.presheaf.map (homOfLE (inf_le_right : U (r k) ⊓ U (r l) ≤ U (r l))).op (e (r l))) := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) (e (r l)) = (M.presheaf.map _ ≫ M.presheaf.map _) (e (r l))
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  have ci : M.presheaf.map (homOfLE (inf_le_left : T k ⊓ T l ≤ T k)).op (M.presheaf.map (homOfLE (hT k)).op (e (r k))) =
      M.presheaf.map (homOfLE hle).op (M.presheaf.map (homOfLE (inf_le_left : U (r k) ⊓ U (r l) ≤ U (r k))).op (e (r k))) := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) (e (r k)) = (M.presheaf.map _ ≫ M.presheaf.map _) (e (r k))
    rw [← Functor.map_comp, ← Functor.map_comp]; rfl
  rw [cj, ci, this]
  rfl

theorem transitions_comap {Z Z' : Scheme.{u}} (φ : Z' ⟶ Z) {ι : Type u} {U : ι → Z.Opens} (c : UnitCocycle U)
    {M : Z.Modules} (e : ∀ i, Γ(M, U i))
    (htrans : ∀ i j, M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j) =
      c.u i j • M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i)) (i j : ι) :
    ((Scheme.Modules.pullback φ).obj M).presheaf.map
        (homOfLE (inf_le_right : φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j ≤ φ ⁻¹ᵁ U j)).op (pullbackLocalSection φ (e j)) =
      (c.comap φ).u i j • ((Scheme.Modules.pullback φ).obj M).presheaf.map
        (homOfLE (inf_le_left : φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j ≤ φ ⁻¹ᵁ U i)).op (pullbackLocalSection φ (e i)) := by
  have h1 : ((Scheme.Modules.pullback φ).obj M).presheaf.map
      (homOfLE (inf_le_right : φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j ≤ φ ⁻¹ᵁ U j)).op (pullbackLocalSection φ (e j)) =
      pullbackLocalSection φ (M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (e j)) :=
    map_homOfLE_pullbackLocalSection φ (L := M) (inf_le_right : U i ⊓ U j ≤ U j) (e j)
  have h2 : ((Scheme.Modules.pullback φ).obj M).presheaf.map
      (homOfLE (inf_le_left : φ ⁻¹ᵁ U i ⊓ φ ⁻¹ᵁ U j ≤ φ ⁻¹ᵁ U i)).op (pullbackLocalSection φ (e i)) =
      pullbackLocalSection φ (M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (e i)) :=
    map_homOfLE_pullbackLocalSection φ (L := M) (inf_le_left : U i ⊓ U j ≤ U i) (e i)
  rw [h1, h2, htrans i j, pullbackLocalSection_smul]
  rfl

section kitE

variable {Z : Scheme.{u}}

theorem isIntegral_opens [IsIntegral Z] (V : Z.Opens) [hV : Nonempty V] : IsIntegral (V : Scheme.{u}) :=
  isIntegral_of_isOpenImmersion V.ι

theorem isIntegrallyClosed_sections_opens (V : Z.Opens)
    (hN : ∀ U : Z.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Z, U))
    (U' : (V : Scheme.{u}).Opens) (hU' : IsAffineOpen U') : IsIntegrallyClosed Γ(V, U') := by
  haveI := hN (V.ι ''ᵁ U') (hU'.image_of_isOpenImmersion V.ι)
  exact IsIntegrallyClosed.of_equiv (V.ι.appIso U').commRingCatIsoToRingEquiv

theorem mapM_irrel' {M : Z.Modules} {A B : (Z.Opens)ᵒᵖ} (f f' : A ⟶ B) (x : Γ(M, A.unop)) :
    M.presheaf.map f x = M.presheaf.map f' x := by
  have hf : f = f' := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hf]

theorem mapO_irrel' {A B : (Z.Opens)ᵒᵖ} (f f' : A ⟶ B) (x : Γ(Z, A.unop)) :
    Z.presheaf.map f x = Z.presheaf.map f' x := by
  have hf : f = f' := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  rw [hf]

theorem subsingleton_sections_of_isEmpty [IsEmpty Z] (M : Z.Modules) (W : Z.Opens) : Subsingleton Γ(M, W) := by
  have hW : W = ⊥ := by ext z; exact (IsEmpty.false z).elim
  subst hW

  let F : TopCat.Sheaf AddCommGrpCat Z.carrier := ⟨M.val.presheaf, M.isSheaf⟩
  have hT := F.isTerminalOfEmpty
  refine ⟨fun a b => ?_⟩
  have h0 : ∀ x : Γ(M, (⊥ : Z.Opens)), x = 0 := fun x => by
    have e := hT.hom_ext (𝟙 _) 0
    exact congrArg (fun φ : F.1.obj (op ⊥) ⟶ F.1.obj (op ⊥) => φ.hom x) e
  rw [h0 a, h0 b]

theorem isFrameOn_of_isEmpty [IsEmpty Z] {M : Z.Modules} {U : Z.Opens} (s : Γ(M, U)) (V : Z.Opens) :
    IsFrameOn s V := by
  intro W hWU _
  haveI := subsingleton_sections_of_isEmpty M W
  haveI : Subsingleton Γ(Z, W) := by
    have hW : W = ⊥ := by ext z; exact (IsEmpty.false z).elim
    subst hW; infer_instance
  exact ⟨fun a b _ => Subsingleton.elim a b, fun x => ⟨0, Subsingleton.elim _ _⟩⟩

theorem nonempty_iso_of_isEmpty [IsEmpty Z] {ι : Type u} {U : ι → Z.Opens} (hU : ⨆ i, U i = ⊤) (c : UnitCocycle U)
    (M M' : Z.Modules) : Nonempty (M ≅ M') := by
  haveI : ∀ W : Z.Opens, Subsingleton Γ(Z, W) := fun W => by
    have hW : W = ⊥ := by ext z; exact (IsEmpty.false z).elim
    subst hW; infer_instance
  obtain ⟨φ, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hU c (M := M) (fun _ => 0)
    (fun i => isFrameOn_of_isEmpty _ _) (fun i j => by
      haveI := subsingleton_sections_of_isEmpty M (U i ⊓ U j); exact Subsingleton.elim _ _)
  obtain ⟨ψ, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hU c (M := M') (fun _ => 0)
    (fun i => isFrameOn_of_isEmpty _ _) (fun i j => by
      haveI := subsingleton_sections_of_isEmpty M' (U i ⊓ U j); exact Subsingleton.elim _ _)
  exact ⟨φ ≪≫ ψ.symm⟩

end kitE
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle"

theorem clauseE (h : Qual π L) (V : Y.Opens) (d : ℕ) [Flat (π ∣_ V)] [LocallyOfFinitePresentation (π ∣_ V)]
    (hd : ∀ y : V, (π ∣_ V).finrank y = d) :
    Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
      Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L)) := by
  haveI := h.intX; haveI := h.intY; haveI := h.fin; haveI := h.surj
  rw [Nm_eq h]

  let πV := π ∣_ V
  let LV := (Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L
  let NV := Scheme.Modules.normModule (π ∣_ V) d LV

  let Uc : ↥Y → (V : Scheme.{u}).Opens := fun y => V.ι ⁻¹ᵁ cover h y
  have hUc : ⨆ y, Uc y = ⊤ := top_le_iff.mp fun v _ => Opens.mem_iSup.mpr ⟨V.ι v, mem_cover h (V.ι v)⟩
  let cc : UnitCocycle Uc := (normCocycle h).comap V.ι
  obtain ⟨τ, -⟩ := Scheme.Modules.exists_pullback_glueOfCocycle_iso V.ι (iSup_cover h) (normCocycle h)

  by_cases hV : Nonempty V
  swap
  ·
    haveI : IsEmpty V := not_nonempty_iff.mp hV
    obtain ⟨e⟩ := nonempty_iso_of_isEmpty hUc cc ((Scheme.Modules.pullback V.ι).obj (glueOfCocycle (normCocycle h))) NV
    exact ⟨e⟩
  haveI := hV

  haveI : IsFinite πV := inferInstance
  haveI : Surjective πV := MorphismProperty.of_isPullback (isPullback_morphismRestrict π V).flip inferInstance
  haveI : IsIntegral (V : Scheme.{u}) := isIntegral_opens V
  haveI : IsIntegral ((π ⁻¹ᵁ V : X.Opens) : Scheme.{u}) := by
    obtain ⟨v⟩ := hV
    obtain ⟨x, hx⟩ := π.surjective v.1
    haveI : Nonempty (π ⁻¹ᵁ V) := ⟨⟨x, show π.base x ∈ V by rw [hx]; exact v.2⟩⟩
    exact isIntegral_opens (π ⁻¹ᵁ V)
  have hNV : ∀ U' : (V : Scheme.{u}).Opens, IsAffineOpen U' → IsIntegrallyClosed Γ(V, U') :=
    isIntegrallyClosed_sections_opens V h.normal

  have hpre : ∀ A : Y.Opens, (π ⁻¹ᵁ V).ι ⁻¹ᵁ (π ⁻¹ᵁ A) = πV ⁻¹ᵁ (V.ι ⁻¹ᵁ A) := fun A => by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, morphismRestrict_ι]
  let sV : ∀ y, Γ(LV, πV ⁻¹ᵁ Uc y) := fun y =>
    LV.presheaf.map (eqToHom (hpre (cover h y)).symm).op (pullbackLocalSection (π ⁻¹ᵁ V).ι (frames h y))
  have hsV : ∀ y, IsFrameOn (sV y) (πV ⁻¹ᵁ Uc y) := fun y => by
    have := ((isFrameOn_frames h y).pullbackLocalSection (π ⁻¹ᵁ V).ι).map (eqToHom (hpre (cover h y)).symm)
    exact this.mono (le_of_eq (hpre (cover h y)).symm)
  let uV : ∀ y y', Γ((π ⁻¹ᵁ V : X.Opens), πV ⁻¹ᵁ (Uc y ⊓ Uc y')) := fun y y' =>
    ((π ⁻¹ᵁ V : X.Opens) : Scheme.{u}).presheaf.map (eqToHom (hpre (cover h y ⊓ cover h y')).symm).op
      (((π ⁻¹ᵁ V).ι.app (π ⁻¹ᵁ (cover h y ⊓ cover h y'))).hom ((frameCocycle h).u y y'))
  have huV : ∀ y y', LV.presheaf.map (homOfLE (Scheme.Hom.preimage_mono πV inf_le_right)).op (sV y') =
      uV y y' • LV.presheaf.map (homOfLE (Scheme.Hom.preimage_mono πV inf_le_left)).op (sV y) := fun y y' => by

    have e0 := transitions_comap (π ⁻¹ᵁ V).ι (frameCocycle h) (frames h) (frameCocycle_spec h) y y'

    have E : πV ⁻¹ᵁ (Uc y ⊓ Uc y') = (π ⁻¹ᵁ V).ι ⁻¹ᵁ (π ⁻¹ᵁ cover h y) ⊓ (π ⁻¹ᵁ V).ι ⁻¹ᵁ (π ⁻¹ᵁ cover h y') :=
      (hpre (cover h y ⊓ cover h y')).symm
    have e1 := congrArg (LV.presheaf.map (eqToHom E).op) e0
    rw [Scheme.Modules.map_smul] at e1

    have lhs : LV.presheaf.map (homOfLE (Scheme.Hom.preimage_mono πV inf_le_right)).op (sV y') =
        LV.presheaf.map (eqToHom E).op (((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L).presheaf.map
          (homOfLE (inf_le_right : (π ⁻¹ᵁ V).ι ⁻¹ᵁ (π ⁻¹ᵁ cover h y) ⊓ (π ⁻¹ᵁ V).ι ⁻¹ᵁ (π ⁻¹ᵁ cover h y') ≤ _)).op
          (pullbackLocalSection (π ⁻¹ᵁ V).ι (frames h y'))) := by
      change (LV.presheaf.map _ ≫ LV.presheaf.map _) _ = (LV.presheaf.map _ ≫ LV.presheaf.map _) _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact mapM_irrel' _ _ _
    have rhs : LV.presheaf.map (homOfLE (Scheme.Hom.preimage_mono πV inf_le_left)).op (sV y) =
        LV.presheaf.map (eqToHom E).op (((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L).presheaf.map
          (homOfLE (inf_le_left : (π ⁻¹ᵁ V).ι ⁻¹ᵁ (π ⁻¹ᵁ cover h y) ⊓ (π ⁻¹ᵁ V).ι ⁻¹ᵁ (π ⁻¹ᵁ cover h y') ≤ _)).op
          (pullbackLocalSection (π ⁻¹ᵁ V).ι (frames h y))) := by
      change (LV.presheaf.map _ ≫ LV.presheaf.map _) _ = (LV.presheaf.map _ ≫ LV.presheaf.map _) _
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact mapM_irrel' _ _ _
    have mid : uV y y' = ((π ⁻¹ᵁ V : X.Opens) : Scheme.{u}).presheaf.map (eqToHom E).op
        (((frameCocycle h).comap (π ⁻¹ᵁ V).ι).u y y') := mapO_irrel' _ _ _
    rw [lhs, rhs, mid]
    exact e1

  obtain ⟨M1, M2, M3, -⟩ := Nf_spec πV hNV
  obtain ⟨κ, T, r, hTU, hTle, Ω, hΩ, hΩtr⟩ :=
    Scheme.Modules.exists_refinement_isFrameOn_normModule_map_eq_normFun_smul πV hNV d hd
      (fun W' => Nf πV W') M1 M2 M3 Uc LV sV hsV uV huV

  have h4 : ∀ y y', Nf πV (Uc y ⊓ Uc y') (uV y y') = cc.u y y' := fun y y' =>
    (Nf_spec π h.normal).2.2.2 V.ι πV (π ⁻¹ᵁ V).ι (isPullback_morphismRestrict π V).flip hNV
      (cover h y ⊓ cover h y') (show Γ(X, π ⁻¹ᵁ (cover h y ⊓ cover h y')) from (frameCocycle h).u y y')

  have hTtop : ⨆ k, T k = ⊤ := hTU.trans hUc
  let cr := cc.refine T r hTle
  obtain ⟨α, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hTtop cr
    (M := glueOfCocycle cc) (fun k => (glueOfCocycle cc).presheaf.map (homOfLE (hTle k)).op (glueFrame cc (r k)))
    (fun k => ((isFrameOn_glueFrame cc (r k)).map (homOfLE (hTle k))).mono (hTle k))
    (transitions_refine cc _ (map_glueFrame_eq_smul cc) T r hTle)
  obtain ⟨β, -⟩ := Scheme.Modules.exists_iso_glueOfCocycle_app_eq_glueFrame hTtop cr (M := NV) Ω hΩ (fun k l => by
    rw [hΩtr k l (inf_le_inf (hTle k) (hTle l)), h4]
    rfl)
  exact ⟨τ ≪≫ α ≪≫ β.symm⟩

end AlgebraicGeometry.NormNormal
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal"
p2m_reactivate "P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry.NormNormal.AlgebraicGeometry.Scheme.Modules.UnitCocycle P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.AlgebraicGeometry"

open AlgebraicGeometry.NormNormal in

theorem solution :
    ∃ Nm : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → X.Modules → Y.Modules,
      ∀ ⦃X Y : Scheme.{u}⦄ (π : X ⟶ Y) [IsFinite π] [Surjective π] [IsIntegral X] [IsIntegral Y],
        (∀ U : Y.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y, U)) →
        (∀ L : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible (Nm π L)) ∧
        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') →
          Nonempty (Nm π L ≅ Nm π L')) ∧
        (∀ L L' : X.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible L' →
          Nonempty (Nm π (L ⊗ L') ≅ Nm π L ⊗ Nm π L')) ∧
        Nonempty (Nm π (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) ∧
        (∀ ⦃X' Y' : Scheme.{u}⦄ (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X), IsPullback g' π' π g →
          ∀ [Flat g] [IsIntegral X'] [IsIntegral Y'],
          (∀ U : Y'.Opens, IsAffineOpen U → IsIntegrallyClosed Γ(Y', U)) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback g).obj (Nm π L) ≅
              Nm π' ((Scheme.Modules.pullback g').obj L))) ∧
        (∀ (V : Y.Opens) (d : ℕ), Flat (π ∣_ V) → LocallyOfFinitePresentation (π ∣_ V) →
          (∀ y : V, (π ∣_ V).finrank y = d) →
          ∀ L : X.Modules, Scheme.Modules.IsInvertible L →
            Nonempty ((Scheme.Modules.pullback V.ι).obj (Nm π L) ≅
              Scheme.Modules.normModule (π ∣_ V) d ((Scheme.Modules.pullback (π ⁻¹ᵁ V).ι).obj L))) := by
  refine ⟨Nm, fun X Y π _ _ _ _ hN => ?_⟩
  have q : ∀ {L : X.Modules}, Scheme.Modules.IsInvertible L → Qual π L :=
    fun hL => ⟨inferInstance, inferInstance, inferInstance, inferInstance, hN, hL⟩
  refine ⟨fun L hL => clause0 (q hL), fun L L' hL ⟨φ⟩ => clauseA (q hL) φ, fun L L' hL hL' => ?_, ?_, ?_, ?_⟩
  ·
    have hLL' : Scheme.Modules.IsInvertible (L ⊗ L') := hL.tensor hL'
    exact clauseB (q hL) (q hL') (q hLL')
  · exact clauseC (q (Scheme.Modules.isInvertible_unit X))
  · intro X' Y' g π' g' sq _ _ _ hN' L hL

    haveI : IsFinite π' := MorphismProperty.of_isPullback sq inferInstance
    haveI : Surjective π' := MorphismProperty.of_isPullback sq inferInstance
    exact clauseD (q hL) g π' g' sq ⟨inferInstance, inferInstance, inferInstance, inferInstance, hN', hL.pullback g'⟩
  · intro V d hfl hlfp hd L hL
    exact clauseE (q hL) V d hd

end S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed (solution)
