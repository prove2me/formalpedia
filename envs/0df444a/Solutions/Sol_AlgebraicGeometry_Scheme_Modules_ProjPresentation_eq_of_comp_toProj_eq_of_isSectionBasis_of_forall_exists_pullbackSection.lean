-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/eebc807a-0c7c-5292-8aa4-1059db706a06

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Spec.map Scheme Scheme.Hom.comp_appLE Proj Spec.map_id Proj.basicOpen Scheme.Modules Scheme.Hom.app_eq_appLE Proj.iSup_basicOpen_eq_top Scheme.ΓSpecIso_naturality Scheme.Hom.comp_preimage Proj.awayToSection Scheme.Hom.comp_apply Scheme.ΓSpecIso Scheme.Modules.IsSectionBasis Scheme.Modules.ProjPresentation ProjSpace.irrelevant_le_span_X ProjSpace.ratio Scheme.Modules.toUnitSection Scheme.Modules.pullbackSection Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub"
namespace S3Packaging
p2m_open "AlgebraicGeometry"

theorem eq_closedPoint_dualNumber (k : Type u) [Field k] (y : PrimeSpectrum (DualNumber k)) :
    y = IsLocalRing.closedPoint (DualNumber k) := by
  apply PrimeSpectrum.ext
  have h1 : Ideal.span {(DualNumber.eps : DualNumber k)} ≤ y.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    have : (DualNumber.eps : DualNumber k) * DualNumber.eps ∈ y.asIdeal := by
      rw [DualNumber.eps_mul_eps]; exact zero_mem _
    exact (y.isPrime.mem_or_mem this).elim id id
  have h2 := DualNumber.isMaximal_span_singleton_eps.eq_of_le y.isPrime.ne_top h1
  show y.asIdeal = IsLocalRing.maximalIdeal (DualNumber k)
  rw [DualNumber.maximalIdeal_eq_span_singleton_eps, h2]

theorem top_le_preimage_of_mem {k : Type u} [Field k] {X : Scheme.{u}}
    (T : Spec (CommRingCat.of (DualNumber k)) ⟶ X) (W : X.Opens)
    (h : T.base (IsLocalRing.closedPoint (DualNumber k)) ∈ W) : ⊤ ≤ T ⁻¹ᵁ W := by
  intro y _
  have hy : y = IsLocalRing.closedPoint (DualNumber k) := eq_closedPoint_dualNumber k y
  show T.base y ∈ W
  rw [hy]; exact h

theorem appLE_hom_eq_of_eq {X Y : Scheme.{u}} {F G : X ⟶ Y} (hFG : F = G) (U : Y.Opens) (V : X.Opens)
    (h1 : V ≤ F ⁻¹ᵁ U) (h2 : V ≤ G ⁻¹ᵁ U) (y : Γ(Y, U)) :
    (F.appLE U V h1).hom y = (G.appLE U V h2).hom y := by
  subst hFG; rfl

theorem appLE_top_hom_eq {X Y : Scheme.{u}} (F : X ⟶ Y) (h : (⊤ : X.Opens) ≤ F ⁻¹ᵁ ⊤) (y : Γ(Y, ⊤)) :
    (F.appLE ⊤ ⊤ h).hom y = F.appTop.hom y := by
  have e := Scheme.Hom.app_eq_appLE (f := F) (U := ⊤)
  show (F.appLE ⊤ ⊤ h).hom y = (F.app ⊤).hom y
  rw [e]
  rfl

theorem appLE_hom_app {X Y Z : Scheme.{u}} (T : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : X.Opens)
    (h : V ≤ T ⁻¹ᵁ (g ⁻¹ᵁ U)) (y : Γ(Z, U)) :
    (T.appLE (g ⁻¹ᵁ U) V h).hom ((g.app U).hom y) =
      ((T ≫ g).appLE U V (by rwa [Scheme.Hom.comp_preimage])).hom y := by
  rw [Scheme.Hom.comp_appLE T g U V]
  rfl

theorem comp_appLE_top_hom {X Y Z : Scheme.{u}} (o : X ⟶ Y) (D : Y ⟶ Z) (U : Z.Opens)
    (h1 : (⊤ : X.Opens) ≤ (o ≫ D) ⁻¹ᵁ U) (h2 : (⊤ : Y.Opens) ≤ D ⁻¹ᵁ U) (g : Γ(Z, U)) :
    ((o ≫ D).appLE U ⊤ h1).hom g = o.appTop.hom ((D.appLE U ⊤ h2).hom g) := by
  have e := Scheme.Hom.appLE_comp_appLE o D U ⊤ ⊤ h2 le_top
  rw [← appLE_top_hom_eq o le_top, ← CategoryTheory.comp_apply, e]

theorem ΓSpecIso_appLE_appLE_ΓSpecIso_inv {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (T : Spec (CommRingCat.of B) ⟶ X)
    (hT : T ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B))) (U : X.Opens) (hU : ⊤ ≤ T ⁻¹ᵁ U) (r : R) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((T.appLE U ⊤ hU).hom
      ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) = algebraMap R B r := by
  have e1 : (T.appLE U ⊤ hU).hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) =
      ((T ≫ f).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) := by
    rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map (CommRingCat.ofHom (algebraMap R B))).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom = CommRingCat.ofHom (algebraMap R B) := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  have key' := congrArg (fun m : CommRingCat.of R ⟶ CommRingCat.of B => m.hom r) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at key'
  rw [e1, appLE_hom_eq_of_eq hT ⊤ ⊤ _ le_top, appLE_top_hom_eq]
  exact key'

end AlgebraicGeometry.S3Packaging

open AlgebraicGeometry.S3Packaging

theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (𝓝 : X.Modules)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓝 𝔓.σ)
    (hpt : ∀ a b : Spec (CommRingCat.of k) ⟶ X, a ≫ f = 𝟙 _ → b ≫ f = 𝟙 _ → a ≠ b →
      ∃ s : 𝟙_ X.Modules ⟶ 𝓝, Scheme.Modules.pullbackSection a s = 0 ∧ Scheme.Modules.pullbackSection b s ≠ 0)
    (htan : ∀ P : Spec (CommRingCat.of (DualNumber k)) ⟶ X,
      P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) →
      P ≠ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) ≫
        (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P) →
      ∃ s : 𝟙_ X.Modules ⟶ 𝓝,
        Scheme.Modules.pullbackSection (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom) ≫ P) s = 0 ∧
          Scheme.Modules.pullbackSection P s ≠ 0)
    (P Q : Spec (CommRingCat.of (DualNumber k)) ⟶ X)
    (hP : P ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (hQ : Q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))))
    (h : P ≫ 𝔓.toProj = Q ≫ 𝔓.toProj) :
    P = Q := by
  classical
  have hoι : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ Spec.map (CommRingCat.ofHom (algebraMap k (DualNumber k))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
      Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]

  have ha : ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ P) ≫ f = 𝟙 _ := by rw [Category.assoc, hP]; exact hoι
  have hb : ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ Q) ≫ f = 𝟙 _ := by rw [Category.assoc, hQ]; exact hoι
  have hab : ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ P) ≫ 𝔓.toProj = ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ Q) ≫ 𝔓.toProj := by rw [Category.assoc, Category.assoc, h]
  have h0 : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ P = (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ Q :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
      k f 𝓝 𝔓 hσ hpt _ _ ha hb hab

  obtain ⟨D, hD, hDo, hval, hiff⟩ :=
    AlgebraicGeometry.exists_hom_spec_dualNumber_fst_eq_and_snd_eq_sub k f P Q hP hQ h0
  refine hiff.mp ?_
  by_contra hne
  obtain ⟨s, hs0, hs1⟩ := htan D hD hne

  obtain ⟨c, hc⟩ := hσ.2 (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
  simp only at hc

  have hcover := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k) (ProjSpace.irrelevant_le_span_X k N)
  have hxmem : (D ≫ 𝔓.toProj).base (IsLocalRing.closedPoint (DualNumber k)) ∈
      (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).Opens) := trivial
  rw [← hcover, TopologicalSpace.Opens.mem_iSup] at hxmem
  obtain ⟨i, hi⟩ := hxmem

  have hox₀ : (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base (IsLocalRing.closedPoint k) = IsLocalRing.closedPoint (DualNumber k) := eq_closedPoint_dualNumber k _
  have hDU : ⊤ ≤ D ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := top_le_preimage_of_mem D _ hi
  have hPx : P.base (IsLocalRing.closedPoint (DualNumber k)) = D.base (IsLocalRing.closedPoint (DualNumber k)) := by
    rw [← hox₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hDo]
  have hQx : Q.base (IsLocalRing.closedPoint (DualNumber k)) = D.base (IsLocalRing.closedPoint (DualNumber k)) := by
    rw [← hox₀, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← h0, hDo]
  have hPU : ⊤ ≤ P ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) :=
    top_le_preimage_of_mem P _ (by
      show 𝔓.toProj.base (P.base (IsLocalRing.closedPoint (DualNumber k))) ∈ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
      rw [hPx]; exact hi)
  have hQU : ⊤ ≤ Q ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) :=
    top_le_preimage_of_mem Q _ (by
      show 𝔓.toProj.base (Q.base (IsLocalRing.closedPoint (DualNumber k))) ∈ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
      rw [hQx]; exact hi)
  have hoDU : ⊤ ≤ ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D) ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := by
    intro y _
    show 𝔓.toProj.base (D.base ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)).base y)) ∈ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
    rw [Subsingleton.elim y (IsLocalRing.closedPoint k), hox₀]; exact hi

  let κ : Fin (N + 1) → Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) := fun j =>
    (f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c j))
  let uu : Fin (N + 1) → Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) := fun j =>
    (𝔓.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))).hom (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio k N i j))
  let G : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) := ∑ j, κ j * uu j
  let ED : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) →+* (DualNumber k) := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom.comp (D.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hDU).hom
  let EP : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) →+* (DualNumber k) := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom.comp (P.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hPU).hom
  let EQ : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) →+* (DualNumber k) := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom.comp (Q.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hQU).hom

  have hPQu : ∀ j, EP (uu j) = EQ (uu j) := by
    intro j
    show (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((P.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hPU).hom (uu j)) =
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((Q.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hQU).hom (uu j))
    simp only [uu]
    rw [appLE_hom_app P 𝔓.toProj _ ⊤ hPU, appLE_hom_app Q 𝔓.toProj _ ⊤ hQU, appLE_hom_eq_of_eq h]

  have hPκ : ∀ j, EP (κ j) = algebraMap k (DualNumber k) (c j) := fun j =>
    ΓSpecIso_appLE_appLE_ΓSpecIso_inv f P hP _ hPU (c j)
  have hQκ : ∀ j, EQ (κ j) = algebraMap k (DualNumber k) (c j) := fun j =>
    ΓSpecIso_appLE_appLE_ΓSpecIso_inv f Q hQ _ hQU (c j)
  have hPQG : EP G = EQ G := by
    simp only [G, map_sum, map_mul, hPQu, hPκ, hQκ]

  obtain ⟨hfst, hsnd⟩ := hval _ hPU hQU hDU G
  have hsnd0 : TrivSqZeroExt.snd (ED G) = 0 := by
    show TrivSqZeroExt.snd ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom ((D.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hDU).hom G)) = 0
    rw [hsnd]
    have : TrivSqZeroExt.snd (EP G) = TrivSqZeroExt.snd (EQ G) := by rw [hPQG]
    exact sub_eq_zero.mpr this

  have hbase := (AlgebraicGeometry.Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
    𝔓 s c hc.symm ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D) i hoDU).mp hs0
  have hfst0 : TrivSqZeroExt.fst (ED G) = 0 := by
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom ((((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) ≫ D).appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hoDU).hom G) = 0 := by
      rw [hbase, map_zero]
    rw [comp_appLE_top_hom (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom)) D _ hoDU hDU, ← CategoryTheory.comp_apply, Scheme.ΓSpecIso_naturality] at h1
    exact h1
  have hED0 : ED G = 0 := TrivSqZeroExt.ext hfst0 hsnd0
  have happ0 : (D.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hDU).hom G = 0 := by
    apply (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).commRingCatIsoToRingEquiv.injective
    rw [map_zero]
    exact hED0
  exact hs1 ((AlgebraicGeometry.Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
    𝔓 s c hc.symm D i hDU).mpr happ0)

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection (solution)
