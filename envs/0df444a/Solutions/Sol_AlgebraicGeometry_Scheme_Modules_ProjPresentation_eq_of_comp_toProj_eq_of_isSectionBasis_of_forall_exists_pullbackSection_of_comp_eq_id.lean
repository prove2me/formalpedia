-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/a572b7c5-1a64-5cb1-bade-d7b1308435e7

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id.AlgebraicGeometry"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Hom Scheme.Hom.appLE_comp_appLE Spec Scheme Scheme.Hom.comp_appLE Proj Proj.basicOpen Scheme.Modules Proj.iSup_basicOpen_eq_top Scheme.Hom.comp_preimage Proj.awayToSection Scheme.Hom.comp_apply Scheme.ΓSpecIso Scheme.Modules.IsSectionBasis Scheme.Modules.ProjPresentation ProjSpace.irrelevant_le_span_X ProjSpace.ratio Scheme.Modules.toUnitSection Scheme.Modules.pullbackSection Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero"
namespace S3Points
p2m_open "AlgebraicGeometry"

theorem appLE_hom_eq_of_eq {X Y : Scheme.{u}} {F G : X ⟶ Y} (hFG : F = G) (U : Y.Opens) (V : X.Opens)
    (h1 : V ≤ F ⁻¹ᵁ U) (h2 : V ≤ G ⁻¹ᵁ U) (y : Γ(Y, U)) :
    (F.appLE U V h1).hom y = (G.appLE U V h2).hom y := by
  subst hFG; rfl

theorem appLE_hom_app {X Y Z : Scheme.{u}} (T : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (V : X.Opens)
    (h : V ≤ T ⁻¹ᵁ (g ⁻¹ᵁ U)) (y : Γ(Z, U)) :
    (T.appLE (g ⁻¹ᵁ U) V h).hom ((g.app U).hom y) =
      ((T ≫ g).appLE U V (by rwa [Scheme.Hom.comp_preimage])).hom y := by
  rw [Scheme.Hom.comp_appLE T g U V]
  rfl

theorem appLE_hom_appLE {X Y Z : Scheme.{u}} (T : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (W : Y.Opens) (V : X.Opens)
    (hW : W ≤ g ⁻¹ᵁ U) (h : V ≤ T ⁻¹ᵁ W) (y : Γ(Z, U)) :
    (T.appLE W V h).hom ((g.appLE U W hW).hom y) =
      ((T ≫ g).appLE U V (h.trans ((TopologicalSpace.Opens.map T.base).map (homOfLE hW)).le)).hom y := by
  rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_comp_appLE]

end AlgebraicGeometry.S3Points

open AlgebraicGeometry.S3Points

theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (𝓝 : X.Modules)
    {N : ℕ} (𝔓 : Scheme.Modules.ProjPresentation 𝓝 f N) (hσ : Scheme.Modules.IsSectionBasis f 𝓝 𝔓.σ)
    (hpt : ∀ a b : Spec (CommRingCat.of k) ⟶ X, a ≫ f = 𝟙 _ → b ≫ f = 𝟙 _ → a ≠ b →
      ∃ s : 𝟙_ X.Modules ⟶ 𝓝, Scheme.Modules.pullbackSection a s = 0 ∧ Scheme.Modules.pullbackSection b s ≠ 0)
    (a b : Spec (CommRingCat.of k) ⟶ X) (ha : a ≫ f = 𝟙 _) (hb : b ≫ f = 𝟙 _)
    (h : a ≫ 𝔓.toProj = b ≫ 𝔓.toProj) :
    a = b := by
  classical
  by_contra hne
  obtain ⟨s, hsa, hsb⟩ := hpt a b ha hb hne
  obtain ⟨c, hc⟩ := hσ.2 (s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
  simp only at hc

  have hcover := Proj.iSup_basicOpen_eq_top (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)
    (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) k) (ProjSpace.irrelevant_le_span_X k N)
  have hxmem : (a ≫ 𝔓.toProj).base (IsLocalRing.closedPoint k) ∈
      (⊤ : (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k)).Opens) := trivial
  rw [← hcover, TopologicalSpace.Opens.mem_iSup] at hxmem
  obtain ⟨i, hi⟩ := hxmem
  have haU : ⊤ ≤ a ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := by
    intro y _
    show 𝔓.toProj.base (a.base y) ∈ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
    rw [Subsingleton.elim y (IsLocalRing.closedPoint k)]; exact hi
  have hbU : ⊤ ≤ b ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := by
    intro y _
    show 𝔓.toProj.base (b.base y) ∈ (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))
    rw [Subsingleton.elim y (IsLocalRing.closedPoint k), ← Scheme.Hom.comp_apply, ← h]; exact hi

  let κ : Fin (N + 1) → Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) := fun j =>
    (f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom (c j))
  let uu : Fin (N + 1) → Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) := fun j =>
    (𝔓.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))).hom (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio k N i j))
  let G : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) := ∑ j, κ j * uu j
  let Ea : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) →+* Γ(Spec (CommRingCat.of k), ⊤) := (a.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ haU).hom
  let Eb : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i))) →+* Γ(Spec (CommRingCat.of k), ⊤) := (b.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hbU).hom
  have hu : ∀ j, Ea (uu j) = Eb (uu j) := by
    intro j
    show (a.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ haU).hom (uu j) = (b.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hbU).hom (uu j)
    simp only [uu]
    rw [appLE_hom_app a 𝔓.toProj _ ⊤ haU, appLE_hom_app b 𝔓.toProj _ ⊤ hbU, appLE_hom_eq_of_eq h]
  have hκ : ∀ j, Ea (κ j) = Eb (κ j) := by
    intro j
    show (a.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ haU).hom (κ j) = (b.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hbU).hom (κ j)
    simp only [κ]
    rw [appLE_hom_appLE a f ⊤ _ ⊤ le_top haU, appLE_hom_appLE b f ⊤ _ ⊤ le_top hbU,
      appLE_hom_eq_of_eq (ha.trans hb.symm)]
  have hG : Ea G = Eb G := by
    simp only [G, map_sum, map_mul, hu, hκ]
  have hA := (AlgebraicGeometry.Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
    𝔓 s c hc.symm a i haU).mp hsa
  have hB : (b.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) ⊤ hbU).hom G = 0 := by
    show Eb G = 0
    rw [← hG]
    exact hA
  exact hsb ((AlgebraicGeometry.Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
    𝔓 s c hc.symm b i hbU).mpr hB)

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_eq_of_comp_toProj_eq_of_isSectionBasis_of_forall_exists_pullbackSection_of_comp_eq_id (solution)
