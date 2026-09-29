-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/c92769f5-b1a6-576b-a67b-539305425737

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero.AlgebraicGeometry Opposite"

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul Scheme.Modules.Hom.zero_app Scheme.Modules.pullback Scheme.Hom Scheme.Modules.Hom Spec Scheme Scheme.Modules.Hom.id_app Proj Proj.basicOpen Scheme.Modules Scheme.Hom.appLE_map Proj.awayToSection Scheme.Modules.map_smul Scheme.ΓSpecIso Scheme.Modules.pullbackUnitIso Scheme.Modules.ProjPresentation ProjSpace.ratio Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_smul Scheme.Modules.pullbackSection Scheme.Modules.pullbackLocalSection Scheme.Modules.pullbackLocalSection_smul Scheme.Modules.pullbackLocalSection_app Scheme.Modules.IsFrameOn.pullbackLocalSection_monoidalV2 Scheme.Modules.IsFrameOn Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2"
namespace S3SectionValue
p2m_open "AlgebraicGeometry"

variable {Z : Scheme.{u}}

theorem app_naturality {M N : Z.Modules} (φ : M ⟶ N) {U V : Z.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    N.presheaf.map i.op (φ.app U x) = φ.app V (M.presheaf.map i.op x) := by
  have h := (φ.mapPresheaf).naturality i.op
  exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, V))) h) x).symm

theorem unit_hom_eq_zero_iff {N : Z.Modules} (u : 𝟙_ Z.Modules ⟶ N) (W₀ : Z.Opens) (hW : ⊤ ≤ W₀) :
    u = 0 ↔ u.app W₀ (Scheme.Modules.toUnitSection W₀ 1) = 0 := by
  obtain rfl : W₀ = ⊤ := le_antisymm le_top hW
  constructor
  · rintro rfl
    rw [Scheme.Modules.Hom.zero_app]; rfl
  · intro h0
    apply Scheme.Modules.hom_ext
    intro W
    ext y
    have hy : y = (Scheme.Modules.ofUnitSection W y) • Scheme.Modules.toUnitSection W 1 := by
      apply Scheme.Modules.ofUnitSection_injective W
      rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_toUnitSection, mul_one]
    have h1 : Scheme.Modules.toUnitSection W (1 : Γ(Z, W)) =
        (𝟙_ Z.Modules).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1) := by
      change Scheme.Modules.toUnitSection W 1 =
        Scheme.Modules.toUnitSection W ((Z.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom 1)
      rw [map_one]
    rw [hy, Scheme.Modules.Hom.app_smul, h1, ← app_naturality u, h0, map_zero, smul_zero,
      Scheme.Modules.Hom.zero_app]
    rfl

theorem map_top_injective (W₀ : Z.Opens) (hW : ⊤ ≤ W₀) :
    Function.Injective (Z.presheaf.map (homOfLE hW).op).hom := by
  obtain rfl : W₀ = ⊤ := le_antisymm le_top hW
  have : homOfLE hW = 𝟙 _ := rfl
  rw [this, op_id, Z.presheaf.map_id]
  exact Function.injective_id

end AlgebraicGeometry.S3SectionValue

open AlgebraicGeometry.S3SectionValue

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {M : X.Modules} {N : ℕ}
    (𝔓 : Scheme.Modules.ProjPresentation M f N)
    (s : 𝟙_ X.Modules ⟶ M) (c : Fin (N + 1) → R)
    (hs : s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) =
      ∑ j, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c j))) • 𝔓.σ j)
    {B : Type u} [CommRing B] (t : Spec (CommRingCat.of B) ⟶ X) (i : Fin (N + 1))
    (ht : ⊤ ≤ t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) :
    Scheme.Modules.pullbackSection t s = 0 ↔
      (t.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ⊤ ht).hom
        (∑ j, (f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))
                le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c j)) *
          (𝔓.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))).hom
            (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j))) = 0 := by
  classical

  have hframe : Scheme.Modules.IsFrameOn (𝔓.σ i) (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) := fun W hWtop hWU => 𝔓.frame i W hWU
  set σU : Γ(M, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) := M.presheaf.map (homOfLE (le_top : (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≤ ⊤)).op (𝔓.σ i) with hσU
  have hframeU : Scheme.Modules.IsFrameOn σU (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) := by
    rw [hσU]; exact hframe.map (homOfLE (le_top : (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≤ ⊤))
  set G : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) := ∑ j, (f.appLE ⊤ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (c j)) *
      (𝔓.toProj.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))).hom (Proj.awayToSection _ (MvPolynomial.X i) (ProjSpace.ratio R N i j)) with hG

  have hA : s.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) (Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1) = G • σU := by
    have h1 : Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) (1 : Γ(X, (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))) =
        (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1) := by
      change Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1 =
        Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ((X.presheaf.map (homOfLE (le_top : (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≤ ⊤)).op).hom 1)
      rw [map_one]
    rw [h1, ← app_naturality s, hs, map_sum, hG, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Scheme.Modules.map_smul, ← 𝔓.app_ratio_smul i j, ← hσU, smul_smul]
    congr 1
    congr 1
    rw [← CategoryTheory.comp_apply, Scheme.Hom.appLE_map]

  have hτ : Scheme.Modules.IsFrameOn (Scheme.Modules.pullbackLocalSection t σU) (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) :=
    Scheme.Modules.IsFrameOn.pullbackLocalSection_monoidalV2 t hframeU

  have hinv : (Scheme.Modules.pullbackUnitIso t).inv.app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) (Scheme.Modules.toUnitSection _ 1) =
      Scheme.Modules.pullbackLocalSection t (Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1) := by
    have h := Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection_monoidalV2 t (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1
    rw [map_one] at h
    have e1 : ((Scheme.Modules.pullbackUnitIso t).hom ≫ (Scheme.Modules.pullbackUnitIso t).inv).app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))
        (Scheme.Modules.pullbackLocalSection t (Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1)) =
        (Scheme.Modules.pullbackUnitIso t).inv.app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) ((Scheme.Modules.pullbackUnitIso t).hom.app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))
          (Scheme.Modules.pullbackLocalSection t (Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1))) := rfl
    have e2 : ((Scheme.Modules.pullbackUnitIso t).hom ≫ (Scheme.Modules.pullbackUnitIso t).inv).app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))
        (Scheme.Modules.pullbackLocalSection t (Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1)) =
        Scheme.Modules.pullbackLocalSection t (Scheme.Modules.toUnitSection (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) 1) := by
      rw [Iso.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    rw [← h]
    exact e1.symm.trans e2
  have hval : (Scheme.Modules.pullbackSection t s).app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) (Scheme.Modules.toUnitSection _ 1) =
      (t.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))).hom G • Scheme.Modules.pullbackLocalSection t σU := by
    have e : (Scheme.Modules.pullbackSection t s).app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) (Scheme.Modules.toUnitSection _ 1) =
        ((Scheme.Modules.pullback t).map s).app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))
          ((Scheme.Modules.pullbackUnitIso t).inv.app (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) (Scheme.Modules.toUnitSection _ 1)) := rfl
    rw [e, hinv, ← Scheme.Modules.pullbackLocalSection_app, hA, Scheme.Modules.pullbackLocalSection_smul]

  rw [unit_hom_eq_zero_iff _ (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) ht, hval]
  have hz := hτ.smul_eq_zero_iff (le_refl _) (le_refl _) ((t.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))).hom G)
  have hid : ((Scheme.Modules.pullback t).obj M).presheaf.map (homOfLE (le_refl (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))))).op
      (Scheme.Modules.pullbackLocalSection t σU) = Scheme.Modules.pullbackLocalSection t σU := by
    have : homOfLE (le_refl (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)))) = 𝟙 _ := rfl
    rw [this, op_id, CategoryTheory.Functor.map_id]
    rfl
  rw [hid] at hz
  rw [hz]

  constructor
  · intro h0
    show (t.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≫ (Spec (CommRingCat.of B)).presheaf.map (homOfLE ht).op).hom G = 0
    rw [CommRingCat.hom_comp, RingHom.comp_apply, h0, map_zero]
  · intro h0
    apply map_top_injective (t ⁻¹ᵁ (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))) ht
    rw [map_zero]
    have : (t.appLE (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ⊤ ht).hom G =
        ((Spec (CommRingCat.of B)).presheaf.map (homOfLE ht).op).hom ((t.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i))).hom G) := by
      show (t.app (𝔓.toProj ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)) ≫ (Spec (CommRingCat.of B)).presheaf.map (homOfLE ht).op).hom G = _
      rw [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [← this]; exact h0

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_pullbackSection_eq_zero_iff_appLE_sum_mul_eq_zero (solution)
