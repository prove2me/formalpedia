-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/32000ef8-aff2-5bad-a1c3-26c11b21ca53

import Mathlib
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionZeroSchemeV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_zeroSchemeIdeal_tensorHom_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.support_comap Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.IdealSheafData.support_mul Scheme.Modules Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal_monoidalV2 Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2 Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.support_comap Modules.pullback mk Modules.pullbackCongr Modules.pullbackId IdealSheafData.support_mul Modules IdealSheafData Modules.IsInvertible Modules.zeroSchemeIdeal Modules.pullbackSection Modules.IsInvertible.comap_zeroSchemeIdeal_monoidalV2 Modules.zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2 Modules.IsInvertible.tensor_monoidalV2 Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr pullbackId tensor IsInvertible tensorPow zeroSchemeIdeal pullbackSection IsInvertible.comap_zeroSchemeIdeal_monoidalV2 zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2 IsInvertible.tensor_monoidalV2 IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback mk comap_zeroSchemeIdeal_monoidalV2 tensor_monoidalV2 zeroSchemeIdeal_tensorHom_monoidalV2" end AlgebraicGeometry.Scheme.Modules.IsInvertible
namespace AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal := AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal_monoidalV2
end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal"
namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "Scheme.IdealSheafData.support_comap Scheme.Modules.pullback Spec Scheme Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.IdealSheafData.support_mul Scheme.Modules Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal_monoidalV2 Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2 Scheme.Modules.IsInvertible.tensor_monoidalV2 Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "IdealSheafData.support_comap Modules.pullback mk Modules.pullbackCongr Modules.pullbackId IdealSheafData.support_mul Modules IdealSheafData Modules.IsInvertible Modules.zeroSchemeIdeal Modules.pullbackSection Modules.IsInvertible.comap_zeroSchemeIdeal_monoidalV2 Modules.zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2 Modules.IsInvertible.tensor_monoidalV2 Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback pullbackCongr pullbackId tensor IsInvertible tensorPow zeroSchemeIdeal pullbackSection IsInvertible.comap_zeroSchemeIdeal_monoidalV2 zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2 IsInvertible.tensor_monoidalV2 IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2" end AlgebraicGeometry.Scheme.Modules
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules" in
alias AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso := AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso_monoidalV2
namespace AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
private alias _root_.AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor := AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor_monoidalV2
end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_export "" "AlgebraicGeometry.Scheme.Modules.IsInvertible.tensor"
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in
alias AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom := AlgebraicGeometry.Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom_monoidalV2

universe u

set_option autoImplicit false
section translate_product
p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2.AlgebraicGeometry"
open scoped CategoryTheory.MonObj

namespace TPSol

variable {k : Type u} [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k)) [GrpObj (Over.mk t)]

noncomputable abbrev T (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : X ⟶ X :=
  (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left

set_option pp.explicit true in
theorem T_inv_mul (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) : T t (y⁻¹ * y) = 𝟙 X := by

  have h1 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) = 𝟙 (Over.mk t) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc, GrpObj.comp_inv, inv_mul_cancel, mul_one]
  have h2 : (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y⁻¹)) ≫
      (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)) =
      𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (y⁻¹ * y)) := by
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit,
      mul_assoc]
    congr 1
    exact (MonObj.comp_mul (CartesianMonoidalCategory.toUnit (Over.mk t)) y⁻¹ y).symm
  exact congrArg CommaMorphism.left (h2.symm.trans h1)

theorem support_zeroSchemeIdeal_pullbackSection {X' : Scheme.{u}} (F : X' ⟶ X) {M : X.Modules}
    (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M) :
    ((Scheme.Modules.zeroSchemeIdeal (Scheme.Modules.pullbackSection F s)).support : Set X') =
      F.base ⁻¹' ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) := by
  rw [← hM.comap_zeroSchemeIdeal F s, Scheme.IdealSheafData.support_comap]
  rfl

end TPSol

set_option maxHeartbeats 3200000 in
open TPSol in
theorem solution
    (k : Type u) [Field k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsq : ∀ x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      Nonempty (
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
        (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
        L))
    (θ : 𝟙_ X.Modules ⟶ L)
    (a b : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    ∃ s : 𝟙_ X.Modules ⟶ L.tensorPow 3,
      ((Scheme.Modules.zeroSchemeIdeal s).support : Set X) =
        (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ a)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ b)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) ∪
          (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (a * b)⁻¹)).left.base ⁻¹'
            ((Scheme.Modules.zeroSchemeIdeal θ).support : Set X) := by
  classical

  let c : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t := (a * b)⁻¹
  let Lp : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) → X.Modules := fun x =>
    (Scheme.Modules.pullback (T t x)).obj L
  have hLp : ∀ x, Scheme.Modules.IsInvertible (Lp x) := fun x => hL.pullback _
  let θp : ∀ x, 𝟙_ X.Modules ⟶ Lp x := fun x => Scheme.Modules.pullbackSection (T t x) θ

  let sab : 𝟙_ X.Modules ⟶ Lp a ⊗ Lp b := (λ_ (𝟙_ X.Modules)).inv ≫ (θp a ⊗ₘ θp b)
  let s₀ : 𝟙_ X.Modules ⟶ Lp c ⊗ (Lp a ⊗ Lp b) := (λ_ (𝟙_ X.Modules)).inv ≫ (θp c ⊗ₘ sab)

  have hT1 : T t (c * (a * b)) = 𝟙 X := T_inv_mul t (a * b)
  have e1 : Lp (c * (a * b)) ≅ L :=
    (Scheme.Modules.pullbackCongr hT1).app L ≪≫ (Scheme.Modules.pullbackId X).app L
  have Φ₁ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ Lp c ⊗ (Lp (a * b) ⊗ L) := whiskerLeftIso (Lp c) (hsq a b).some
  have Φ₂ : Lp c ⊗ (Lp (a * b) ⊗ L) ≅ (Lp c ⊗ Lp (a * b)) ⊗ L := (α_ (Lp c) (Lp (a * b)) L).symm
  have Φ₃ : (Lp c ⊗ Lp (a * b)) ⊗ L ≅ (Lp (c * (a * b)) ⊗ L) ⊗ L := whiskerRightIso (hsq c (a * b)).some L
  have Φ₄ : (Lp (c * (a * b)) ⊗ L) ⊗ L ≅ ((𝟙_ X.Modules ⊗ L) ⊗ L) ⊗ L :=
    whiskerRightIso (whiskerRightIso (e1 ≪≫ (λ_ L).symm) L) L
  have Φ : Lp c ⊗ (Lp a ⊗ Lp b) ≅ L.tensorPow 3 := Φ₁ ≪≫ Φ₂ ≪≫ Φ₃ ≪≫ Φ₄
  refine ⟨s₀ ≫ Φ.hom, ?_⟩
  rw [Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso]

  have hZ : Scheme.Modules.zeroSchemeIdeal s₀ =
      Scheme.Modules.zeroSchemeIdeal (θp c) *
        (Scheme.Modules.zeroSchemeIdeal (θp a) * Scheme.Modules.zeroSchemeIdeal (θp b)) := by
    rw [Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom (hLp c) ((hLp a).tensor (hLp b)),
      Scheme.Modules.IsInvertible.zeroSchemeIdeal_tensorHom (hLp a) (hLp b)]
  rw [hZ, Scheme.IdealSheafData.support_mul, Scheme.IdealSheafData.support_mul]
  simp only [TopologicalSpace.Closeds.coe_sup]
  rw [support_zeroSchemeIdeal_pullbackSection (T t c) hL θ, support_zeroSchemeIdeal_pullbackSection (T t a) hL θ,
    support_zeroSchemeIdeal_pullbackSection (T t b) hL θ]
  exact Set.union_comm _ _

end translate_product

end S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_hom_tensorPow_three_support_zeroSchemeIdeal_eq_monoidalV2 (solution)
