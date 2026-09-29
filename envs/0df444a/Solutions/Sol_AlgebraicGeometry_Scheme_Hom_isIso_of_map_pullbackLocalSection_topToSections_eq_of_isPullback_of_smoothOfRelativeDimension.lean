-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Hom.isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/1cd940c2-f178-5491-886d-4cbe39bd1b29

import Mathlib
import Definitions.Def_PresheafOfModules_ExteriorPower
import Definitions.Def_AlgebraicGeometry_ModulesDet
import Definitions.Def_AlgebraicGeometry_KaehlerModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_NeronModelInfra_TopFormOrder
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsFrameOn_pullbackLocalSection
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_of_isFrameOn_of_iSup_eq_top
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehlerDifferential_map_of_isAffineOpen_le
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFrameOn_topToSections_iotaMulti_of_forall_exists_basis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped TensorProduct

universe u

namespace OmegaPullBCGC7

theorem isScalarTower_sectionsAlgebra_map {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) {U W : X.Opens} (hW : W ≤ U) :
    letI := f.sectionsAlgebra U; letI := f.sectionsAlgebra W
    letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
    IsScalarTower A Γ(X, U) Γ(X, W) := by
  letI := f.sectionsAlgebra U; letI := f.sectionsAlgebra W
  letI : Algebra Γ(X, U) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ W le_top).hom a =
    (X.presheaf.map (homOfLE hW).op).hom (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U le_top).hom a)
  rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_map]

theorem tensorKaehlerEquiv_one_tmul (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra A B] [Algebra S B] [Algebra R B] [IsScalarTower R A B] [IsScalarTower R S B]
    [Algebra.IsPushout R S A B] (x : Ω[A⁄R]) :
    KaehlerDifferential.tensorKaehlerEquiv R S A B (1 ⊗ₜ x) = KaehlerDifferential.map R S A B x := by
  have h1 : ∀ y, y ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) →
      KaehlerDifferential.tensorKaehlerEquiv R S A B (1 ⊗ₜ y) = KaehlerDifferential.map R S A B y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul, KaehlerDifferential.map_D]
    | zero => simp
    | add y z _ _ hy hz => rw [TensorProduct.tmul_add, map_add, hy, hz, map_add]
    | smul a y _ hy =>
      rw [TensorProduct.tmul_smul, LinearMap.map_smul, ← IsScalarTower.algebraMap_smul B a (1 ⊗ₜ[A] y : B ⊗[A] Ω[A⁄R]),
        LinearEquiv.map_smul, hy, IsScalarTower.algebraMap_smul]
  exact h1 x (by rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top)

theorem appLE_congr' {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = f'.appLE U V (h ▸ e) := by
  subst h; rfl

theorem exists_affineOpen_le {X : Scheme.{u}} (O : X.Opens) (x : X) (hx : x ∈ O) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ O := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx O.2
  exact ⟨W, hW, hxW, hWO⟩

end OmegaPullBCGC7

set_option backward.isDefEq.respectTransparency false in
open OmegaPullBCGC7 in
theorem solution
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    {X Y : Scheme.{u}} (gY : Y ⟶ Spec (CommRingCat.of A)) (gX : X ⟶ Spec (CommRingCat.of B))
    (φ : X ⟶ Y) (hφ : IsPullback φ gX gY (Spec.map (CommRingCat.ofHom (algebraMap A B)))) (d : ℕ)
    [SmoothOfRelativeDimension d gY]
    (θ : (Scheme.Modules.pullback φ).obj (gY.topDifferentials d) ⟶ gX.topDifferentials d)
    (hθ : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : X.Opens) (hW : IsAffineOpen W) (hWU : W ≤ φ ⁻¹ᵁ U),
        letI := gY.sectionsAlgebra U; letI := gX.sectionsAlgebra W
        letI : Algebra Γ(Y, U) Γ(X, W) := (φ.appLE U W hWU).hom.toAlgebra
        ∀ [Algebra A Γ(X, W)] [IsScalarTower A B Γ(X, W)] [IsScalarTower A Γ(Y, U) Γ(X, W)]
          (η : ⋀[Γ(Y, U)]^d (gY.kaehlerPresheaf.obj (op U))),
          (gX.topDifferentials d).presheaf.map (homOfLE hWU).op
              (θ.app (φ ⁻¹ᵁ U) (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U η))) =
            gX.topToSections d W (NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, W) d η)) :
    IsIso θ := by
  classical

  have key : ∀ x : X, ∃ (V : X.Opens) (p : Γ((Scheme.Modules.pullback φ).obj (gY.topDifferentials d), V)),
      x ∈ V ∧ Scheme.Modules.IsFrameOn p V ∧ Scheme.Modules.IsFrameOn (θ.app V p) V := by
    intro x

    obtain ⟨U₀, hyU₀, e, he⟩ :=
      AlgebraicGeometry.Scheme.Hom.exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension gY d (φ.base x)
    obtain ⟨U, hU, hyU, hUU₀⟩ := exists_affineOpen_le U₀ (φ.base x) hyU₀
    letI algAU : Algebra A Γ(Y, U) := gY.sectionsAlgebra U
    obtain ⟨bU, hbU⟩ := he U hUU₀ hU
    have hbij : Function.Bijective (gY.kaehlerToSectionsₗ U) :=
      AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen gY hU
    let κU : (Ω[Γ(Y, U)⁄A]) ≃ₗ[Γ(Y, U)] Γ(gY.kaehler, U) := LinearEquiv.ofBijective (gY.kaehlerToSectionsₗ U) hbij
    let η : Module.Basis (Fin d) Γ(Y, U) (Ω[Γ(Y, U)⁄A]) := bU.map κU.symm

    have hs : Scheme.Modules.IsFrameOn (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U) d η)) U := by
      refine AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis gY d hU η fun W hW hWaff => ?_
      intro
      exact AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le gY hU hWaff hW (ι := Fin d) η
    have hp := AlgebraicGeometry.Scheme.Modules.IsFrameOn.pullbackLocalSection φ hs

    obtain ⟨hW₀, hPO⟩ := AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback gY gX φ hφ U hU
    letI algBW : Algebra B Γ(X, φ ⁻¹ᵁ U) := gX.sectionsAlgebra (φ ⁻¹ᵁ U)
    letI algUW : Algebra Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom.toAlgebra
    letI algAW : Algebra A Γ(X, φ ⁻¹ᵁ U) := ((algebraMap B Γ(X, φ ⁻¹ᵁ U)).comp (algebraMap A B)).toAlgebra
    haveI : IsScalarTower A B Γ(X, φ ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower A Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
      refine IsScalarTower.of_algebraMap_eq fun a => ?_
      change (CommRingCat.ofHom (algebraMap A B) ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
          gX.appLE ⊤ (φ ⁻¹ᵁ U) le_top).hom a =
        (φ.appLE U (φ ⁻¹ᵁ U) le_rfl).hom
          (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ gY.appLE ⊤ U le_top).hom a)
      rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE, appLE_congr' hφ.w,
        Scheme.Hom.comp_appLE, ← Category.assoc (CommRingCat.ofHom _), Scheme.ΓSpecIso_inv_naturality,
        Category.assoc]
      rfl
    haveI : Algebra.IsPushout A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := hPO

    let η₀' : Fin d → Ω[Γ(X, φ ⁻¹ᵁ U)⁄B] := fun i => KaehlerDifferential.map A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) (η i)
    let η₀ : Module.Basis (Fin d) Γ(X, φ ⁻¹ᵁ U) (Ω[Γ(X, φ ⁻¹ᵁ U)⁄B]) :=
      (Algebra.TensorProduct.basis Γ(X, φ ⁻¹ᵁ U) η).map
        (KaehlerDifferential.tensorKaehlerEquiv A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U))
    have hη₀ : ∀ i, η₀ i = η₀' i := by
      intro i
      simp only [η₀, η₀', Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
      exact tensorKaehlerEquiv_one_tmul A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) (η i)

    have hq := hθ U hU (φ ⁻¹ᵁ U) hW₀ le_rfl (exteriorPower.ιMulti Γ(Y, U) d η)
    have hid : (homOfLE (le_refl (φ ⁻¹ᵁ U))).op = 𝟙 (op (φ ⁻¹ᵁ U)) := rfl
    rw [hid, CategoryTheory.Functor.map_id] at hq
    have hRHS : NeronModelInfra.TopFormOrder.topFormMap A B Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) d
        (exteriorPower.ιMulti Γ(Y, U) d η) = exteriorPower.ιMulti Γ(X, φ ⁻¹ᵁ U) d η₀' := by
      unfold NeronModelInfra.TopFormOrder.topFormMap
      rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      rfl
    have hθp : θ.app (φ ⁻¹ᵁ U)
          (Scheme.Modules.pullbackLocalSection φ (gY.topToSections d U (exteriorPower.ιMulti Γ(Y, U) d η))) =
        gX.topToSections d (φ ⁻¹ᵁ U) (exteriorPower.ιMulti Γ(X, φ ⁻¹ᵁ U) d η₀') := by
      exact hq.trans (congrArg (gX.topToSections d (φ ⁻¹ᵁ U)) hRHS)
    refine ⟨φ ⁻¹ᵁ U, _, hyU, hp, ?_⟩
    rw [hθp]
    refine AlgebraicGeometry.Scheme.Hom.isFrameOn_topToSections_iotaMulti_of_forall_exists_basis gX d hW₀ η₀' fun W' hW' hW'aff => ?_
    intro
    obtain ⟨b', hb'⟩ := AlgebraicGeometry.Scheme.Hom.exists_basis_kaehlerDifferential_map_of_isAffineOpen_le gX hW₀ hW'aff hW' (ι := Fin d) η₀
    exact ⟨b', fun i => by rw [hb' i, hη₀ i]⟩

  choose V p hV using key
  refine AlgebraicGeometry.Scheme.Modules.isIso_of_isFrameOn_of_iSup_eq_top θ V ?_ p (fun x => θ.app (V x) (p x))
    (fun x => (hV x).2.1) (fun x => (hV x).2.2) (fun x => rfl)
  exact top_le_iff.mp fun x _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨x, (hV x).1⟩

end S_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Hom_isIso_of_map_pullbackLocalSection_topToSections_eq_of_isPullback_of_smoothOfRelativeDimension (solution)
