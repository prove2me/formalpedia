-- Prove2me | solution 1 for AlgebraicGeometry.GradedOAlgebra.IsSectionRing.isBaseChange_of_apply_eq_pullback_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/2f590edb-8144-58d9-adcd-42c08402ab17

import Definitions.Def_AlgebraicGeometry_GradedOAlgebraSectionRing
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensorProduct_linearEquiv_sections_pullback_of_flat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensorPow_monoidalV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_isBaseChange_of_apply_eq_pullback_of_flat
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free PresheafOfModules.ExteriorPower.instModulePresheafAb"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules"
open scoped TensorProduct

theorem solution
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.Flat S S']
    {X X' : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of S)) [QuasiCompact f] [IsSeparated f]
    (f' : X' ⟶ Spec (CommRingCat.of S')) (c : X' ⟶ X)
    (hc : IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))))
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (L' : X'.Modules) (e : (Scheme.Modules.pullback c).obj L ≅ L')
    (R : Type u) [CommRing R] [Algebra S R] (𝓡 : ℕ → Submodule S R) [GradedAlgebra 𝓡]
    (ι : ∀ n : ℕ, 𝓡 n → Γ(L.tensorPow n, ⊤)) (hR : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f L R 𝓡 ι)
    (R' : Type u) [CommRing R'] [Algebra S' R'] [Algebra S R'] [IsScalarTower S S' R']
    (𝓡' : ℕ → Submodule S' R') [GradedAlgebra 𝓡']
    (ι' : ∀ n : ℕ, 𝓡' n → Γ(L'.tensorPow n, ⊤)) (hR' : AlgebraicGeometry.GradedOAlgebra.IsSectionRing f' L' R' 𝓡' ι')
    (θ : R →ₐ[S] R') (hθdeg : ∀ n, ∀ x ∈ 𝓡 n, θ x ∈ 𝓡' n)
    (hθ : ∀ (n : ℕ) (x : 𝓡 n), ι' n ⟨θ x, hθdeg n x x.2⟩ =
        ((Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n).hom.app ⊤)
          ((((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (L.tensorPow n)).app ⊤) (ι n x)))
    (n : ℕ) :
    IsBaseChange S' ((θ.toLinearMap.restrict (p := 𝓡 n) (q := (𝓡' n).restrictScalars S) (hθdeg n))
      : 𝓡 n →ₗ[S] (𝓡' n).restrictScalars S) := by
  classical

  letI aS : Algebra S Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ f.appTop).hom.toAlgebra
  letI mS : Module S Γ(L.tensorPow n, ⊤) := Module.compHom _ (algebraMap S Γ(X, ⊤))
  letI aS' : Algebra S' Γ(X', ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of S')).inv ≫ f'.appTop).hom.toAlgebra
  letI mS'₁ : Module S' Γ((Scheme.Modules.pullback c).obj (L.tensorPow n), ⊤) := Module.compHom _ (algebraMap S' Γ(X', ⊤))
  letI mS'₂ : Module S' Γ(L'.tensorPow n, ⊤) := Module.compHom _ (algebraMap S' Γ(X', ⊤))

  obtain ⟨β, hβ⟩ := AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_tensorProduct_linearEquiv_sections_pullback_of_flat
    S' f f' c hc (L.tensorPow n) (hL.tensorPow_monoidalV2 n)

  let ιL : ↥(𝓡 n) ≃ₗ[S] Γ(L.tensorPow n, ⊤) :=
    LinearEquiv.ofBijective
      { toFun := ι n
        map_add' := hR.map_add n
        map_smul' := fun s x => hR.map_smul n s x } (hR.bijective n)
  let ιL' : ↥(𝓡' n) ≃ₗ[S'] Γ(L'.tensorPow n, ⊤) :=
    LinearEquiv.ofBijective
      { toFun := ι' n
        map_add' := hR'.map_add n
        map_smul' := fun s x => hR'.map_smul n s x } (hR'.bijective n)

  let I := Scheme.Modules.pullbackTensorPowIso c L n ≪≫ Scheme.Modules.tensorPowMapIso e n
  let γ : Γ((Scheme.Modules.pullback c).obj (L.tensorPow n), ⊤) ≃ₗ[S'] Γ(L'.tensorPow n, ⊤) :=
    { toFun := fun x => I.hom.app ⊤ x
      invFun := fun y => I.inv.app ⊤ y
      map_add' := fun x y => (I.hom.app ⊤).hom.map_add x y
      map_smul' := fun s x => by
        change I.hom.app ⊤ ((algebraMap S' Γ(X', ⊤) s) • x) = (algebraMap S' Γ(X', ⊤) s) • I.hom.app ⊤ x
        exact Scheme.Modules.Hom.app_smul _ _ _
      left_inv := fun x => by
        change (I.hom.app ⊤ ≫ I.inv.app ⊤) x = x
        rw [← Scheme.Modules.Hom.comp_app, I.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
      right_inv := fun y => by
        change (I.inv.app ⊤ ≫ I.hom.app ⊤) y = y
        rw [← Scheme.Modules.Hom.comp_app, I.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl }

  let E : S' ⊗[S] ↥(𝓡 n) ≃ₗ[S'] ↥(𝓡' n) := (((ιL.baseChange S S' _ _).trans β).trans γ).trans ιL'.symm
  refine IsBaseChange.of_equiv E fun x => ?_
  apply ιL'.injective
  change ιL' (ιL'.symm (γ (β ((ιL.baseChange S S' _ _) (1 ⊗ₜ x))))) = ι' n ⟨θ x, hθdeg n x x.2⟩
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.baseChange_tmul, hθ n x]
  change I.hom.app ⊤ (β (1 ⊗ₜ ι n x)) = _
  rw [hβ]

end S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_isBaseChange_of_apply_eq_pullback_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_GradedOAlgebra_IsSectionRing_isBaseChange_of_apply_eq_pullback_of_flat (solution)
