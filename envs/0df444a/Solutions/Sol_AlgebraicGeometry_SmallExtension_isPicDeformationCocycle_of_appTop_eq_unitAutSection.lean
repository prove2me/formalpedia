-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_appTop_eq_unitAutSection
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/cf5aa62a-5120-57f9-bb8b-e5d7191539e3

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_trans_and_unitAutSection_refl
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace PicDefRescale

theorem uAS_trans {Y : Scheme.{u}} (W : Y.Opens)
    (e₁ e₂ : SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :
    Scheme.Modules.unitAutSection W (e₁ ≪≫ e₂) =
      Scheme.Modules.unitAutSection W e₁ * Scheme.Modules.unitAutSection W e₂ :=
  (Scheme.Modules.unitAutSection_trans_and_unitAutSection_refl W).1 e₁ e₂

theorem unit_app_one_res {Y : Scheme.{u}} (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf)
    {U V : Y.Opens} (i : V ⟶ U) :
    (Y.presheaf.map i.op).hom ((ψ.hom.val.app (op U)).hom (1 : Y.presheaf.obj (op U))) =
      (ψ.hom.val.app (op V)).hom (1 : Y.presheaf.obj (op V)) := by
  have h := PresheafOfModules.naturality_apply ψ.hom.val i.op (1 : Y.presheaf.obj (op U))

  erw [PresheafOfModules.unit_map_one] at h
  exact h.symm

theorem uAS_conj_res {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (Scheme.Modules.unitAutSection ⊤
          ((Scheme.Modules.pullbackUnitIso (⊤ : Y.Opens).ι).symm ≪≫
            (Scheme.Modules.pullback (⊤ : Y.Opens).ι).mapIso ψ ≪≫
            Scheme.Modules.pullbackUnitIso (⊤ : Y.Opens).ι)) := by
  rw [Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one,
    Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one, unit_app_one_res]

variable {X : Scheme.{u}}

theorem res_res {U V : X.Opens} (h : V ≤ U) (x : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom x := by
  have hc : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ X.presheaf.map (homOfLE h).op =
      X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [← Functor.map_comp]; rfl
  rw [← hc]; rfl

end PicDefRescale

open PicDefRescale in
theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    (M : X.Modules)
    (φ₀ φ₀' : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (u u' : Γ(X, ⊤)) (huu' : u * u' = 1)
    (hu : g.appTop.hom u =
      Scheme.Modules.unitAutSection ⊤
        ((Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι).symm ≪≫
          (Scheme.Modules.pullback (⊤ : X₀.Opens).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
          Scheme.Modules.pullbackUnitIso (⊤ : X₀.Opens).ι))
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀' w := by
  obtain ⟨τ, ea, ea', h1, h2, h3⟩ := hw

  let ru : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => (X.presheaf.map (homOfLE (le_top : 𝒰.U a ≤ ⊤)).op).hom u
  let ru' : ∀ a : 𝒰.ι, Γ(X, 𝒰.U a) := fun a => (X.presheaf.map (homOfLE (le_top : 𝒰.U a ≤ ⊤)).op).hom u'
  have hru : ∀ a, ru a * ru' a = 1 := fun a => by
    simp only [ru, ru', ← map_mul, huu', map_one]
  refine ⟨τ, fun a => ea a * ru a, fun a => ea' a * ru' a, fun a => ?_, fun a => ?_, fun s => ?_⟩
  ·
    calc ea a * ru a * (ea' a * ru' a) = (ea a * ea' a) * (ru a * ru' a) := by ring
      _ = 1 := by rw [h1 a, hru a, one_mul]
  ·
    have hsplit : ((τ.comap g a).symm ≪≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀' ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι :
          SheafOfModules.unit (((𝒰.comap g).U a : Scheme.{u})).ringCatSheaf ≅
            SheafOfModules.unit (((𝒰.comap g).U a : Scheme.{u})).ringCatSheaf) =
        ((τ.comap g a).symm ≪≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀ ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) ≪≫
        ((Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).symm ≪≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
            Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) := by
      apply Iso.ext
      change (τ.comap g a).inv ≫ (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map φ₀'.hom ≫
          (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom =
        ((τ.comap g a).inv ≫ (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map φ₀.hom ≫
          (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom) ≫
        ((Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).inv ≫
          (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map (φ₀.inv ≫ φ₀'.hom) ≫
            (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom)
      simp
    have key : Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((τ.comap g a).symm ≪≫
            (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀' ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) =
        Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((τ.comap g a).symm ≪≫
            (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso φ₀ ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) *
        Scheme.Modules.unitAutSection ((𝒰.comap g).U a)
          ((Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).symm ≪≫
            (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso (φ₀.symm ≪≫ φ₀') ≪≫
              Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι) := by
      rw [hsplit]
      exact uAS_trans _ _ _
    refine Eq.trans ?_ key.symm
    rw [map_mul, ← h2 a, uAS_conj_res, ← hu]
    congr 1

    have nat := congrArg (fun φ => φ.hom u) (g.naturality (homOfLE (le_top : 𝒰.U a ≤ ⊤)).op)
    exact nat
  ·
    have hres : (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ru' (s.1 0)) *
        (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ru (s.1 1)) = 1 := by
      simp only [ru, ru', res_res, ← map_mul, ← map_one (X.presheaf.map (homOfLE (le_top : 𝒰.inter s ≤ ⊤)).op).hom,
        mul_comm u' u, huu']
    have key : τ.transition s *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0) * ru' (s.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1) * ru (s.1 1)) - 1 =
        τ.transition s *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0)) *
          (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1)) - 1 := by
      rw [map_mul, map_mul]
      calc _ = τ.transition s *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ea' (s.1 0)) *
            (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ea (s.1 1)) *
            ((X.presheaf.map (homOfLE (𝒰.inter_le s 0)).op).hom (ru' (s.1 0)) *
              (X.presheaf.map (homOfLE (𝒰.inter_le s 1)).op).hom (ru (s.1 1))) - 1 := by ring
        _ = _ := by rw [hres, mul_one]
    rw [key]
    exact h3 s

end S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_appTop_eq_unitAutSection (solution)
