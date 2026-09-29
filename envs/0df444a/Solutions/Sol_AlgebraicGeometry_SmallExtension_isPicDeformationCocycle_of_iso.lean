-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isPicDeformationCocycle_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/7f15c58c-d671-5ed7-ac9e-b839ed7eb549

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace PicDefIso

variable {Y : Scheme.{u}} {𝒱 : Y.OrderedAffineCover} {𝓜 𝓜' : Y.Modules}

noncomputable def transport (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) :
    Scheme.Modules.CechTrivialisation 𝒱 𝓜' :=
  fun a => (Scheme.Modules.pullback (𝒱.U a).ι).mapIso e ≪≫ τ a

theorem transport_restrict (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {a : 𝒱.ι} {W : Y.Opens} (h : W ≤ 𝒱.U a) :
    (transport e τ).restrict h = (Scheme.Modules.pullback W.ι).mapIso e ≪≫ τ.restrict h := by
  apply Iso.ext
  simp only [transport, Scheme.Modules.CechTrivialisation.restrict, Iso.trans_hom, Iso.symm_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.map_comp, NatTrans.naturality_assoc, Functor.comp_map]
  simp

theorem transport_transition (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜) (s : 𝒱.Idx 1) :
    (transport e τ).transition s = τ.transition s := by
  simp only [Scheme.Modules.CechTrivialisation.transition, transport_restrict]
  congr 1
  apply Iso.ext
  change ((τ.restrict (𝒱.inter_le s 0)).inv ≫ ((Scheme.Modules.pullback (𝒱.inter s).ι).mapIso e).inv) ≫
      ((Scheme.Modules.pullback (𝒱.inter s).ι).mapIso e).hom ≫ (τ.restrict (𝒱.inter_le s 1)).hom =
    (τ.restrict (𝒱.inter_le s 0)).inv ≫ (τ.restrict (𝒱.inter_le s 1)).hom
  simp

theorem transport_comap_hom (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (a : 𝒱.ι) :
    ((transport e τ).comap h a).hom =
      (Scheme.Modules.pullback h ⋙ Scheme.Modules.pullback (h ⁻¹ᵁ 𝒱.U a).ι).map e.hom ≫ (τ.comap h a).hom := by
  change ((Scheme.Modules.pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜').hom ≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι h (𝒱.U a)).symm).app 𝓜').hom ≫
      ((Scheme.Modules.pullbackComp (h ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜').inv ≫
      (Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map
        (((Scheme.Modules.pullback (𝒱.U a).ι).mapIso e).hom ≫ (τ a).hom) ≫
      (Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)).hom =
    (Scheme.Modules.pullback h ⋙ Scheme.Modules.pullback (h ⁻¹ᵁ 𝒱.U a).ι).map e.hom ≫
      ((Scheme.Modules.pullbackComp (h ⁻¹ᵁ 𝒱.U a).ι h).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackCongr (morphismRestrict_ι h (𝒱.U a)).symm).app 𝓜).hom ≫
      ((Scheme.Modules.pullbackComp (h ∣_ 𝒱.U a) (𝒱.U a).ι).app 𝓜).inv ≫
      (Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map (τ a).hom ≫
      (Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)).hom
  simp only [Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, NatTrans.naturality_assoc]
  simp only [Functor.comp_map, Functor.map_comp]
  erw [Category.assoc ((Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map ((Scheme.Modules.pullback (𝒱.U a).ι).map e.hom))
    ((Scheme.Modules.pullback (h ∣_ 𝒱.U a)).map (τ a).hom) (Scheme.Modules.pullbackUnitIso (h ∣_ 𝒱.U a)).hom]

theorem transport_comap (e : 𝓜' ≅ 𝓜) (τ : Scheme.Modules.CechTrivialisation 𝒱 𝓜)
    {Y' : Scheme.{u}} (h : Y' ⟶ Y) [IsAffineHom h] (a : 𝒱.ι) :
    (transport e τ).comap h a =
      (Scheme.Modules.pullback ((𝒱.comap h).U a).ι).mapIso ((Scheme.Modules.pullback h).mapIso e) ≪≫ τ.comap h a :=
  Iso.ext (transport_comap_hom e τ h a)

end PicDefIso

open PicDefIso in
theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X₀ Xk : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (g : X₀ ⟶ X) [IsAffineHom g]
    (𝒰 : X.OrderedAffineCover)
    {M M' : X.Modules} (e : M ≅ M')
    (φ₀ : (Scheme.Modules.pullback g).obj M ≅ SheafOfModules.unit X₀.ringCatSheaf)
    (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 1)
    (hw : SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M φ₀ w) :
    SmallExtension.IsPicDeformationCocycle V ι f fk i g 𝒰 M'
      ((Scheme.Modules.pullback g).mapIso e.symm ≪≫ φ₀) w := by
  obtain ⟨τ, ea, ea', h1, h2, h3⟩ := hw
  refine ⟨transport e.symm τ, ea, ea', h1, fun a => ?_, fun s => ?_⟩
  · rw [h2 a, transport_comap]
    congr 1
    generalize (Scheme.Modules.pullback g).mapIso e.symm = E
    apply Iso.ext
    change (τ.comap g a).inv ≫ (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map φ₀.hom ≫
        (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom =
      ((τ.comap g a).inv ≫ ((Scheme.Modules.pullback ((𝒰.comap g).U a).ι).mapIso E).inv) ≫
        (Scheme.Modules.pullback ((𝒰.comap g).U a).ι).map (E.hom ≫ φ₀.hom) ≫
        (Scheme.Modules.pullbackUnitIso ((𝒰.comap g).U a).ι).hom
    simp
  · rw [transport_transition]
    exact h3 s

end S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isPicDeformationCocycle_of_iso (solution)
