-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.isPicObstructionCocycle_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/6bed33d0-aecc-526a-a6db-5cf054dbd4a1

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_of_iso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B₁))
    {X₀ : Scheme.{u}} (g : X₀ ⟶ X) [IsAffineHom g]
    {Xk : Scheme.{u}} (fk : Xk ⟶ Spec (CommRingCat.of k)) (i : Xk ⟶ X) [IsAffineHom i]
    (𝒰 : X.OrderedAffineCover)
    (𝓛₀ 𝓜₀ : X₀.Modules) (e : 𝓛₀ ≅ 𝓜₀) (c : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).cochain (𝒰.comap i) 2)
    (hc : IsPicObstructionCocycle V ι f fk i g 𝒰 𝓛₀ c) :
    IsPicObstructionCocycle V ι f fk i g 𝒰 𝓜₀ c := by
  obtain ⟨τ, u, u', hu, huu', hδ⟩ := hc

  let τ' : Scheme.Modules.CechTrivialisation (𝒰.comap g) 𝓜₀ := fun a =>
    (Scheme.Modules.pullback (((𝒰.comap g).U a).ι)).mapIso e.symm ≪≫ τ a

  have hres : ∀ {a : (𝒰.comap g).ι} {W : X₀.Opens} (h : W ≤ (𝒰.comap g).U a),
      Scheme.Modules.CechTrivialisation.restrict τ' h =
        (Scheme.Modules.pullback W.ι).mapIso e.symm ≪≫ Scheme.Modules.CechTrivialisation.restrict τ h := by
    intro a W h
    have n1 := (Scheme.Modules.pullbackCongr (X₀.homOfLE_ι h)).inv.naturality e.inv
    have n2 := (Scheme.Modules.pullbackComp (X₀.homOfLE h) ((𝒰.comap g).U a).ι).inv.naturality e.inv
    apply Iso.ext
    simp only [Scheme.Modules.CechTrivialisation.restrict, τ', Functor.mapIso_trans, Iso.trans_hom, Iso.symm_hom,
      Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
    rw [reassoc_of% n1]
    erw [reassoc_of% n2]
  have htrans : ∀ s, Scheme.Modules.CechTrivialisation.transition τ' s =
      Scheme.Modules.CechTrivialisation.transition τ s := by
    intro s
    have hiso : (Scheme.Modules.CechTrivialisation.restrict τ' ((𝒰.comap g).inter_le s 0)).symm ≪≫
          Scheme.Modules.CechTrivialisation.restrict τ' ((𝒰.comap g).inter_le s 1) =
        (Scheme.Modules.CechTrivialisation.restrict τ ((𝒰.comap g).inter_le s 0)).symm ≪≫
          Scheme.Modules.CechTrivialisation.restrict τ ((𝒰.comap g).inter_le s 1) := by
      rw [hres, hres]
      apply Iso.ext
      simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Functor.mapIso_hom, Functor.mapIso_inv, Iso.symm_inv,
        Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Scheme.Modules.CechTrivialisation.transition]
    exact congrArg (Scheme.Modules.unitAutSection _) hiso
  exact ⟨τ', u, u', fun s => (hu s).trans (htrans s).symm, huu', hδ⟩

end S_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_of_iso
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_isPicObstructionCocycle_of_iso (solution)
