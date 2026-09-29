-- Prove2me | solution 1 for AlgebraicGeometry.SmallExtension.IsFibreReading.appLE_of_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/58759fba-dac0-56d6-9cbd-8255a560874e

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_CechPicardObstruction
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
p2m_open "AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u

theorem solution
    {B₁ : Type u} [CommRing B₁] {k : Type u} [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] [Module B₁ V] (ι : V →ₗ[B₁] B₁)
    {X X' Xk Xk' : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of B₁)) (f' : X' ⟶ Spec (CommRingCat.of B₁))
    (fk : Xk ⟶ Spec (CommRingCat.of k)) (fk' : Xk' ⟶ Spec (CommRingCat.of k))
    (i : Xk ⟶ X) (i' : Xk' ⟶ X')
    (h : X' ⟶ X) (hh : h ≫ f = f')
    (hk : Xk' ⟶ Xk) (hhk : hk ≫ i = i' ≫ h) (hfk : hk ≫ fk = fk')
    (U : X.Opens) (W : Xk.Opens) (hW : W ≤ i ⁻¹ᵁ U)
    (U' : X'.Opens) (hU' : U' ≤ h ⁻¹ᵁ U) (W' : Xk'.Opens) (hW' : W' ≤ i' ⁻¹ᵁ U') (hWk : W' ≤ hk ⁻¹ᵁ W)
    (δ : Γ(X, U)) (w : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk).obj W)
    (w' : Module.Dual k V →ₗ[k] (OModulePresheaf.unit fk').obj W')
    (hw' : ∀ ξ : Module.Dual k V, w' ξ = (hk.appLE W W' hWk).hom (w ξ))
    (hw : IsFibreReading V ι f fk i U W hW δ w) :
    IsFibreReading V ι f' fk' i' U' W' hW' ((h.appLE U U' hU').hom δ) w' := by
  classical
  letI algU : Algebra B₁ Γ(X, U) := algebraOfHom f U
  letI algU' : Algebra B₁ Γ(X', U') := algebraOfHom f' U'
  letI algW : Algebra k Γ(Xk, W) := algebraOfHom fk W
  letI algW' : Algebra k Γ(Xk', W') := algebraOfHom fk' W'

  have hcompat : ∀ b : B₁, (h.appLE U U' hU').hom (algebraMap B₁ Γ(X, U) b) = algebraMap B₁ Γ(X', U') b := by
    intro b
    show (h.appLE U U' hU').hom ((f.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b)) =
      (f'.appLE ⊤ U' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b)
    have := congrArg (fun k => k.hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom b))
      (Scheme.Hom.appLE_comp_appLE h f ⊤ U U' le_top hU')
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    subst hh
    rfl

  have hkcompat : ∀ c : k, (hk.appLE W W' hWk).hom (algebraMap k Γ(Xk, W) c) = algebraMap k Γ(Xk', W') c := by
    intro c
    show (hk.appLE W W' hWk).hom ((fk.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) =
      (fk'.appLE ⊤ W' le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
    have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
      (Scheme.Hom.appLE_comp_appLE hk fk ⊤ W W' le_top hWk)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    rw [this]
    subst hfk
    rfl
  have hsq : ∀ s : Γ(X, U), (hk.appLE W W' hWk).hom ((Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom s)) =
      (Xk'.presheaf.map (homOfLE hW').op).hom ((i'.app U').hom ((h.appLE U U' hU').hom s)) := by
    intro s

    have e1 : (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom s) = (i.appLE U W hW).hom s := rfl
    have e2 : (Xk'.presheaf.map (homOfLE hW').op).hom ((i'.app U').hom ((h.appLE U U' hU').hom s)) =
        (i'.appLE U' W' hW').hom ((h.appLE U U' hU').hom s) := rfl
    rw [e1, e2]
    have a := congrArg (fun q => q.hom s) (Scheme.Hom.appLE_comp_appLE hk i U W W' hW hWk)
    have b := congrArg (fun q => q.hom s) (Scheme.Hom.appLE_comp_appLE i' h U U' W' hU' hW')
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at a b
    rw [a, b]

    have : ∀ (p q : Xk' ⟶ X) (hpq : p = q) (e₁ : W' ≤ p ⁻¹ᵁ U) (e₂ : W' ≤ q ⁻¹ᵁ U), (p.appLE U W' e₁).hom s = (q.appLE U W' e₂).hom s := by
      intro p q hpq e₁ e₂; subst hpq; rfl
    exact this _ _ hhk _ _

  obtain ⟨n, v, s, hδ, hwξ⟩ := hw
  refine ⟨n, v, fun j => (h.appLE U U' hU').hom (s j), ?_, ?_⟩
  · rw [← hδ, map_sum]
    simp only [map_mul, hcompat]
  · intro ξ
    rw [hw' ξ, hwξ ξ]
    change (hk.appLE W W' hWk).hom (∑ j, algebraMap k (Xk.presheaf.obj (op W)) (ξ (v j)) * (Xk.presheaf.map (homOfLE hW).op).hom ((i.app U).hom (s j))) =
      ∑ j, algebraMap k (Xk'.presheaf.obj (op W')) (ξ (v j)) * (Xk'.presheaf.map (homOfLE hW').op).hom ((i'.app U').hom ((h.appLE U U' hU').hom (s j)))
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hkcompat, hsq]

end S_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq
end P2MW
export P2MW.S_AlgebraicGeometry_SmallExtension_IsFibreReading_appLE_of_comp_eq (solution)
