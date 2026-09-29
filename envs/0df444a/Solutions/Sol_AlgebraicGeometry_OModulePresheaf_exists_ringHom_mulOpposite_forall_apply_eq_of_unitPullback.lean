-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/57f2deb6-5439-5a0d-a034-a453006f0d6a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld CerednikDrinfeld.QM
open scoped TensorProduct

theorem solution
    {κ : Type} [Field κ] {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of κ)) (L : RelativeGroupLaw κ fX)
    (𝒦 : X.OrderedAffineCover)
    (H₁ : Type) [AddCommGroup H₁] [Module κ H₁]
    (cls₁ : ↥(LinearMap.ker ((OModulePresheaf.unit fX).d 𝒦 1)) →ₗ[κ] H₁)
    (ρ : ∀ φ : X ⟶ X, φ ≫ fX = fX → (H₁ →ₗ[κ] H₁))
    (hρid : ρ (𝟙 X) (Category.id_comp fX) = LinearMap.id)
    (hρcomp : ∀ (φ φ' : X ⟶ X) (hφ : φ ≫ fX = fX) (hφ' : φ' ≫ fX = fX),
      ρ (φ ≫ φ') (by rw [Category.assoc, hφ', hφ]) = (ρ φ hφ).comp (ρ φ' hφ'))
    (hρadd : ∀ (φ φ' χ : X ⟶ X) (hφ : φ ≫ fX = fX) (hφ' : φ' ≫ fX = fX) (hχ : χ ≫ fX = fX),
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P : SchemeHomOver t fX),
          P.1 ≫ χ = (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩ ⟨P.1 ≫ φ', by rw [Category.assoc, hφ']; exact P.2⟩).1) →
      ρ χ hχ = ρ φ hφ + ρ φ' hφ')
    (hρpin : ∀ (φ : X ⟶ X) (hφ : φ ≫ fX = fX) (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
        (hl : ∀ v, 𝒱.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit fX).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := fX) φ 𝒱 𝒦 lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := fX) (𝟙 X) 𝒱 𝒦 lam' hl' (0 + 1) z'.1 ∈ LinearMap.range ((OModulePresheaf.unit fX).d 𝒱 0) →
        ρ φ hφ (cls₁ z) = cls₁ z')
    {Λ : Type} [Ring Λ] (ψ : Λ → (X ⟶ X)) (hψ : ∀ x : Λ, ψ x ≫ fX = fX)
    (hψone : ψ 1 = 𝟙 X) (hψmul : ∀ x y : Λ, ψ (x * y) = ψ y ≫ ψ x)
    (hψadd : ∀ (x y : Λ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of κ)) (P : SchemeHomOver t fX),
      P.1 ≫ ψ (x + y) = (L.mul t ⟨P.1 ≫ ψ x, by rw [Category.assoc, hψ, P.2]⟩ ⟨P.1 ≫ ψ y, by rw [Category.assoc, hψ, P.2]⟩).1) :
    ∃ ρΛ : Λᵐᵒᵖ →+* Module.End κ H₁,
      ∀ (x : Λ) (𝒱 : X.OrderedAffineCover) (lam lam' : 𝒱.ι → 𝒦.ι)
        (hl : ∀ v, 𝒱.U v ≤ ψ x ⁻¹ᵁ 𝒦.U (lam v)) (hl' : ∀ v, 𝒱.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam' v))
        (z z' : ↥(LinearMap.ker ((OModulePresheaf.unit fX).d 𝒦 1))),
        OModulePresheaf.unitPullback (πX := fX) (ψ x) 𝒱 𝒦 lam hl (0 + 1) z.1 -
            OModulePresheaf.unitPullback (πX := fX) (𝟙 X) 𝒱 𝒦 lam' hl' (0 + 1) z'.1 ∈ LinearMap.range ((OModulePresheaf.unit fX).d 𝒱 0) →
        ρΛ (MulOpposite.op x) (cls₁ z) = cls₁ z' := by
  have hcongr : ∀ (φ φ' : X ⟶ X) (h : φ = φ') (hφ : φ ≫ fX = fX) (hφ' : φ' ≫ fX = fX), ρ φ hφ = ρ φ' hφ' := by
    rintro φ φ' rfl hφ hφ'; rfl
  let R : Λᵐᵒᵖ → Module.End κ H₁ := fun x => ρ (ψ x.unop) (hψ x.unop)
  have hone : R 1 = 1 := by
    show ρ (ψ 1) (hψ 1) = LinearMap.id
    rw [hcongr (ψ 1) (𝟙 X) hψone (hψ 1) (Category.id_comp fX), hρid]
  have hmul : ∀ x y : Λᵐᵒᵖ, R (x * y) = R x * R y := by
    intro x y
    show ρ (ψ (y.unop * x.unop)) (hψ _) = (ρ (ψ x.unop) (hψ _)).comp (ρ (ψ y.unop) (hψ _))
    rw [hcongr _ _ (hψmul y.unop x.unop) (hψ _) (by rw [Category.assoc, hψ, hψ]), hρcomp]
  have haddR : ∀ x y : Λᵐᵒᵖ, R (x + y) = R x + R y := by
    intro x y
    show ρ (ψ (x.unop + y.unop)) (hψ _) = ρ (ψ x.unop) (hψ _) + ρ (ψ y.unop) (hψ _)
    exact hρadd (ψ x.unop) (ψ y.unop) (ψ (x.unop + y.unop)) (hψ _) (hψ _) (hψ _)
      (fun t P => hψadd x.unop y.unop t P)
  have hzero : R 0 = 0 := by
    have h := haddR 0 0
    rw [add_zero] at h
    have h2 : R 0 + R 0 = R 0 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  refine ⟨{ toFun := R, map_one' := hone, map_mul' := hmul, map_zero' := hzero, map_add' := haddR }, ?_⟩
  intro x 𝒱 lam lam' hl hl' z z' hz
  exact hρpin (ψ x) (hψ x) 𝒱 lam lam' hl hl' z z' hz

end S_AlgebraicGeometry_OModulePresheaf_exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_ringHom_mulOpposite_forall_apply_eq_of_unitPullback (solution)
