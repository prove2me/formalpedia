-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/d0a11ee5-c369-5148-849e-a72deb1d5c5a

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme.TwoAffineOpenCover"
open scoped TensorProduct

universe u

namespace PV6K1bR

theorem appLE_congr_hom {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ φ ⁻¹ᵁ U) (e' : V ≤ ψ ⁻¹ᵁ U) : φ.appLE U V e = ψ.appLE U V e' := by
  subst h; rfl

end PV6K1bR

open PV6K1bR in
theorem solution
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (π : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (A : Type u) [CommRing A] [Algebra R A]
    (𝒰 𝒱 : Y.OrderedAffineCover)

    (h : pullback π (specMap R A) ⟶ pullback π (specMap R A))
    (hh : h ≫ pullback.snd π (specMap R A) = pullback.snd π (specMap R A))
    (lam : 𝒱.ι → 𝒰.ι) (hl : ∀ v, (𝒱.baseChange π A).U v ≤ h ⁻¹ᵁ (𝒰.baseChange π A).U (lam v))
    (n : ℕ) (z : (OModulePresheaf.unit (pullback.snd π (specMap R A))).cochain (𝒰.baseChange π A) n)
    (s : 𝒱.Idx n) (hinj : Function.Injective (lam ∘ s.1))

    (σ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      (A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))) ≃+*
        Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hσ₁ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ y : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)),
        σ ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map
              (homOfLE (𝒰.baseChange_inter_le π A ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).op).hom
            (((pullback.fst π (specMap R A)).app (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom y))
    (hσ₂ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom (pullback.snd π (specMap R A))
        ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))) =
        algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) a)
    (σV : letI := algebraOfHom π (𝒱.inter s)
      (A ⊗[R] Γ(Y, 𝒱.inter s)) ≃+* Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s))
    (hσV₁ : letI := algebraOfHom π (𝒱.inter s)
      ∀ y : Γ(Y, 𝒱.inter s),
        σV ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒱.baseChange_inter_le π A s)).op).hom
            (((pullback.fst π (specMap R A)).app (𝒱.inter s)).hom y))
    (hσV₂ : letI := algebraOfHom π (𝒱.inter s)
      letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒱.baseChange π A).inter s)
      ∀ a : A, σV (a ⊗ₜ[R] (1 : Γ(Y, 𝒱.inter s))) = algebraMap A Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s) a)

    (θ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom π (𝒱.inter s)
      Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) →ₐ[R] Γ(Y, 𝒱.inter s))
    (hθ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom π (𝒱.inter s)
      ∀ y : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)),
        ((pullback π (specMap R A)).presheaf.map
            (homOfLE ((𝒱.baseChange π A).inter_le_preimage_inter_sortIdx h (𝒰.baseChange π A) lam hl s hinj)).op).hom
          ((h.app ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom
            (((pullback π (specMap R A)).presheaf.map
                (homOfLE (𝒰.baseChange_inter_le π A ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).op).hom
              (((pullback.fst π (specMap R A)).app (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom y))) =
        ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒱.baseChange_inter_le π A s)).op).hom
          (((pullback.fst π (specMap R A)).app (𝒱.inter s)).hom (θ y)))

    (x : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hx : σ x = z ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) :
    letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
    letI := algebraOfHom π (𝒱.inter s)
    OModulePresheaf.unitPullback (πX := pullback.snd π (specMap R A)) h (𝒱.baseChange π A) (𝒰.baseChange π A) lam hl n z s =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        σV ((Algebra.TensorProduct.map (AlgHom.id A A) θ) x) := by
  classical
  letI iU := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
  letI iV := algebraOfHom π (𝒱.inter s)
  letI iUA := algebraOfHom (pullback.snd π (specMap R A)) ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
  letI iVA := algebraOfHom (pullback.snd π (specMap R A)) ((𝒱.baseChange π A).inter s)
  rw [OModulePresheaf.unitPullback_apply_of_injective h (𝒱.baseChange π A) (𝒰.baseChange π A) lam hl n z s hinj, ← hx]
  congr 1
  clear hx

  have hA : ∀ a : A,
      ((pullback π (specMap R A)).presheaf.map
          (homOfLE ((𝒱.baseChange π A).inter_le_preimage_inter_sortIdx h (𝒰.baseChange π A) lam hl s hinj)).op).hom
        ((h.app ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom (algebraMap A Γ((pullback π (specMap R A)), ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))) a)) =
      algebraMap A Γ((pullback π (specMap R A)), ((𝒱.baseChange π A).inter s)) a := by
    intro a
    change ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.snd π (specMap R A)).appLE ⊤ ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) le_top ≫ h.app ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) ≫
        (pullback π (specMap R A)).presheaf.map
          (homOfLE ((𝒱.baseChange π A).inter_le_preimage_inter_sortIdx h (𝒰.baseChange π A) lam hl s hinj)).op).hom a =
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (pullback.snd π (specMap R A)).appLE ⊤ ((𝒱.baseChange π A).inter s) le_top).hom a
    congr 2
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE, appLE_congr_hom hh]
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y ihx ihy => simp only [map_add, ihx, ihy]
  | tmul a y =>
    have e : a ⊗ₜ[R] y = (a ⊗ₜ[R] (1 : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))) *
        ((1 : A) ⊗ₜ[R] y) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [e, map_mul, map_mul, map_mul, map_mul, map_mul, hσ₂, hσ₁, hA, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgHom.id_apply, map_one, hσV₂, hσV₁, hθ]

#print axioms solution

end S_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin (solution)
