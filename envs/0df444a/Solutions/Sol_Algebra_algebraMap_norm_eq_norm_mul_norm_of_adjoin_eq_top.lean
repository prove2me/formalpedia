-- Prove2me | solution 1 for Algebra.algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/98c7e82c-50c2-5065-8e88-732deef244fd

import Mathlib
import Theorems.Thm_Algebra_norm_prod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top

open scoped TensorProduct

namespace NormSplit

theorem surjective_of_adjoin_eq_top
    {F F₁ F₂ E : Type*} [Field F] [Field F₁] [Field F₂] [Field E]
    [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F₁ E] [Algebra F₂ E]
    [IsScalarTower F F₁ E] [IsScalarTower F F₂ E]
    (μ : F₂ ⊗[F] F₁ →ₐ[F₂] E)
    (hμ : ∀ (a : F₂) (b : F₁), μ (a ⊗ₜ b) = algebraMap F₂ E a * algebraMap F₁ E b)
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤) :
    Function.Surjective μ := by
  intro z
  have hz : z ∈ Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) :=
    hgen ▸ Algebra.mem_top
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · exact ⟨1 ⊗ₜ b, by rw [hμ, map_one, one_mul]⟩
    · exact ⟨a ⊗ₜ 1, by rw [hμ, map_one, mul_one]⟩
  | algebraMap r =>
    refine ⟨algebraMap F₂ (F₂ ⊗[F] F₁) (algebraMap F F₂ r), ?_⟩
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  | add x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p + q, map_add μ p q⟩
  | mul x y _ _ hx hy =>
    obtain ⟨p, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨p * q, map_mul μ p q⟩

end NormSplit

theorem solution
    {F F₁ F₂ Z Z' : Type*} [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra F F₁] [Algebra F F₂]
    [Algebra F Z] [Algebra F₁ Z] [Algebra F₂ Z] [IsScalarTower F F₁ Z] [IsScalarTower F F₂ Z]
    [Algebra F Z'] [Algebra F₁ Z'] [Algebra F₂ Z'] [IsScalarTower F F₁ Z'] [IsScalarTower F F₂ Z']
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F₁ Z] [FiniteDimensional F₁ Z']
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ Z) ∪ Set.range (algebraMap F₂ Z)) = ⊤)
    (hgen' : Algebra.adjoin F (Set.range (algebraMap F₁ Z') ∪ Set.range (algebraMap F₂ Z')) = ⊤)
    (hdeg : Module.finrank F₁ Z + Module.finrank F₁ Z' = Module.finrank F F₂)
    (hne : ∃ (a : F₂) (b : F₁), algebraMap F₂ Z' a = algebraMap F₁ Z' b ∧
      algebraMap F₂ Z a ≠ algebraMap F₁ Z b)
    (g : F₁) :
    algebraMap F F₂ (Algebra.norm F g)
      = Algebra.norm F₂ (algebraMap F₁ Z g) * Algebra.norm F₂ (algebraMap F₁ Z' g) := by
  classical

  haveI : FiniteDimensional F Z := Module.Finite.trans F₁ Z
  haveI : FiniteDimensional F Z' := Module.Finite.trans F₁ Z'
  haveI : FiniteDimensional F₂ Z := Module.Finite.of_restrictScalars_finite F F₂ Z
  haveI : FiniteDimensional F₂ Z' := Module.Finite.of_restrictScalars_finite F F₂ Z'

  have hdeg₂ : Module.finrank F₂ Z + Module.finrank F₂ Z' = Module.finrank F F₁ := by
    have hZ := Module.finrank_mul_finrank F F₁ Z
    have hZ₂ := Module.finrank_mul_finrank F F₂ Z
    have hZ' := Module.finrank_mul_finrank F F₁ Z'
    have hZ'₂ := Module.finrank_mul_finrank F F₂ Z'
    have h2 : 0 < Module.finrank F F₂ := Module.finrank_pos
    have key : (Module.finrank F₂ Z + Module.finrank F₂ Z') * Module.finrank F F₂
        = Module.finrank F F₁ * Module.finrank F F₂ := by
      calc (Module.finrank F₂ Z + Module.finrank F₂ Z') * Module.finrank F F₂
          = Module.finrank F Z + Module.finrank F Z' := by rw [add_mul, mul_comm, hZ₂, mul_comm, hZ'₂]
        _ = Module.finrank F F₁ * (Module.finrank F₁ Z + Module.finrank F₁ Z') := by
            rw [mul_add, hZ, hZ']
        _ = Module.finrank F F₁ * Module.finrank F F₂ := by rw [hdeg]
    exact Nat.eq_of_mul_eq_mul_right h2 key

  let m : (F₂ ⊗[F] F₁) →ₐ[F₂] Z := Algebra.TensorProduct.lift (Algebra.ofId F₂ Z)
    (IsScalarTower.toAlgHom F F₁ Z) (fun _ _ => Commute.all _ _)
  let m' : (F₂ ⊗[F] F₁) →ₐ[F₂] Z' := Algebra.TensorProduct.lift (Algebra.ofId F₂ Z')
    (IsScalarTower.toAlgHom F F₁ Z') (fun _ _ => Commute.all _ _)
  have hm : ∀ (a : F₂) (b : F₁), m (a ⊗ₜ b) = algebraMap F₂ Z a * algebraMap F₁ Z b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b
  have hm' : ∀ (a : F₂) (b : F₁), m' (a ⊗ₜ b) = algebraMap F₂ Z' a * algebraMap F₁ Z' b := fun a b =>
    Algebra.TensorProduct.lift_tmul _ _ _ a b

  have hsurj : Function.Surjective m := NormSplit.surjective_of_adjoin_eq_top m hm hgen
  have hsurj' : Function.Surjective m' := NormSplit.surjective_of_adjoin_eq_top m' hm' hgen'

  have hI : (RingHom.ker m).IsMaximal := RingHom.ker_isMaximal_of_surjective m hsurj
  have hJ : (RingHom.ker m').IsMaximal := RingHom.ker_isMaximal_of_surjective m' hsurj'
  have hIJ : RingHom.ker m ≠ RingHom.ker m' := by
    obtain ⟨a, b, hab', hab⟩ := hne
    intro h
    have hx : (a ⊗ₜ (1 : F₁) - (1 : F₂) ⊗ₜ b : (F₂ ⊗[F] F₁)) ∈ RingHom.ker m' := by
      rw [RingHom.mem_ker, map_sub, hm', hm', map_one, map_one, mul_one, one_mul, hab', sub_self]
    rw [← h, RingHom.mem_ker, map_sub, hm, hm, map_one, map_one, mul_one, one_mul, sub_eq_zero] at hx
    exact hab hx
  have hsup : RingHom.ker m ⊔ RingHom.ker m' = ⊤ := Ideal.IsMaximal.coprime_of_ne hI hJ hIJ

  let e : (F₂ ⊗[F] F₁) →ₐ[F₂] Z × Z' := m.prod m'
  have he : ∀ x, e x = (m x, m' x) := fun x => rfl
  have hesurj : Function.Surjective e := by
    rintro ⟨z, z'⟩
    obtain ⟨p, rfl⟩ := hsurj z
    obtain ⟨q, rfl⟩ := hsurj' z'
    have h1 : (1 : (F₂ ⊗[F] F₁)) ∈ RingHom.ker m ⊔ RingHom.ker m' := hsup ▸ Submodule.mem_top
    obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp h1
    refine ⟨p * j + q * i, ?_⟩
    rw [RingHom.mem_ker] at hi hj
    have hmj : m j = 1 := by
      have := congrArg m hij; rw [map_add, hi, zero_add, map_one] at this; exact this
    have hm'i : m' i = 1 := by
      have := congrArg m' hij; rw [map_add, hj, add_zero, map_one] at this; exact this
    rw [he, Prod.mk.injEq, map_add, map_add, map_mul, map_mul, map_mul, map_mul, hi, hj, hmj, hm'i]
    constructor <;> ring

  have hdim : Module.finrank F₂ (F₂ ⊗[F] F₁) = Module.finrank F₂ (Z × Z') := by
    rw [Module.finrank_prod, hdeg₂, Module.finrank_baseChange]
  have heinj : Function.Injective e :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := e.toLinearMap)).mpr hesurj
  let ε : (F₂ ⊗[F] F₁) ≃ₐ[F₂] Z × Z' := AlgEquiv.ofBijective e ⟨heinj, hesurj⟩
  have hε : ε (1 ⊗ₜ g) = (algebraMap F₁ Z g, algebraMap F₁ Z' g) := by
    show e (1 ⊗ₜ g) = _
    rw [he, hm, hm', map_one, map_one, one_mul, one_mul]

  have hN1 : Algebra.norm F₂ ((1 : F₂) ⊗ₜ[F] g : (F₂ ⊗[F] F₁))
      = Algebra.norm F₂ (algebraMap F₁ Z g) * Algebra.norm F₂ (algebraMap F₁ Z' g) := by
    rw [← Algebra.norm_eq_of_algEquiv ε, hε, Algebra.norm_prod]
  have hN2 : Algebra.norm F₂ ((1 : F₂) ⊗ₜ[F] g : (F₂ ⊗[F] F₁)) = algebraMap F F₂ (Algebra.norm F g) := by
    rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange (A := F₂)]
    congr 1
    refine TensorProduct.AlgebraTensorModule.ext fun a b => ?_
    rw [LinearMap.baseChange_tmul]
    show ((1 : F₂) ⊗ₜ[F] g) * (a ⊗ₜ[F] b) = a ⊗ₜ[F] (g * b)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← hN2, hN1]

end S_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
end P2MW
export P2MW.S_Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top (solution)
