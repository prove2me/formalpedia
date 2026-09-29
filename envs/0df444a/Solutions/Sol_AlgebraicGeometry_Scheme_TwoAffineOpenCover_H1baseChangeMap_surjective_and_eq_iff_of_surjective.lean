-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.TwoAffineOpenCover.H1baseChangeMap_surjective_and_eq_iff_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.122355+00:00
-- url     : https://prove2.me/submissions/23a078b5-29a8-5301-85a9-9fdd74b3bf04

import Mathlib
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCoverH1BaseChange
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_baseChangeIsos_structureSheaf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra AlgebraicGeometry.Scheme.TwoAffineOpenCover

open scoped TensorProduct

namespace PicTanH1BC

section Algebra

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Algebra R A]

theorem exists_eq_one_tmul (hA : Function.Surjective (algebraMap R A)) {P : Type*} [AddCommGroup P] [Module R P]
    (w : A ⊗[R] P) : ∃ p : P, w = (1 : A) ⊗ₜ[R] p := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
  | tmul a p =>
    obtain ⟨r, rfl⟩ := hA a
    exact ⟨r • p, by rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]⟩
  | add w w' hw hw' =>
    obtain ⟨p, rfl⟩ := hw
    obtain ⟨p', rfl⟩ := hw'
    exact ⟨p + p', (TensorProduct.tmul_add _ _ _).symm⟩

theorem one_tmul_eq_one_tmul_iff (hA : Function.Surjective (algebraMap R A)) {M : Type*} [AddCommGroup M]
    [Module R M] (m n : M) :
    (1 : A) ⊗ₜ[R] m = (1 : A) ⊗ₜ[R] n ↔ m - n ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R M) := by
  have hA' : Function.Surjective (Algebra.ofId R A) := fun a => hA a
  have hk : RingHom.ker (Algebra.ofId R A) = RingHom.ker (algebraMap R A) := Ideal.ext fun _ => Iff.rfl
  let e : (R ⧸ RingHom.ker (Algebra.ofId R A)) ≃ₐ[R] A := Ideal.quotientKerAlgEquivOfSurjective hA'
  let Ψ : A ⊗[R] M ≃ₗ[R] M ⧸ (RingHom.ker (Algebra.ofId R A) • (⊤ : Submodule R M)) :=
    TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl R M) ≪≫ₗ
      TensorProduct.quotTensorEquivQuotSMul M (RingHom.ker (Algebra.ofId R A))
  have hΨ : ∀ x : M, Ψ ((1 : A) ⊗ₜ[R] x) = Submodule.Quotient.mk x := fun x => by
    simp only [Ψ, LinearEquiv.trans_apply, TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply, map_one,
      LinearEquiv.refl_apply]
    exact TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ x
  rw [← hk, ← Ψ.injective.eq_iff, hΨ, hΨ, Submodule.Quotient.eq]

theorem smul_top_quotient {M : Type*} [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M) :
    (I • (⊤ : Submodule R (M ⧸ N))) = (I • (⊤ : Submodule R M)).map N.mkQ := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

theorem one_tmul_mem_range_baseChange_iff (hA : Function.Surjective (algebraMap R A))
    {P M : Type*} [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M] (d : P →ₗ[R] M) (p : M) :
    (1 : A) ⊗ₜ[R] p ∈ LinearMap.range (d.baseChange A) ↔
      (Submodule.Quotient.mk p : M ⧸ LinearMap.range d) ∈
        RingHom.ker (algebraMap R A) • (⊤ : Submodule R (M ⧸ LinearMap.range d)) := by
  rw [smul_top_quotient, Submodule.mem_map]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨s, rfl⟩ := exists_eq_one_tmul hA v
    rw [LinearMap.baseChange_tmul] at hv
    refine ⟨p - d s, (one_tmul_eq_one_tmul_iff hA p (d s)).1 hv.symm, ?_⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self d s),
      sub_zero]
  · rintro ⟨p', hp', hpp'⟩
    rw [Submodule.mkQ_apply, Submodule.Quotient.eq] at hpp'

    obtain ⟨s, hs⟩ := LinearMap.mem_range.1 hpp'
    have h1 : (1 : A) ⊗ₜ[R] p' = (1 : A) ⊗ₜ[R] (0 : M) :=
      (one_tmul_eq_one_tmul_iff hA p' 0).2 (by rw [sub_zero]; exact hp')
    have hp : p = p' - d s := by rw [hs]; abel
    refine ⟨(1 : A) ⊗ₜ[R] (-s), ?_⟩
    rw [LinearMap.baseChange_tmul, map_neg, hp, TensorProduct.tmul_sub, h1, TensorProduct.tmul_zero, zero_sub,
      TensorProduct.tmul_neg]

end Algebra

section Main

theorem main {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A)) :
    Function.Surjective (𝒱.H1baseChangeMap c A) ∧
    ∀ x y : (𝒱.structureSheafSections c).H1,
      𝒱.H1baseChangeMap c A x = 𝒱.H1baseChangeMap c A y ↔
        x - y ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R (𝒱.structureSheafSections c).H1) := by
  obtain ⟨e0, e1, e01, eH0, eH1, h0, h1, h01, hH0, hH1⟩ :=
    Scheme.TwoAffineOpenCover.exists_baseChangeIsos_structureSheaf 𝒱 c A
  have hβ : ∀ m : (𝒱.cover c).A01, 𝒱.H1baseChangeMap c A (Submodule.Quotient.mk m) =
      eH1 (Submodule.Quotient.mk ((1 : A) ⊗ₜ[R] m)) := by
    intro m
    rw [hH1, h01, H1baseChangeMap_mk, baseChange_map01_apply]
  refine ⟨?_, ?_⟩
  · intro z
    obtain ⟨q, rfl⟩ := eH1.surjective z
    induction q using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨m, rfl⟩ := exists_eq_one_tmul hA w
      exact ⟨Submodule.Quotient.mk m, hβ m⟩
  · intro x y
    induction x using Submodule.Quotient.induction_on with
    | H m =>
      induction y using Submodule.Quotient.induction_on with
      | H n =>
        rw [hβ, hβ, eH1.injective.eq_iff, Submodule.Quotient.eq, ← TensorProduct.tmul_sub,
          ← Submodule.Quotient.mk_sub]
        exact one_tmul_mem_range_baseChange_iff hA _ (m - n)

end Main

end PicTanH1BC

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (A : Type u) [CommRing A] [Algebra R A] (hA : Function.Surjective (algebraMap R A)) :
    Function.Surjective (𝒱.H1baseChangeMap c A) ∧
    ∀ x y : (𝒱.structureSheafSections c).H1,
      𝒱.H1baseChangeMap c A x = 𝒱.H1baseChangeMap c A y ↔
        x - y ∈ RingHom.ker (algebraMap R A) • (⊤ : Submodule R (𝒱.structureSheafSections c).H1) :=
  PicTanH1BC.main 𝒱 c A hA

end S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_H1baseChangeMap_surjective_and_eq_iff_of_surjective (solution)
