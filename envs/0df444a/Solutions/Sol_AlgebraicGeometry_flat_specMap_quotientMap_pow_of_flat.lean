-- Prove2me | solution 1 for AlgebraicGeometry.flat_specMap_quotientMap_pow_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/370eb8d9-e627-59fc-ba9d-9cea705151fa

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TensorProduct

namespace FlatTrunc13

variable (𝒪 : Type) [CommRing 𝒪] (S : Type) [CommRing S] [Algebra 𝒪 S]

theorem flat_quotientMap [Module.Flat 𝒪 S] (I : Ideal 𝒪) (J : Ideal S) (hIJ : I ≤ J.comap (algebraMap 𝒪 S))
    (hJI : J ≤ I.map (algebraMap 𝒪 S)) :
    (Ideal.quotientMap J (algebraMap 𝒪 S) hIJ).Flat := by
  set A := 𝒪 ⧸ I with hA
  set φ := Ideal.quotientMap J (algebraMap 𝒪 S) hIJ with hφ
  letI : Algebra A (S ⧸ J) := φ.toAlgebra
  have hφa : ∀ a : A, algebraMap A (S ⧸ J) a = φ a := fun a => rfl
  haveI : IsScalarTower 𝒪 A (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun o => rfl)

  let L : A ⊗[𝒪] S →ₐ[A] S ⧸ J :=
    Algebra.TensorProduct.lift (Algebra.ofId A (S ⧸ J)) (Ideal.Quotient.mkₐ 𝒪 J) (fun _ _ => Commute.all _ _)
  have hL : ∀ (a : A) (s : S), L (a ⊗ₜ s) = φ a * Ideal.Quotient.mk J s := fun a s => by
    simp only [L, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk, hφa]
  have hker : ∀ s ∈ J, (Algebra.TensorProduct.includeRight : S →ₐ[𝒪] A ⊗[𝒪] S) s = 0 := by
    intro s hs
    have hs' : s ∈ Ideal.span ((algebraMap 𝒪 S) '' (I : Set 𝒪)) := hJI hs
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs'
    · rintro _ ⟨o, ho, rfl⟩
      rw [Algebra.TensorProduct.includeRight_apply, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul,
        Algebra.smul_def, mul_one, show algebraMap 𝒪 A o = 0 from (Ideal.Quotient.eq_zero_iff_mem.2 ho), TensorProduct.zero_tmul]
    · exact map_zero _
    · intro x y _ _ hx hy; rw [map_add, hx, hy, add_zero]
    · intro r x _ hx; rw [smul_eq_mul, map_mul, hx, mul_zero]
  let K : S ⧸ J →+* A ⊗[𝒪] S :=
    Ideal.Quotient.lift J (Algebra.TensorProduct.includeRight : S →ₐ[𝒪] A ⊗[𝒪] S).toRingHom hker
  have hK : ∀ s : S, K (Ideal.Quotient.mk J s) = (1 : A) ⊗ₜ s := fun s => rfl
  have hKφ : ∀ a : A, K (φ a) = a ⊗ₜ (1 : S) := by
    intro a
    obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective a
    show K (Ideal.Quotient.mk J (algebraMap 𝒪 S o)) = _
    rw [hK, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  have hKL : ∀ t : A ⊗[𝒪] S, K (L t) = t := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul a s => rw [hL, map_mul, hKφ, hK, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hLK : ∀ x : S ⧸ J, L (K x) = x := by
    intro x
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hK, hL, map_one, one_mul]

  let e : (S ⧸ J) ≃ₗ[A] A ⊗[𝒪] S :=
    { toFun := K
      invFun := L
      map_add' := fun x y => map_add K x y
      map_smul' := fun a x => by
        obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
        show K (a • Ideal.Quotient.mk J s) = a • K (Ideal.Quotient.mk J s)
        rw [Algebra.smul_def, hφa, map_mul, hKφ, hK, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul,
          one_mul, smul_eq_mul, mul_one]
      left_inv := hLK
      right_inv := hKL }
  show @Module.Flat A (S ⧸ J) _ _ φ.toAlgebra.toModule
  exact Module.Flat.of_linearEquiv e

end FlatTrunc13

open FlatTrunc13 in
theorem solution
    (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (S : Type) [CommRing S] [Algebra 𝒪 S] [Module.Flat 𝒪 S] (n : ℕ) :
    Flat (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (Ideal.span {(algebraMap 𝒪 S π) ^ (n + 1)}) (algebraMap 𝒪 S)
      (by rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow]; exact Ideal.subset_span rfl)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom]
  exact flat_quotientMap 𝒪 S _ _ _ (by rw [Ideal.map_span, Set.image_singleton, map_pow])

end S_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat
end P2MW
export P2MW.S_AlgebraicGeometry_flat_specMap_quotientMap_pow_of_flat (solution)
