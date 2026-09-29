-- Prove2me | solution 1 for Algebra.exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/400d555e-b48a-573c-a058-1860701f6d81

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed

set_option autoImplicit false

theorem solution
    {k : Type*} [Field k] [IsAlgClosed k]
    {B : Type*} [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    {ι : Type*} [Finite ι] (g : ι → B) (hg : ∀ i, g i ≠ 0) :
    ∃ χ : B →ₐ[k] k, ∀ i, χ (g i) ≠ 0 := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  set G : B := ∏ i, g i with hGdef
  have hG : G ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hg i)

  let S := Localization.Away G
  haveI : Nontrivial S := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have hinj : Function.Injective (algebraMap B S) :=
      IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hG)
    exact zero_ne_one (hinj (by rw [map_zero, map_one]; exact h))
  haveI : Algebra.FiniteType k S := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  haveI := hm
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (S ⧸ m) := Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  haveI : Module.Finite k (S ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (S ⧸ m)
  haveI : Algebra.IsAlgebraic k (S ⧸ m) := Algebra.IsAlgebraic.of_finite k (S ⧸ m)
  let φ : (S ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  let ψ : B →ₐ[k] S ⧸ m := (Ideal.Quotient.mkₐ k m).comp (IsScalarTower.toAlgHom k B S)
  refine ⟨φ.comp ψ, fun i => ?_⟩

  have hGunit : IsUnit (algebraMap B S G) := IsLocalization.Away.algebraMap_isUnit G
  have hGS : (φ.comp ψ) G ≠ 0 := by
    intro h0
    have hu : IsUnit ((φ.comp ψ) G) := by
      have : (φ.comp ψ) G = φ (Ideal.Quotient.mk m (algebraMap B S G)) := rfl
      rw [this]
      exact (hGunit.map (Ideal.Quotient.mk m)).map φ
    exact hu.ne_zero h0
  intro hgi
  apply hGS
  show (φ.comp ψ) (∏ i, g i) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hgi

#print axioms solution

end S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed
end P2MW
export P2MW.S_Algebra_exists_algHom_forall_apply_ne_zero_of_finiteType_of_isAlgClosed (solution)
