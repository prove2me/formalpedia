-- Prove2me | solution 1 for Algebra.exists_linearMap_apply_mul_eq_zero_imp_of_isReduced
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/9394877d-e9f4-5594-b645-788e156bd42d

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced

namespace P2MFrobeniusOfReduced

open Module

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

theorem exists_dual_apply_ne_zero {V : Type*} [AddCommGroup V] [Module K V] {v : V} (hv : v ≠ 0) :
    ∃ μ : V →ₗ[K] K, μ v ≠ 0 := by
  by_contra h
  exact hv ((Module.forall_dual_apply_eq_zero_iff K v).mp fun μ => not_not.mp (not_exists.mp h μ))

theorem eq_zero_of_forall_mem_maximal [IsArtinianRing A] [IsReduced A] {x : A}
    (hx : ∀ I : MaximalSpectrum A, x ∈ I.asIdeal) : x = 0 := by
  have hjac : x ∈ Ideal.jacobson (⊥ : Ideal A) := by
    refine Ideal.mem_sInf.mpr ?_
    rintro J ⟨-, hJ⟩
    exact hx ⟨J, hJ⟩
  rw [IsArtinianRing.jacobson_eq_radical] at hjac
  have hnil : IsNilpotent x := (mem_nilradical (R := A)).mp hjac
  exact hnil.eq_zero

variable (K A) in
theorem main [FiniteDimensional K A] [IsReduced A] :
    ∃ l : A →ₗ[K] K, ∀ x : A, (∀ y : A, l (x * y) = 0) → x = 0 := by
  classical
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  haveI : Fintype (MaximalSpectrum A) := Fintype.ofFinite _

  have hμ : ∀ I : MaximalSpectrum A,
      ∃ μ : (A ⧸ I.asIdeal) →ₗ[K] K, μ 1 ≠ 0 := by
    intro I
    haveI : Nontrivial (A ⧸ I.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr I.isMaximal.ne_top
    exact exists_dual_apply_ne_zero one_ne_zero
  choose μ hμ using hμ

  let π : ∀ I : MaximalSpectrum A, A →ₗ[K] A ⧸ I.asIdeal :=
    fun I => (Ideal.Quotient.mkₐ K I.asIdeal).toLinearMap
  have hπ : ∀ (I : MaximalSpectrum A) (x : A), π I x = Ideal.Quotient.mk I.asIdeal x := fun I x => rfl
  refine ⟨∑ I, (μ I).comp (π I), fun x hx => ?_⟩

  refine eq_zero_of_forall_mem_maximal fun I => ?_
  haveI : I.asIdeal.IsMaximal := I.isMaximal
  by_contra hxI

  set u : A ⧸ I.asIdeal := Ideal.Quotient.mk I.asIdeal x with hu
  have hu0 : u ≠ 0 := fun h => hxI (Ideal.Quotient.eq_zero_iff_mem.mp h)
  letI : Field (A ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal

  have hzero : ∀ z : A ⧸ I.asIdeal, μ I z = 0 := by
    intro z

    have hcop : Pairwise (Function.onFun IsCoprime fun J : MaximalSpectrum A => J.asIdeal) :=
      fun J J' hJJ' => MaximalSpectrum.isCoprime_of_ne hJJ'
    obtain ⟨y, hy⟩ := Ideal.pi_quotient_surjective hcop
      (Function.update (0 : ∀ J : MaximalSpectrum A, A ⧸ J.asIdeal) I (u⁻¹ * z))
    have hyI : Ideal.Quotient.mk I.asIdeal y = u⁻¹ * z := by
      rw [hy I, Function.update_self]
    have hyJ : ∀ J : MaximalSpectrum A, J ≠ I → Ideal.Quotient.mk J.asIdeal y = 0 := by
      intro J hJ
      rw [hy J, Function.update_of_ne hJ, Pi.zero_apply]

    have hl := hx y
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, hπ, map_mul] at hl
    rw [Finset.sum_eq_single I] at hl
    · rw [hyI, ← hu, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul] at hl
      exact hl
    · intro J _ hJ
      rw [hyJ J hJ, mul_zero, map_zero]
    · intro h
      exact absurd (Finset.mem_univ I) h
  exact hμ I (hzero 1)

end P2MFrobeniusOfReduced

theorem solution
    (K A : Type*) [Field K] [CommRing A] [Algebra K A] [FiniteDimensional K A] [IsReduced A] :
    ∃ l : A →ₗ[K] K, ∀ x : A, (∀ y : A, l (x * y) = 0) → x = 0 :=
  P2MFrobeniusOfReduced.main K A

end S_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced
end P2MW
export P2MW.S_Algebra_exists_linearMap_apply_mul_eq_zero_imp_of_isReduced (solution)
