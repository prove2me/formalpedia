-- Prove2me | solution 1 for Algebra.exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/37a02fbc-f87d-538d-b295-8428e98e5691

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed

set_option autoImplicit false

universe u

open scoped nonZeroDivisors

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type u) [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B] [Module.Free A B]
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [Algebra.IsSeparable K L]
    (P : Ideal B) [P.IsPrime]
    (h : ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ P) :
    ∃ Q : Ideal B, Q.IsPrime ∧ Q ≤ P ∧ Q.height = 1 ∧
      ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L)) ≤ Q := by
  classical

  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  haveI : IsIntegralClosure B A L :=
    ⟨IsFractionRing.injective B L, fun {x} =>
      ⟨fun hx => IsIntegrallyClosed.isIntegral_iff.mp hx.tower_top,
       fun ⟨y, hy⟩ => hy ▸ (Algebra.IsIntegral.isIntegral (R := A) y).algebraMap⟩⟩
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization_of_isSeparable A K L B
  have hinjBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L
  set D : Ideal B :=
    ((1 / Submodule.traceDual A K (1 : Submodule B L) : Submodule B L).comap (Algebra.linearMap B L))
    with hDdef

  let ι := Module.Free.ChooseBasisIndex A B
  let bB : Module.Basis ι A B := Module.Free.chooseBasis A B
  let bL : Module.Basis ι K L := bB.localizationLocalization K A⁰ L
  haveI : FiniteDimensional K L := Module.Finite.of_basis bL
  set C : Submodule B L := Submodule.traceDual A K (1 : Submodule B L) with hCdef
  have hspan : (1 : Submodule B L).restrictScalars A = Submodule.span A (Set.range bL) := by
    rw [Module.Basis.localizationLocalization_span]
    ext x
    simp only [Submodule.restrictScalars_mem, Submodule.mem_one, LinearMap.mem_range]
    rfl
  have hC : C.restrictScalars A = Submodule.span A (Set.range bL.traceDual) :=
    Submodule.traceDual_span_of_basis A (1 : Submodule B L) bL hspan
  have hCmem : ∀ c : L, c ∈ C ↔ c ∈ Submodule.span A (Set.range bL.traceDual) := fun c => by
    rw [← hC, Submodule.restrictScalars_mem]
  have hDmem : ∀ x : B, x ∈ D ↔ ∀ c ∈ C, algebraMap B L x * c ∈ (1 : Submodule B L) := fun x => by
    rw [hDdef, Submodule.mem_comap, Algebra.linearMap_apply, Submodule.mem_div_iff_forall_mul_mem]

  obtain ⟨⟨d, hdM⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Algebra.algebraMapSubmonoid B A⁰) (fun i => (bL.traceDual i : L))
  have hd0 : d ≠ 0 := by
    obtain ⟨a, ha, rfl⟩ := hdM
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective A B)).mpr (nonZeroDivisors.ne_zero ha)
  have hdL : algebraMap B L d ≠ 0 := (map_ne_zero_iff _ hinjBL).mpr hd0
  choose y hy using hd

  have hy' : ∀ i, algebraMap B L (y i) = algebraMap B L d * bL.traceDual i := fun i => by
    rw [hy i]
    exact Algebra.smul_def d _

  let M : Submodule B (B ⧸ Ideal.span {d}) :=
    Submodule.span B (Set.range fun i => Ideal.Quotient.mk (Ideal.span {d}) (y i))
  have hsmul_mk : ∀ (x z : B), x • Ideal.Quotient.mk (Ideal.span {d}) z =
      Ideal.Quotient.mk (Ideal.span {d}) (x * z) := fun x z => by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
  have hMann : ∀ x : B, x ∈ Module.annihilator B M ↔ ∀ i, x * y i ∈ Ideal.span {d} := fun x => by
    change x ∈ M.annihilator ↔ _
    rw [Submodule.mem_annihilator_span]
    constructor
    · intro hx i
      have := hx ⟨_, ⟨i, rfl⟩⟩
      rwa [hsmul_mk, Ideal.Quotient.eq_zero_iff_mem] at this
    · rintro hx ⟨_, ⟨i, rfl⟩⟩
      rw [hsmul_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact hx i
  have hDM : D = Module.annihilator B M := by
    ext x
    rw [hDmem, hMann]
    constructor
    · intro hx i
      have hci : (bL.traceDual i : L) ∈ C := (hCmem _).mpr (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨w, hw⟩ := Submodule.mem_one.mp (hx _ hci)
      rw [Ideal.mem_span_singleton']
      refine ⟨w, hinjBL ?_⟩
      rw [map_mul, map_mul, hw, hy']
      ring
    · intro hx c hc
      have hw : ∀ i, ∃ w : B, w * d = x * y i := fun i => Ideal.mem_span_singleton'.mp (hx i)
      choose w hw using hw
      have hxw : ∀ i, algebraMap B L x * bL.traceDual i = algebraMap B L (w i) := fun i => by
        apply mul_left_cancel₀ hdL
        rw [← mul_assoc, mul_comm (algebraMap B L d), mul_assoc, ← hy', ← map_mul, ← hw i,
          map_mul, mul_comm]
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp ((hCmem c).mp hc)
      rw [Finset.mul_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [mul_smul_comm, hxw]
      exact Submodule.smul_of_tower_mem _ (a i) (Submodule.mem_one.mpr ⟨w i, rfl⟩)

  have hAnnP : Module.annihilator B M ≤ P := by rw [← hDM]; exact h
  obtain ⟨Q, hQmin, hQP⟩ := Ideal.exists_minimalPrimes_le hAnnP
  have hQass : Q ∈ associatedPrimes B M :=
    Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes B M hQmin
  have hQass' : Q ∈ associatedPrimes B (B ⧸ Ideal.span {d}) :=
    associatedPrimes.subset_of_injective (f := M.subtype) (Submodule.injective_subtype M) hQass
  haveI hQprime : Q.IsPrime := IsAssociatedPrime.isPrime hQass'
  refine ⟨Q, hQprime, hQP, IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hd0 Q hQass', ?_⟩
  rw [hDM]
  exact hQmin.1.2

end S_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed
end P2MW
export P2MW.S_Algebra_exists_le_height_eq_one_of_comap_one_div_traceDual_le_of_free_of_isIntegrallyClosed (solution)
