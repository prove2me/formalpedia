-- Prove2me | solution 1 for AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/12066fcc-ead5-548a-a44d-f8d000cd6869

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
import Theorems.Thm_AlgebraicCurve_Place_exists_forall_ord_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem

set_option autoImplicit false

open AlgebraicCurve

set_option maxHeartbeats 3200000 in
theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (S : Finset (Place K F)) (V₀ : Place K F) (hV₀ : V₀ ∉ S) (x : Pic0 K F) :
    x ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F) (_ : V ∉ S)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by
  classical
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  haveI : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  set G : Set (Pic0 K F) := {y : Pic0 K F | ∃ (V : Place K F) (_ : V ∉ S)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} with hG

  have hgen_mem : ∀ V : Place K F, Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F) := by
    intro V
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
    simp
  have hgen : ∀ V : Place K F, V ∉ S →
      Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hgen_mem V⟩ ∈ AddSubgroup.closure G :=
    fun V hV => AddSubgroup.subset_closure ⟨V, hV, hgen_mem V, rfl⟩

  have key : ∀ (D : Divisor K F) (hD : D ∈ Divisor.degZero (K := K) (F := F)),
      (∀ v ∈ S, D v = 0) → Pic0.mk ⟨D, hD⟩ ∈ AddSubgroup.closure G := by
    intro D hD hS

    have hsum : (∑ v ∈ D.support, D v) = 0 := by
      have h := hD
      rw [Divisor.mem_degZero] at h
      have : Divisor.degree D = ∑ v ∈ D.support, D v := by
        conv_lhs => rw [← Finsupp.sum_single D]
        rw [Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Divisor.degree_single, hdeg1]; simp
      rw [← this, h]
    have h1 : ∑ v ∈ D.support, D v • Finsupp.single v (1 : ℤ) = D := by
      conv_rhs => rw [← Finsupp.sum_single D]
      rw [Finsupp.sum]
      exact Finset.sum_congr rfl fun v _ => Finsupp.smul_single_one v (D v)
    have hDiv : ∑ v ∈ D.support, D v • (Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1) = D := by
      have h2 : ∑ v ∈ D.support, D v • (Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1) =
          ∑ v ∈ D.support, D v • Finsupp.single v (1 : ℤ) - (∑ v ∈ D.support, D v) • Finsupp.single V₀ 1 := by
        rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun v _ => smul_sub _ _ _
      rw [h2, hsum, zero_smul, sub_zero, h1]
    have hDeq : (⟨D, hD⟩ : Divisor.degZero (K := K) (F := F)) =
        ∑ v ∈ D.support, D v • (⟨Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1, hgen_mem v⟩ : Divisor.degZero (K := K) (F := F)) := by
      apply Subtype.ext
      rw [AddSubgroup.val_finset_sum]
      simp only [AddSubgroupClass.coe_zsmul]
      exact hDiv.symm
    rw [hDeq]
    show QuotientAddGroup.mk _ ∈ _
    rw [QuotientAddGroup.mk_sum]
    refine AddSubgroup.sum_mem _ fun v hv => ?_
    rw [QuotientAddGroup.mk_zsmul]
    have hvS : v ∉ S := fun hvS => (Finsupp.mem_support_iff.mp hv) (hS v hvS)
    exact AddSubgroup.zsmul_mem _ (hgen v hvS) _

  have hall := AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single hdeg1 V₀ x
  refine (AddSubgroup.closure_le (AddSubgroup.closure G)).mpr ?_ hall
  rintro _ ⟨V, hVdeg, rfl⟩
  by_cases hVS : V ∉ S
  · exact hgen V hVS
  push_neg at hVS

  obtain ⟨f, hf0, hford⟩ := AlgebraicCurve.Place.exists_forall_ord_eq S (fun w => if w = V then 1 else 0)
  obtain ⟨Pf, hPf, hPfdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hPfmem : Pf ∈ Divisor.degZero (K := K) (F := F) := hPfdeg
  have hPfpr : Pic0.mk (⟨Pf, hPfmem⟩ : Divisor.degZero (K := K) (F := F)) = 0 := by
    show QuotientAddGroup.mk _ = 0
    rw [QuotientAddGroup.eq_zero_iff]
    exact ⟨f, hf0, hPf⟩

  have hD'mem : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 - Pf ∈ Divisor.degZero (K := K) (F := F) :=
    sub_mem (hgen_mem V) hPfmem
  have hD'S : ∀ w ∈ S, (Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 - Pf : Divisor K F) w = 0 := by
    intro w hw
    have hwV₀ : w ≠ V₀ := fun h => hV₀ (h ▸ hw)
    rw [Finsupp.sub_apply, Finsupp.sub_apply, hPf w, hford w hw]
    by_cases hwV : w = V
    · subst hwV
      simp [Finsupp.single_apply, hwV₀, hwV₀.symm]
    · simp [Finsupp.single_apply, hwV, Ne.symm hwV, hwV₀, hwV₀.symm]
  have hsplit : (⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, hVdeg⟩ : Divisor.degZero (K := K) (F := F)) =
      ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 - Pf, hD'mem⟩ + ⟨Pf, hPfmem⟩ := by
    apply Subtype.ext
    simp
  rw [hsplit, Pic0.mk_add, hPfpr, add_zero]
  exact key _ hD'mem hD'S

#print axioms solution

end S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single_of_notMem (solution)
