-- Prove2me | solution 1 for AlgebraicCurve.RegularProlongation.exists_forall_residue_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/ad0e8ccd-78c6-537c-be2e-59ac3b87e648

import Mathlib
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ValuationSubring_exists_forall_mem_and_sub_mem_nonunits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq

set_option autoImplicit false
set_option maxHeartbeats 4800000

open AlgebraicCurve IsLocalRing

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Finite ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (hR : Function.Injective fun i => (R i).integers)
    (a : ∀ i, Fb i) :
    ∃ z : F, ∀ i, ∃ h : z ∈ (R i).integers, (R i).residue ⟨z, h⟩ = a i := by
  classical

  choose b hb using fun i => (R i).residue_surjective (a i)

  have hincomp : ∀ i j, (R i).integers ≤ (R j).integers → i = j := by
    intro i j hij
    apply hR
    refine le_antisymm hij (fun f hfj => ?_)
    rcases eq_or_ne f 0 with rfl | hf0
    · exact zero_mem _

    obtain ⟨c, hcf, hcfu⟩ := (R i).exists_smul_mem f hf0
    have hc0 : c ≠ 0 := (R i).smul_const_ne_zero hcf hcfu
    have hac0 : (algebraMap L F c) ≠ 0 := fun h => hc0 ((algebraMap L F).injective (by simp [h]))
    have hcfUi : IsUnit (⟨c • f, hcf⟩ : (R i).integers) :=
      (R i).isUnit_of_residue_ne_zero hcfu

    have hvcf : (R i).integers.valuation (c • f) = 1 :=
      ((R i).integers.valuation_eq_one_iff ⟨c • f, hcf⟩).mp hcfUi
    have hcfi : (c • f)⁻¹ ∈ (R i).integers := by
      have : (R i).integers.valuation (c • f)⁻¹ ≤ 1 := by
        rw [map_inv₀, hvcf, inv_one]
      exact ((R i).integers.valuation_le_one_iff _).mp this

    have hmul : (algebraMap L F c⁻¹ : F) = (c • f)⁻¹ * f := by
      rw [Algebra.smul_def, map_inv₀, mul_inv_rev, mul_assoc,
        mul_comm ((algebraMap L F c)⁻¹) f, ← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
    have hcinv_in_j : algebraMap L F c⁻¹ ∈ (R j).integers := by
      rw [hmul]; exact mul_mem (hij hcfi) hfj
    have hcinvA : c⁻¹ ∈ A := ((R j).algebraMap_mem_iff c⁻¹).mp hcinv_in_j

    have hcinv_i : algebraMap L F c⁻¹ ∈ (R i).integers :=
      ((R i).algebraMap_mem_iff c⁻¹).mpr hcinvA
    have hfeq : f = algebraMap L F c⁻¹ * (c • f) := by
      rw [Algebra.smul_def, map_inv₀, ← mul_assoc, inv_mul_cancel₀ hac0, one_mul]
    rw [hfeq]
    exact mul_mem hcinv_i hcf

  obtain ⟨z, hz⟩ := ValuationSubring.exists_forall_mem_and_sub_mem_nonunits
    (fun i => (R i).integers) hincomp (fun i => ↑(b i)) (fun i => (b i).2)
  refine ⟨z, fun i => ⟨(hz i).1, ?_⟩⟩

  set zO : (R i).integers := ⟨z, (hz i).1⟩ with hzO
  have hcoe : (↑(zO - b i) : F) = z - ↑(b i) := rfl
  have hval : (R i).integers.valuation (↑(zO - b i) : F) < 1 := by
    rw [hcoe]
    have := (hz i).2
    rwa [ValuationSubring.mem_nonunits_iff] at this
  have hnu : ¬ IsUnit (zO - b i) := fun hu =>
    ne_of_lt hval (((R i).integers.valuation_eq_one_iff (zO - b i)).mp hu)
  have h0 : (R i).residue (zO - b i) = 0 := by
    have hker : zO - b i ∈ RingHom.ker (R i).residue := by
      rw [(R i).ker_residue, mem_maximalIdeal]; exact hnu
    exact hker
  rw [map_sub, hb i, sub_eq_zero] at h0
  exact h0

end S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq
end P2MW
export P2MW.S_AlgebraicCurve_RegularProlongation_exists_forall_residue_eq (solution)
