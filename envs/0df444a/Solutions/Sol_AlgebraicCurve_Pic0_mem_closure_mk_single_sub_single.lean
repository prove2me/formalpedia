-- Prove2me | solution 1 for AlgebraicCurve.Pic0.mem_closure_mk_single_sub_single
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:01.734404+00:00
-- url     : https://prove2.me/submissions/376dc100-b1ef-5078-9fc4-a52f1e959f58

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
set_option autoImplicit false
open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] (h1 : ∀ v : Place K F, v.deg = 1)
    (V₀ : Place K F) (x : Pic0 K F) :
    x ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} := by
  classical
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  have hgen : ∀ v : Place K F,
      Finsupp.single v (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F) := fun v => by
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, h1, h1]; simp
  set g : Place K F → ↥(Divisor.degZero (K := K) (F := F)) := fun v => ⟨_, hgen v⟩ with hg

  have hdeg : ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v = 0 := by
    have h0 : Divisor.degree (D : Divisor K F) = 0 := Divisor.mem_degZero.mp D.2
    have : Divisor.degree (D : Divisor K F) = ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v * ((v.deg : ℕ) : ℤ) := by
      show Finsupp.liftAddHom _ (D : Divisor K F) = _
      rw [Finsupp.liftAddHom_apply, Finsupp.sum]
      rfl
    rw [this] at h0
    simpa [h1] using h0
  have hD : D = ∑ v ∈ (D : Divisor K F).support, ((D : Divisor K F) v) • g v := by
    apply Subtype.ext
    rw [AddSubgroup.val_finsetSum]
    simp only [AddSubgroupClass.coe_zsmul, hg, smul_sub, Finset.sum_sub_distrib]
    rw [← Finset.sum_smul, hdeg, zero_smul, sub_zero]
    simp only [Finsupp.smul_single_one]
    exact ((D : Divisor K F).sum_single).symm
  have hφ : ∀ E, Pic0.mk (K := K) (F := F) E =
      QuotientAddGroup.mk' ((Divisor.principal (K := K) (F := F)).addSubgroupOf (Divisor.degZero (K := K) (F := F))) E :=
    fun E => rfl
  have hmem : ∀ v : Place K F, Pic0.mk (g v) ∈ AddSubgroup.closure
      {y : Pic0 K F | ∃ (V : Place K F)
        (h : Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1 ∈ Divisor.degZero (K := K) (F := F)),
        y = Pic0.mk ⟨Finsupp.single V (1 : ℤ) - Finsupp.single V₀ 1, h⟩} :=
    fun v => AddSubgroup.subset_closure ⟨v, hgen v, rfl⟩
  rw [hD, hφ, map_sum]
  refine AddSubgroup.sum_mem _ fun v _ => ?_
  rw [map_zsmul]
  exact AddSubgroup.zsmul_mem _ (hmem v) _

end S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single
end P2MW
export P2MW.S_AlgebraicCurve_Pic0_mem_closure_mk_single_sub_single (solution)
