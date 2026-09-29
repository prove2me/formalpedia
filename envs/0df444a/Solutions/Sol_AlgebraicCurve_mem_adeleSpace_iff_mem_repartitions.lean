-- Prove2me | solution 1 for AlgebraicCurve.mem_adeleSpace_iff_mem_repartitions
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/2f08bb52-01bf-5282-927a-e97ae06f83d0

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor repartitions mem_repartitions_of_forall_le_exp repartitionsOf principalRepartitions mem_principalRepartitions_iff adeleBdd diagonalHom adeleSpace adeleBdd_le_adeleSpace globalSub mem_adeleSpace_iff"
p2m_open "AlgebraicCurve"

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_repartitionsOf_iff_coe_mem_adeleBdd {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl

theorem mem_repartitions_of_mem_adeleBdd {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd D) :
    α ∈ repartitions K F :=
  mem_repartitions_of_forall_le_exp D α hα

theorem mem_repartitions_of_mem_adeleSpace {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    α ∈ repartitions K F := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact mem_repartitions_of_mem_adeleBdd hD

theorem diagonalHom_eq_coe_algebraMap (f : F) :
    diagonalHom K F f = ((algebraMap F ↥(repartitions K F) f : ↥(repartitions K F)) : Place K F → F) := rfl

theorem mem_principalRepartitions_iff_coe_mem_globalSub {α : ↥(repartitions K F)} :
    α ∈ principalRepartitions K F ↔ (α : Place K F → F) ∈ globalSub K F := by
  rw [mem_principalRepartitions_iff]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩

noncomputable def boundedFamilies [HasPrincipalDivisors K F] : Subalgebra F (Place K F → F) where
  carrier := {α | ∃ D : Divisor K F, ∀ v : Place K F, v.adicValuation (α v) ≤ exp (D v)}
  mul_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D + E, fun v => ?_⟩
    rw [Pi.mul_apply, map_mul, Finsupp.add_apply, exp_add]
    exact mul_le_mul' (hD v) (hE v)
  add_mem' := by
    rintro α β ⟨D, hD⟩ ⟨E, hE⟩
    refine ⟨D ⊔ E, fun v => ?_⟩
    rw [Pi.add_apply]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · exact (hD v).trans (exp_le_exp.mpr (le_sup_left (a := D) (b := E) v))
    · exact (hE v).trans (exp_le_exp.mpr (le_sup_right (a := D) (b := E) v))
  algebraMap_mem' := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf
    · exact ⟨0, fun v => by simp⟩
    · obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf
      refine ⟨-P, fun v => ?_⟩
      rw [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        v.adicValuation_eq_exp_neg_ord hf, Finsupp.neg_apply, hP]

end AlgebraicCurve

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions.AlgebraicCurve WithZero in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] {α : Place K F → F} :
    α ∈ adeleSpace K F ↔ α ∈ repartitions K F := by
  constructor
  · exact mem_repartitions_of_mem_adeleSpace
  · intro hα
    have h : repartitions K F ≤ boundedFamilies (K := K) (F := F) := by
      refine Algebra.adjoin_le ?_
      intro β hβ
      classical
      let S : Finset (Place K F) := hβ.toFinset
      refine ⟨∑ v ∈ S, Finsupp.single v (-(v.ord (β v))), fun v => ?_⟩
      by_cases hv : v ∈ S
      · have hβv : β v ≠ 0 := by
          intro h0
          have : ¬v.adicValuation (β v) ≤ 1 := by simpa [S] using hv
          apply this; simp [h0]
        rw [v.adicValuation_eq_exp_neg_ord hβv, exp_le_exp, Finsupp.finset_sum_apply,
          Finset.sum_eq_single v (fun w _ hw => Finsupp.single_eq_of_ne (Ne.symm hw)) (fun h => (h hv).elim),
          Finsupp.single_eq_same]
      · have : v.adicValuation (β v) ≤ 1 := by
          by_contra h; exact hv (by simpa [S] using h)
        refine this.trans ?_
        rw [Finsupp.finset_sum_apply, Finset.sum_eq_zero (fun w hw => ?_), exp_zero]
        exact Finsupp.single_eq_of_ne (fun h => hv (h ▸ hw))
    obtain ⟨D, hD⟩ := h hα
    exact adeleBdd_le_adeleSpace (D := D) hD

end S_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions
end P2MW
export P2MW.S_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions (solution)
