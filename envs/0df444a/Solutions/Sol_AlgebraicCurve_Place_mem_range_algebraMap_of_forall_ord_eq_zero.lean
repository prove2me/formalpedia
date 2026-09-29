-- Prove2me | solution 1 for AlgebraicCurve.Place.mem_range_algebraMap_of_forall_ord_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/bec9b8a3-66ad-55b6-b2c0-4260de7e5597

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_neg_of_transcendental
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint"

set_option autoImplicit false

open AlgebraicCurve
open scoped IntermediateField.algebraAdjoinAdjoin

set_option maxHeartbeats 3200000 in

theorem solution {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] [IsAlgClosed K] (j : F) (hj : Transcendental K j) [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F] {x : F} (hx : ∀ v : Place K F, v.ord x = 0) : x ∈ (algebraMap K F).range := by
  classical
  by_contra hxK

  have hxt : Transcendental K x := fun halg =>
    hxK (minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)))

  haveI hS : Algebra.IsAlgebraic (IntermediateField.adjoin K ({j} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI hKjF : Algebra.IsAlgebraic (Algebra.adjoin K ({j} : Set F)) F :=
    Algebra.IsAlgebraic.trans _ (IntermediateField.adjoin K ({j} : Set F)) _
  have htrdeg : Algebra.trdeg K F ≤ 1 := by
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk (R := K) (s := ({j} : Set F)) (A := F)
    simpa using h

  have hjind : AlgebraicIndependent K ![j] := algebraicIndependent_iff_transcendental.mpr hj
  have htrdeg_eq : Algebra.trdeg K F = 1 := by
    refine le_antisymm htrdeg ?_
    have h := hjind.lift_cardinalMk_le_trdeg
    simpa using h

  have hxind : AlgebraicIndependent K ![x] := algebraicIndependent_iff_transcendental.mpr hxt
  have hxbasis : IsTranscendenceBasis K ![x] :=
    hxind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by
      simp only [Cardinal.mk_fintype, Fintype.card_fin, Nat.cast_one, Cardinal.lift_one]
      exact (Cardinal.lift_le_one_iff).mpr htrdeg_eq.le)
  have hrange : Set.range ![x] = ({x} : Set F) := by
    simp [Set.range_unique]
  haveI hxalg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    hrange ▸ hxbasis.isAlgebraic_field

  obtain ⟨t, ht⟩ := Module.finite_def.mp
    (inferInstance : Module.Finite (IntermediateField.adjoin K ({j} : Set F)) F)
  set Lx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hLx_def
  set M : IntermediateField Lx F := IntermediateField.adjoin Lx ({j} ∪ (t : Set F))
    with hM_def
  have hjM : j ∈ M := by
    rw [hM_def]
    exact IntermediateField.subset_adjoin _ _ (Set.mem_union_left _ rfl)
  have hKjle : ∀ z : F, z ∈ IntermediateField.adjoin K ({j} : Set F) → z ∈ M := by
    have hle : IntermediateField.adjoin K ({j} : Set F) ≤
        IntermediateField.restrictScalars K M :=
      IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hjM)
    exact fun z hz => hle hz
  have hadjtop : M = ⊤ := by
    rw [eq_top_iff]
    rintro f -
    have hf : f ∈ Submodule.span (IntermediateField.adjoin K ({j} : Set F)) (t : Set F) := by
      rw [ht]; trivial
    induction hf using Submodule.span_induction with
    | mem g hg =>
      rw [hM_def]
      exact IntermediateField.subset_adjoin _ _ (Set.mem_union_right _ hg)
    | zero => exact zero_mem _
    | add g h _ _ hg hh => exact add_mem hg hh
    | smul e g _ hg =>
      rw [Algebra.smul_def]
      exact mul_mem (hKjle _ e.2) hg
  haveI hfinadj : FiniteDimensional Lx M :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  haveI hfintop : FiniteDimensional Lx (⊤ : IntermediateField Lx F) := hadjtop ▸ hfinadj
  haveI : FiniteDimensional Lx F :=
    IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

  obtain ⟨v, hv⟩ := AlgebraicCurve.Place.exists_ord_neg_of_transcendental x hxt
  rw [hx v] at hv
  exact lt_irrefl 0 hv

end S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_Place_mem_range_algebraMap_of_forall_ord_eq_zero (solution)
