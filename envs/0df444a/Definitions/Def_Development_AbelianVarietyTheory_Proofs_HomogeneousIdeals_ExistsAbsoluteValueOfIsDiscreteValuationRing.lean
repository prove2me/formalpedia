-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- name    : Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAbsoluteValueOfIsDiscreteValuationRing
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:37.468224+00:00
-- url     : https://prove2.me/theorems/464523bd-c590-4455-b6bd-c8f9aefe640c
-- title:
--   Exists Absolute Value Of Is Discrete Valuation Ring
-- statement:
--   Definitions and structural lemmas for Exists Absolute Value Of Is Discrete Valuation Ring, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAbsoluteValueOfIsDiscreteValuationRing.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_PowLeComapMapPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
namespace GlobalTheory
universe u
noncomputable abbrev normIntegers (C : Type*) [NormedField C] [IsUltrametricDist C] :
    ValuationSubring C :=
  (NormedField.valuation (K := C)).valuationSubring
theorem normIntegers_integers (C : Type*) [NormedField C] [IsUltrametricDist C] :
    (NormedField.valuation (K := C)).Integers (normIntegers C) :=
  Valuation.valuationSubring.integers _
section Extend
variable {A B : Type*} [CommRing A] [CommRing B]
end Extend
namespace NormIntegers
section Basic
variable {C : Type*} [NormedField C] [IsUltrametricDist C] {O : Type*} [CommRing O] [Algebra O C]
  (hO : (NormedField.valuation (K := C)).Integers O)
include hO
theorem norm_le_one (x : O) : ‖algebraMap O C x‖ ≤ 1 := by
  simpa [← NNReal.coe_le_coe] using hO.map_le_one x
theorem exists_of_norm_le_one {x : C} (hx : ‖x‖ ≤ 1) : ∃ y : O, algebraMap O C y = x :=
  hO.exists_of_le_one (by simpa [← NNReal.coe_le_coe] using hx)
theorem dvd_iff_norm_le {x y : O} : x ∣ y ↔ ‖algebraMap O C y‖ ≤ ‖algebraMap O C x‖ := by
  rw [hO.dvd_iff_le]; simp [← NNReal.coe_le_coe]
theorem isUnit_iff_norm_eq_one {x : O} : IsUnit x ↔ ‖algebraMap O C x‖ = 1 := by
  rw [hO.isUnit_iff_valuation_eq_one]; simp [← NNReal.coe_inj]
theorem norm_pos_iff {x : O} : 0 < ‖algebraMap O C x‖ ↔ x ≠ 0 := by
  simp [map_eq_zero_iff _ hO.hom_inj]
theorem mem_span_singleton_pow_iff {w x : O} {n : ℕ} :
    x ∈ Ideal.span {w} ^ n ↔ ‖algebraMap O C x‖ ≤ ‖algebraMap O C w‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, dvd_iff_norm_le hO, map_pow, norm_pow]
theorem mem_maximalIdeal_iff [IsLocalRing O] {x : O} :
    x ∈ IsLocalRing.maximalIdeal O ↔ ‖algebraMap O C x‖ < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_norm_eq_one hO]
  exact (norm_le_one hO x).lt_iff_ne.symm
theorem isDomain : IsDomain O := hO.hom_inj.isDomain
theorem isLocalRing : IsLocalRing O :=
  haveI := isDomain hO
  haveI := ValuationRing.of_integers _ hO
  inferInstance
theorem isHausdorff_span_singleton {w : O} (hw : ‖algebraMap O C w‖ < 1) :
    IsHausdorff (Ideal.span {w}) O where
  haus' x hx := by
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, mem_span_singleton_pow_iff hO] at hx
    have := ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hw) hx
    by_contra h
    exact absurd this (not_le.2 ((norm_pos_iff hO).2 h))
theorem isAdicComplete_span_singleton [CompleteSpace C] {w : O} (hw : ‖algebraMap O C w‖ < 1) :
    IsAdicComplete (Ideal.span {w}) O where
  toIsHausdorff := isHausdorff_span_singleton hO hw
  prec' f hf := by
    simp only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_span_singleton_pow_iff hO,
      map_sub] at hf ⊢
    have hc : CauchySeq fun n => algebraMap O C (f n) := by
      refine cauchySeq_of_le_geometric ‖algebraMap O C w‖ 1 hw fun n => ?_
      rw [dist_eq_norm, one_mul]
      exact hf (Nat.le_succ n)
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun n => norm_le_one hO _
    obtain ⟨l, rfl⟩ := exists_of_norm_le_one hO hL1
    refine ⟨l, fun n => ?_⟩
    refine le_of_tendsto ((tendsto_const_nhds.sub hL).norm) ?_
    filter_upwards [Filter.eventually_ge_atTop n] with m hm using hf hm
theorem henselianLocalRing [CompleteSpace C] : HenselianLocalRing O :=
  { toIsLocalRing := isLocalRing hO
    is_henselian := fun f hf a₀ h₁ h₂ => by
      haveI := isLocalRing hO
      haveI := isAdicComplete_span_singleton hO ((mem_maximalIdeal_iff hO).1 h₁)
      obtain ⟨a, ha, ha'⟩ := HenselianRing.is_henselian (I := Ideal.span {f.eval a₀}) f hf a₀
        (Ideal.mem_span_singleton_self _) (h₂.map _)
      exact ⟨a, ha, (Ideal.span_singleton_le_iff_mem _).2 h₁ ha'⟩ }
theorem isAlgClosed_residueField [IsAlgClosed C] [IsLocalRing O] :
    IsAlgClosed (IsLocalRing.ResidueField O) := by
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  obtain ⟨q, hq, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (f := IsLocalRing.residue O)
    (Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective p) hp
  have hd : (q.map (algebraMap O C)).degree ≠ 0 := by
    rw [hmon.degree_map, hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd
  have hint : IsIntegral O x := ⟨q, hmon, by rwa [IsRoot, eval_map] at hx⟩
  obtain ⟨y, rfl⟩ := hO.exists_of_le_one (hO.mem_of_integral hint)
  have hy : q.eval y = 0 := by
    apply hO.hom_inj
    rw [IsRoot, eval_map, eval₂_at_apply] at hx
    rw [hx, map_zero]
  refine ⟨IsLocalRing.residue O y, ?_⟩
  rw [← hq, eval_map, eval₂_at_apply, hy, map_zero]
end Basic
end NormIntegers
@[reducible] noncomputable def completionNontriviallyNormedField (K : Type*)
    [NontriviallyNormedField K] : NontriviallyNormedField (UniformSpace.Completion K) where
  __ : NormedField (UniformSpace.Completion K) := inferInstance
  non_trivial := by
    obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := K)
    exact ⟨x, by simpa using hx⟩
instance {C : Type*} [NormedField C] [IsUltrametricDist C] [CompleteSpace C] :
    HenselianLocalRing (normIntegers C) :=
  { (inferInstance : IsLocalRing (normIntegers C)) with
    is_henselian := (NormIntegers.henselianLocalRing (normIntegers_integers C)).is_henselian }
instance {C : Type*} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] :
    IsAlgClosed (IsLocalRing.ResidueField (normIntegers C)) :=
  NormIntegers.isAlgClosed_residueField (normIntegers_integers C)
end GlobalTheory


