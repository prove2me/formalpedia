-- Prove2me | solution 1 for AlgebraicCurve.RROpens.exists_degree_eq_sub_one_and_ell_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/aca5eb4f-1edc-5b51-b559-97d8b38d39f3

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_RROpens_exists_finset_subset_ell_sub_sum_single_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_exists_sub_algebraMap_mem_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

universe u v

noncomputable section

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero.AlgebraicCurve WithZero"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "IsCurveOver IsCurveOver.hasPrincipalDivisors IsCurveOver.deg_eq_one_of_isAlgClosed IsCurveOver.forall_deg_eq_one_of_isAlgClosed Place Place.coe_algebraMap Place.adicValuation_coe_eq_one_iff Divisor Divisor.degree Divisor.degree_single LSpace ell mem_lSpace_iff lSpace_mono algebraMap_mem_lSpace_zero one_mem_lSpace_zero ConstantsAreBase ell_zero_eq_one_of_constantsAreBase RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero Place.exists_sub_algebraMap_mem_maximalIdeal"
namespace GenericVanishSol
p2m_open "AlgebraicCurve"

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

section Val

variable (v : Place K F)

theorem adicValuation_algebraMap_eq_one {c : K} (hc : c ≠ 0) : v.adicValuation (algebraMap K F c) = 1 := by
  rw [← Place.coe_algebraMap]
  exact (v.adicValuation_coe_eq_one_iff _).mpr ((IsUnit.mk0 c hc).map _)

theorem mem_valuationSubring_of_adicValuation_le_one {x : F} (hx : v.adicValuation x ≤ 1) :
    x ∈ v.toValuationSubring := by
  by_contra hxR
  have hx0 : x ≠ 0 := fun h => hxR (h ▸ v.toValuationSubring.zero_mem)
  have hxi : x⁻¹ ∈ v.toValuationSubring := (v.toValuationSubring.mem_or_inv_mem x).resolve_left hxR
  have hnu : ¬ IsUnit (⟨x⁻¹, hxi⟩ : v.toValuationSubring) := by
    rintro ⟨u, hu⟩
    apply hxR
    have h1 : ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) * (⟨x⁻¹, hxi⟩ : v.toValuationSubring) = 1 := by
      rw [← hu, Units.inv_mul]
    have h2 : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) * x⁻¹ = 1 := by
      have := congrArg (fun a : v.toValuationSubring => (a : F)) h1
      simpa using this
    have h3 : (((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring) : F) = x := by
      field_simp at h2
      exact h2
    exact h3 ▸ ((u⁻¹ : v.toValuationSubringˣ) : v.toValuationSubring).2
  have hlt : v.adicValuation x⁻¹ < 1 :=
    lt_of_le_of_ne (v.adicValuation_le_one_of_mem hxi)
      (fun h => hnu ((v.adicValuation_coe_eq_one_iff ⟨x⁻¹, hxi⟩).mp h))
  rw [map_inv₀, inv_lt_one₀ (zero_lt_iff.mpr (v.adicValuation_ne_zero hx0))] at hlt
  exact not_le.mpr hlt hx

theorem ord_pos_of_adicValuation_lt_one {f : F} (hf : f ≠ 0) (h : v.adicValuation f < 1) : 0 < v.ord f := by
  rw [v.adicValuation_eq_exp_neg_ord hf, ← exp_zero, exp_lt_exp] at h
  omega

theorem adicValuation_lt_one_of_ord_pos {f : F} (hf : f ≠ 0) (h : 0 < v.ord f) : v.adicValuation f < 1 := by
  rw [v.adicValuation_eq_exp_neg_ord hf, ← exp_zero, exp_lt_exp]
  omega

end Val

section Deg

theorem degree_eq_sum (D : Divisor K F) : Divisor.degree D = D.sum fun w n => n * (w.deg : ℤ) := by
  simp [Divisor.degree]

theorem degree_pos_of_nonneg {D : Divisor K F} (h : ∀ w, 0 ≤ D w) {v : Place K F} (hv : 0 < D v)
    (hdeg : ∀ w : Place K F, w.deg = 1) : 0 < Divisor.degree D := by
  rw [degree_eq_sum]
  have hmem : v ∈ D.support := Finsupp.mem_support_iff.mpr hv.ne'
  calc (0 : ℤ) < D v * (v.deg : ℤ) := by rw [hdeg v]; simpa using hv
    _ ≤ D.sum fun w n => n * (w.deg : ℤ) := by
        refine Finset.single_le_sum (f := fun w => D w * (w.deg : ℤ)) (fun w _ => ?_) hmem
        show 0 ≤ D w * (w.deg : ℤ)
        rw [hdeg w]; simpa using h w

theorem exists_pos_of_degree_eq_zero {D : Divisor K F} (h0 : Divisor.degree D = 0) {w : Place K F} (hw : D w < 0)
    (hdeg : ∀ w : Place K F, w.deg = 1) : ∃ z, 0 < D z := by
  by_contra hcon
  push_neg at hcon
  have : Divisor.degree D < 0 := by
    have hneg := degree_pos_of_nonneg (D := -D) (fun z => by simpa using hcon z) (v := w) (by simpa using hw) hdeg
    rw [map_neg] at hneg
    omega
  omega

end Deg

section Constants

variable [IsAlgClosed K] [IsCurveOver K F]

theorem mem_lSpace_zero_iff {f : F} : f ∈ LSpace (0 : Divisor K F) ↔ ∀ w : Place K F, w.adicValuation f ≤ 1 := by
  rw [mem_lSpace_iff]
  simp

theorem constantsAreBase [Nonempty (Place K F)] : ConstantsAreBase K F := by
  apply le_antisymm
  · intro f hf
    rw [mem_lSpace_zero_iff] at hf
    obtain ⟨v⟩ := (inferInstance : Nonempty (Place K F))
    let b : v.toValuationSubring := ⟨f, mem_valuationSubring_of_adicValuation_le_one v (hf v)⟩
    obtain ⟨c, hc⟩ := Place.exists_sub_algebraMap_mem_maximalIdeal v (IsCurveOver.deg_eq_one_of_isAlgClosed v) b

    set h : F := f - algebraMap K F c with hh
    by_cases h0 : h = 0
    · exact ⟨c, (sub_eq_zero.mp h0).symm⟩
    exfalso
    have hcoe : ((b - algebraMap K v.toValuationSubring c : v.toValuationSubring) : F) = h := by
      simp [b, hh]
    have hle : ∀ w : Place K F, w.adicValuation h ≤ 1 := fun w => by
      rw [hh]
      exact (Valuation.map_sub _ _ _).trans (max_le (hf w) (w.adicValuation_algebraMap_le_one c))
    have hv : v.adicValuation h < 1 := by
      refine lt_of_le_of_ne (hle v) fun h1 => ?_
      rw [← hcoe, Place.adicValuation_coe_eq_one_iff] at h1
      exact (IsLocalRing.mem_maximalIdeal _ |>.mp hc) h1
    obtain ⟨D, hD, hD0⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor h h0
    have hnn : ∀ w, 0 ≤ D w := fun w => by
      rw [hD w]
      exact ((w.adicValuation_le_one_iff).mp (hle w)).resolve_left h0
    have hpos : 0 < D v := by
      rw [hD v]; exact ord_pos_of_adicValuation_lt_one v h0 hv
    have := degree_pos_of_nonneg hnn hpos IsCurveOver.forall_deg_eq_one_of_isAlgClosed
    omega
  · rintro f ⟨c, rfl⟩
    exact algebraMap_mem_lSpace_zero c

end Constants

section Inf

variable [IsAlgClosed K] [IsCurveOver K F]

theorem exists_zero_sub_const {f₀ : F} (hf₀ : f₀ ∉ LSpace (0 : Divisor K F)) (c : K) :
    ∃ z : Place K F, z.adicValuation (f₀ - algebraMap K F c) < 1 := by
  have hc0 : f₀ - algebraMap K F c ≠ 0 := by
    intro h
    apply hf₀
    rw [sub_eq_zero.mp h]
    exact algebraMap_mem_lSpace_zero c
  have hnot : f₀ - algebraMap K F c ∉ LSpace (0 : Divisor K F) := by
    intro h
    apply hf₀
    have := add_mem h (algebraMap_mem_lSpace_zero (K := K) (F := F) c)
    simpa using this
  rw [mem_lSpace_zero_iff] at hnot
  push_neg at hnot
  obtain ⟨w, hw⟩ := hnot
  have hw' : w.ord (f₀ - algebraMap K F c) < 0 := (w.not_adicValuation_le_one_iff).mp (not_le.mpr hw)
  obtain ⟨D, hD, hD0⟩ := (IsCurveOver.hasPrincipalDivisors (K := K) (F := F)).exists_divisor _ hc0
  obtain ⟨z, hz⟩ := exists_pos_of_degree_eq_zero hD0 (w := w) (by rw [hD w]; exact hw')
    IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  exact ⟨z, adicValuation_lt_one_of_ord_pos z hc0 (by rw [← hD z]; exact hz)⟩

theorem infinite_place {f₀ : F} (hf₀ : f₀ ∉ LSpace (0 : Divisor K F)) : Infinite (Place K F) := by
  choose z hz using exists_zero_sub_const (K := K) (F := F) hf₀
  haveI : Infinite K := inferInstance
  refine Infinite.of_injective z fun c c' hcc' => ?_
  by_contra hne
  have h1 := hz c
  have h2 := hz c'
  rw [← hcc'] at h2
  have hsub : (f₀ - algebraMap K F c') - (f₀ - algebraMap K F c) = algebraMap K F (c - c') := by
    rw [map_sub]; ring
  have hlt : (z c).adicValuation (algebraMap K F (c - c')) < 1 := by
    rw [← hsub]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt h2 h1)
  rw [adicValuation_algebraMap_eq_one (z c) (sub_ne_zero.mpr hne)] at hlt
  exact lt_irrefl _ hlt

end Inf

theorem main [IsAlgClosed K] [IsCurveOver K F] [Nonempty (Place K F)] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    ∃ D : Divisor K F, Divisor.degree D = (g : ℤ) - 1 ∧ ell D = 0 := by
  classical
  have hdeg1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed (K := K) (F := F)
  have hC : ConstantsAreBase K F := constantsAreBase
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC

  have hKc : ell Kc = g := by
    have := hRR 0
    rw [sub_zero, hell0, map_zero] at this
    omega

  obtain ⟨v₀⟩ := (inferInstance : Nonempty (Place K F))
  let D₁ : Divisor K F := (g + 1 : ℤ) • Finsupp.single v₀ 1
  have hD₁ : 2 ≤ ell D₁ := by
    have h1 := hRR D₁
    have hdegD : Divisor.degree D₁ = g + 1 := by
      simp [D₁, Divisor.degree_single, hdeg1 v₀]
    rw [hdegD] at h1
    have : (0 : ℤ) ≤ ell (Kc - D₁) := Int.natCast_nonneg _
    omega
  haveI hfin0 : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    Module.finite_of_finrank_pos (by rw [show Module.finrank K (LSpace (0 : Divisor K F)) = 1 from hell0]; norm_num)
  have hnotle : ¬ (LSpace D₁ ≤ LSpace (0 : Divisor K F)) := by
    intro hle
    have := Submodule.finrank_mono hle
    rw [show Module.finrank K (LSpace (0 : Divisor K F)) = 1 from hell0] at this
    change ell D₁ ≤ 1 at this
    omega
  obtain ⟨f₀, -, hf₀⟩ := Set.not_subset.mp hnotle
  haveI : Infinite (Place K F) := infinite_place hf₀

  obtain ⟨T, -, hcard, hT⟩ := RROpens.exists_finset_subset_ell_sub_sum_single_eq_zero Kc g hRR Kc Set.univ
    Set.infinite_univ
  rw [hKc] at hcard
  set E : Divisor K F := ∑ v ∈ T, Finsupp.single v 1 with hE
  have hdegE : Divisor.degree E = g := by
    rw [hE, map_sum]
    simp [Divisor.degree_single, hdeg1, hcard]
  have hellE : ell E = 1 := by
    have h1 := hRR E
    rw [hT, hdegE] at h1
    omega

  obtain ⟨Q, hQ⟩ := Infinite.exists_notMem_finset T
  refine ⟨E - Finsupp.single Q 1, ?_, ?_⟩
  · rw [map_sub, hdegE, Divisor.degree_single, hdeg1 Q]; ring
  · by_contra hne
    have hEQ : E Q = 0 := by
      rw [hE, Finset.sum_apply']
      exact Finset.sum_eq_zero fun v hv => by
        rw [Finsupp.single_apply, if_neg]
        rintro rfl; exact hQ hv
    haveI : FiniteDimensional K (LSpace E) :=
      Module.finite_of_finrank_pos (by rw [show Module.finrank K (LSpace E) = 1 from hellE]; norm_num)
    have hle : LSpace (E - Finsupp.single Q 1) ≤ LSpace E :=
      lSpace_mono (sub_le_self _ (by simpa using (zero_le_one : (0 : ℤ) ≤ 1)))
    have hrank : Module.finrank K (LSpace (E - Finsupp.single Q 1)) = Module.finrank K (LSpace E) := by
      apply le_antisymm (Submodule.finrank_mono hle)
      rw [show Module.finrank K (LSpace E) = 1 from hellE]
      exact Nat.one_le_iff_ne_zero.mpr hne
    have heq : LSpace (E - Finsupp.single Q 1) = LSpace E := Submodule.eq_of_le_of_finrank_eq hle hrank
    have h1E : (1 : F) ∈ LSpace E := by
      refine lSpace_mono ?_ (one_mem_lSpace_zero (K := K) (F := F))
      intro v
      rw [hE, Finsupp.coe_zero, Pi.zero_apply, Finset.sum_apply']
      exact Finset.sum_nonneg fun w _ => by
        rw [Finsupp.single_apply]; split_ifs <;> norm_num
    rw [← heq, mem_lSpace_iff] at h1E
    have hQ1 := h1E Q
    rw [map_one, Finsupp.sub_apply, hEQ, Finsupp.single_eq_same, zero_sub, ← exp_zero, exp_le_exp] at hQ1
    norm_num at hQ1

end AlgebraicCurve.GenericVanishSol

end

open _root_.AlgebraicCurve _root_.P2MW.S_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero.AlgebraicCurve in
theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K]
    [IsCurveOver K F] [Nonempty (Place K F)] (Kc : Divisor K F) (g : ℕ)
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g) :
    ∃ D : Divisor K F, Divisor.degree D = (g : ℤ) - 1 ∧ ell D = 0 :=
  AlgebraicCurve.GenericVanishSol.main Kc g hRR

end S_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_exists_degree_eq_sub_one_and_ell_eq_zero (solution)
