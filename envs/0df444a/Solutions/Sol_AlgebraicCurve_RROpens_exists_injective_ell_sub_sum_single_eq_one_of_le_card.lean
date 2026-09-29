-- Prove2me | solution 1 for AlgebraicCurve.RROpens.exists_injective_ell_sub_sum_single_eq_one_of_le_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/8e46d26d-5707-524b-b1ec-3de3eaffb260

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card

set_option autoImplicit false

universe u v

noncomputable section

open Module

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField LSpace ell mem_lSpace_iff_ord lSpace_mono ell_eq_zero_of_degree_neg"
p2m_open "AlgebraicCurve"

namespace RROpensFinPoolImpl

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem one_le_deg [IsCurveOver K F] (P : Place K F) : 1 ≤ P.deg := by
  haveI : Module.Finite K P.ResidueField := IsCurveOver.finite_residueField P
  exact Module.finrank_pos

private theorem degree_eq_sum_support (D : Divisor K F) :
    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  classical
  conv_lhs => rw [← Finsupp.sum_single D, Finsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun v _ => Divisor.degree_single v (D v)

private theorem card_support_le_degree [IsCurveOver K F] {E : Divisor K F} (hE : ∀ v, 0 ≤ E v) :
    (E.support.card : ℤ) ≤ Divisor.degree E := by
  rw [degree_eq_sum_support]
  have h1 : ∀ v ∈ E.support, (1 : ℤ) ≤ E v * (v.deg : ℤ) := fun v hv => by
    have hv : E v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have hv1 : 1 ≤ E v := by have := hE v; omega
    have hd : (1 : ℤ) ≤ (v.deg : ℤ) := by exact_mod_cast one_le_deg v
    nlinarith
  calc (E.support.card : ℤ) = ∑ v ∈ E.support, (1 : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ v ∈ E.support, E v * (v.deg : ℤ) := Finset.sum_le_sum h1

private theorem sub_single_le (G : Divisor K F) (Q : Place K F) :
    G - Finsupp.single Q 1 ≤ G := by
  classical
  rw [Finsupp.le_def]; intro v; rw [Finsupp.sub_apply]
  have : (0 : ℤ) ≤ Finsupp.single Q 1 v := by
    rw [Finsupp.single_apply]; split_ifs <;> norm_num
  linarith

private theorem degree_sub_sum_single (D : Divisor K F) {S T : Finset (Place K F)}
    (hS : ∀ v ∈ S, v.deg = 1) (hTS : T ⊆ S) :
    Divisor.degree (D - ∑ v ∈ T, Finsupp.single v 1) = Divisor.degree D - T.card := by
  have h : ∀ v ∈ T, Divisor.degree (Finsupp.single v (1 : ℤ)) = 1 := fun v hv => by
    rw [Divisor.degree_single, hS v (hTS hv), Nat.cast_one, mul_one]
  rw [map_sub, map_sum, Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

section WithPack

variable {Kc : Divisor K F} {g : ℕ}

private theorem degree_add_one_sub_le_ell
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (E : Divisor K F) : Divisor.degree E + 1 - (g : ℤ) ≤ (ell E : ℤ) := by
  have h := hRR E
  have h0 : (0 : ℤ) ≤ (ell (Kc - E) : ℤ) := Int.natCast_nonneg _
  linarith

private theorem finite_lSpace [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (P : Place K F) (D : Divisor K F) : Module.Finite K (LSpace D) := by
  classical
  set n : ℕ := ((g : ℤ) - Divisor.degree D).toNat with hn
  set D' : Divisor K F := D + (n : ℤ) • Finsupp.single P 1 with hD'
  have hdeg : (g : ℤ) ≤ Divisor.degree D' := by
    have h1 : (1 : ℤ) ≤ (P.deg : ℤ) := by exact_mod_cast one_le_deg P
    have hn0 : (g : ℤ) - Divisor.degree D ≤ (n : ℤ) := by
      rw [hn]; exact Int.self_le_toNat _
    rw [hD', map_add, map_zsmul, Divisor.degree_single, one_mul, smul_eq_mul]
    nlinarith [Int.natCast_nonneg n]
  have hpos : 0 < finrank K (LSpace D') := by
    have h := degree_add_one_sub_le_ell hRR D'
    have : (1 : ℤ) ≤ (ell D' : ℤ) := by linarith
    have h' : 1 ≤ ell D' := by exact_mod_cast this
    exact h'
  haveI : Module.Finite K (LSpace D') := Module.finite_of_finrank_pos hpos
  have hle : D ≤ D' := by
    rw [Finsupp.le_def]; intro v
    rw [hD', Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    have : (0 : ℤ) ≤ Finsupp.single P 1 v := by
      rw [Finsupp.single_apply]; split_ifs <;> norm_num
    nlinarith [Int.natCast_nonneg n]
  exact Submodule.finiteDimensional_of_le (lSpace_mono hle)

private theorem exists_mem_ell_sub_single_lt [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {G : Divisor K F} (hG : 0 < ell G) (B T : Finset (Place K F))
    (hlt : Divisor.degree G + B.card < T.card) :
    ∃ Q ∈ T, Q ∉ B ∧ ell (G - Finsupp.single Q 1) < ell G := by
  classical

  have hbot : LSpace G ≠ ⊥ := fun h => by
    have : ell G = 0 := by rw [ell, h, finrank_bot]
    omega
  obtain ⟨f, hfG, hf0⟩ := (Submodule.ne_bot_iff _).mp hbot
  obtain ⟨Δ, hΔord, hΔdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hford : ∀ v, -G v ≤ v.ord f := (mem_lSpace_iff_ord.mp hfG).resolve_left hf0

  have heff : ∀ v, 0 ≤ (G + Δ) v := fun v => by
    rw [Finsupp.add_apply, hΔord v]; have := hford v; omega
  have hdeg' : Divisor.degree (G + Δ) = Divisor.degree G := by
    rw [map_add, hΔdeg, add_zero]

  have hcard : (((G + Δ).support ∪ B).card : ℤ) < T.card := by
    have h1 := card_support_le_degree heff
    have h2 : (((G + Δ).support ∪ B).card : ℤ) ≤ (G + Δ).support.card + B.card := by
      exact_mod_cast Finset.card_union_le _ _
    linarith
  obtain ⟨Q, hQT, hQ⟩ : ∃ Q ∈ T, Q ∉ (G + Δ).support ∪ B := by
    by_contra h
    have hsub : T ⊆ (G + Δ).support ∪ B := fun Q hQ => by
      by_contra hQ'
      exact h ⟨Q, hQ, hQ'⟩
    have h' : (T.card : ℤ) ≤ ((G + Δ).support ∪ B).card := by
      exact_mod_cast Finset.card_le_card hsub
    linarith
  rw [Finset.mem_union, not_or, Finsupp.notMem_support_iff, Finsupp.add_apply, hΔord Q] at hQ
  obtain ⟨hGQ, hQB⟩ := hQ
  refine ⟨Q, hQT, hQB, ?_⟩

  have hfnot : f ∉ LSpace (G - Finsupp.single Q 1) := by
    intro h
    have h' := (mem_lSpace_iff_ord.mp h).resolve_left hf0 Q
    rw [Finsupp.sub_apply, Finsupp.single_eq_same] at h'
    omega
  have hle : LSpace (G - Finsupp.single Q 1) ≤ LSpace G := lSpace_mono (sub_single_le G Q)
  have hlt' : LSpace (G - Finsupp.single Q 1) < LSpace G :=
    lt_of_le_of_ne hle fun h => hfnot (h ▸ hfG)
  haveI : Module.Finite K (LSpace G) := finite_lSpace hRR Q G
  exact Submodule.finrank_lt_finrank_of_lt hlt'

private theorem exists_subset_card_eq_ell_add_le [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    (S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1) (D : Divisor K F)
    (hDS : Divisor.degree D < S.card) :
    ∀ i : ℕ, (i : ℤ) + g ≤ Divisor.degree D + 1 →
      ∃ T : Finset (Place K F), T ⊆ S ∧ T.card = i ∧
        ell (D - ∑ v ∈ T, Finsupp.single v 1) + i ≤ ell D := by
  classical
  intro i
  induction i with
  | zero =>
    intro _
    exact ⟨∅, Finset.empty_subset _, Finset.card_empty, by simp⟩
  | succ i ih =>
    intro hi
    push_cast at hi
    obtain ⟨T, hTS, hTcard, hTell⟩ := ih (by linarith)
    have hdegG : Divisor.degree (D - ∑ v ∈ T, Finsupp.single v 1) = Divisor.degree D - i := by
      rw [degree_sub_sum_single D hS hTS, hTcard]
    have hGpos : 0 < ell (D - ∑ v ∈ T, Finsupp.single v 1) := by
      have h := degree_add_one_sub_le_ell hRR (D - ∑ v ∈ T, Finsupp.single v 1)
      rw [hdegG] at h
      have : (0 : ℤ) < ell (D - ∑ v ∈ T, Finsupp.single v 1) := by linarith
      exact_mod_cast this
    obtain ⟨Q, hQS, hQT, hdrop⟩ :=
      exists_mem_ell_sub_single_lt hRR hGpos T S (by rw [hdegG, hTcard]; linarith)
    refine ⟨insert Q T, Finset.insert_subset hQS hTS,
      by rw [Finset.card_insert_of_notMem hQT, hTcard], ?_⟩
    rw [Finset.sum_insert hQT,
      show D - (Finsupp.single Q 1 + ∑ v ∈ T, Finsupp.single v 1)
          = D - ∑ v ∈ T, Finsupp.single v 1 - Finsupp.single Q 1 from by abel]
    omega

theorem exists_injective_ell_sub_sum_single_eq_one_of_le_card_impl [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    (S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1) (hcard : r + 1 ≤ S.card)
    (D : Divisor K F) (hdeg : Divisor.degree D = r) :
    ∃ f : Fin (r - g) → Place K F, Function.Injective f ∧ (∀ j, f j ∈ S) ∧
      ell (D - ∑ j : Fin (r - g), Finsupp.single (f j) 1) = 1 := by
  classical

  have hKc : Divisor.degree Kc = 2 * (g : ℤ) - 2 := by
    have h0 := hRR 0
    have h1 := hRR Kc
    rw [sub_zero, map_zero] at h0
    rw [sub_self] at h1
    linarith

  have hz : ell (Kc - D) = 0 :=
    ell_eq_zero_of_degree_neg (by rw [map_sub, hKc, hdeg]; omega)
  have hellD : (ell D : ℤ) = r + 1 - g := by
    have h := hRR D
    rw [hz, hdeg] at h
    push_cast at h
    linarith
  have hgr' : g ≤ r := by omega
  have hrS : r < S.card := hcard

  obtain ⟨T, hTS, hTcard, hTell⟩ :=
    exists_subset_card_eq_ell_add_le hRR S hS D (by rw [hdeg]; exact_mod_cast hrS) (r - g)
      (by rw [hdeg]; push_cast [Nat.cast_sub hgr']; linarith)

  have hE : ell (D - ∑ v ∈ T, Finsupp.single v 1) = 1 := by
    apply le_antisymm
    · omega
    · have h := degree_add_one_sub_le_ell hRR (D - ∑ v ∈ T, Finsupp.single v 1)
      rw [degree_sub_sum_single D hS hTS, hTcard, hdeg] at h
      push_cast [Nat.cast_sub hgr'] at h
      have : (1 : ℤ) ≤ ell (D - ∑ v ∈ T, Finsupp.single v 1) := by linarith
      exact_mod_cast this

  let e : {v // v ∈ T} ≃ Fin (r - g) := T.equivFinOfCardEq hTcard
  refine ⟨fun j => (e.symm j : Place K F), Subtype.val_injective.comp e.symm.injective,
    fun j => hTS (e.symm j).2, ?_⟩
  have hsum : ∑ j : Fin (r - g), Finsupp.single ((e.symm j : Place K F)) (1 : ℤ)
      = ∑ v ∈ T, Finsupp.single v 1 := by
    rw [← Finset.sum_coe_sort T]
    exact Fintype.sum_equiv e.symm _ _ fun j => rfl
  rw [hsum]
  exact hE

end WithPack

end RROpensFinPoolImpl

end AlgebraicCurve

end

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card.AlgebraicCurve"

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    (S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1) (hcard : r + 1 ≤ S.card)
    (D : Divisor K F) (hdeg : Divisor.degree D = r) :
    ∃ f : Fin (r - g) → Place K F, Function.Injective f ∧ (∀ j, f j ∈ S) ∧
      ell (D - ∑ j : Fin (r - g), Finsupp.single (f j) 1) = 1 :=
  AlgebraicCurve.RROpensFinPoolImpl.exists_injective_ell_sub_sum_single_eq_one_of_le_card_impl
    hRR hgr S hS hcard D hdeg

end S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_exists_injective_ell_sub_sum_single_eq_one_of_le_card (solution)
