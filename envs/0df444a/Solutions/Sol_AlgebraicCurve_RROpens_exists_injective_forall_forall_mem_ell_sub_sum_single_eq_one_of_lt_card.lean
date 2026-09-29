-- Prove2me | solution 1 for AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/faaa82ef-8849-5f01-a586-3ff3f1d12343

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

namespace P2MW.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card

set_option autoImplicit false

universe u v w

noncomputable section

open Module

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField LSpace ell mem_lSpace_iff_ord lSpace_mono ell_eq_zero_of_degree_neg"
p2m_open "AlgebraicCurve"

namespace RROpensFinPoolBlockImpl

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

private theorem degree_sub_sum_univ_single [IsCurveOver K F] (D : Divisor K F) {m : ℕ} (v : Fin m → Place K F)
    (hv : ∀ j, (v j).deg = 1) :
    Divisor.degree (D - ∑ j : Fin m, Finsupp.single (v j) 1) = Divisor.degree D - m := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin m)), Divisor.degree (Finsupp.single (v j) (1 : ℤ)) = 1 := fun j _ => by
    rw [Divisor.degree_single, hv j, Nat.cast_one, mul_one]
  rw [map_sub, map_sum, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

private theorem exists_forall_forall_mem_ell_sub_single_lt [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {Θ : Type*} [Fintype Θ] {G : Θ → Divisor K F} (hG : ∀ θ, 0 < ell (G θ))
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i')) (T : Finset ι)
    (hlt : ∑ θ, Divisor.degree (G θ) + T.card < Fintype.card ι) :
    ∃ i, i ∉ T ∧ ∀ θ, ∀ w ∈ B i, ell (G θ - Finsupp.single w 1) < ell (G θ) := by
  classical

  have hex : ∀ θ, ∃ f : F, f ∈ LSpace (G θ) ∧ f ≠ 0 ∧ ∃ Δ : Divisor K F,
      (∀ v, Δ v = v.ord f) ∧ Divisor.degree Δ = 0 := by
    intro θ
    have hbot : LSpace (G θ) ≠ ⊥ := fun h => by
      have : ell (G θ) = 0 := by rw [ell, h, finrank_bot]
      have := hG θ; omega
    obtain ⟨f, hfG, hf0⟩ := (Submodule.ne_bot_iff _).mp hbot
    obtain ⟨Δ, hΔord, hΔdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
    exact ⟨f, hfG, hf0, Δ, hΔord, hΔdeg⟩
  choose f hfG hf0 Δ hΔord hΔdeg using hex
  have hford : ∀ θ v, -(G θ) v ≤ v.ord (f θ) := fun θ => (mem_lSpace_iff_ord.mp (hfG θ)).resolve_left (hf0 θ)
  have heff : ∀ θ v, 0 ≤ (G θ + Δ θ) v := fun θ v => by
    rw [Finsupp.add_apply, hΔord θ v]; have := hford θ v; omega
  have hdeg' : ∀ θ, Divisor.degree (G θ + Δ θ) = Divisor.degree (G θ) := fun θ => by
    rw [map_add, hΔdeg θ, add_zero]

  set U : Finset (Place K F) := Finset.univ.biUnion fun θ => (G θ + Δ θ).support with hU
  have hUcard : (U.card : ℤ) ≤ ∑ θ, Divisor.degree (G θ) := by
    have h1 : (U.card : ℤ) ≤ ∑ θ, ((G θ + Δ θ).support.card : ℤ) := by
      exact_mod_cast Finset.card_biUnion_le
    refine h1.trans (Finset.sum_le_sum fun θ _ => ?_)
    rw [← hdeg' θ]; exact card_support_le_degree (heff θ)

  set Ubl : Finset ι := Finset.univ.filter fun i => ∃ w ∈ B i, w ∈ U with hUbl
  have hUblcard : Ubl.card ≤ U.card := by
    have hdisj' : (↑Ubl : Set ι).PairwiseDisjoint (fun i => B i ∩ U) := by
      intro i _ i' _ hne
      exact (hdisj i i' hne).mono Finset.inter_subset_left Finset.inter_subset_left
    calc Ubl.card = ∑ i ∈ Ubl, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ Ubl, (B i ∩ U).card := Finset.sum_le_sum fun i hi => by
          obtain ⟨w, hwB, hwU⟩ := (Finset.mem_filter.mp hi).2
          exact Finset.card_pos.mpr ⟨w, Finset.mem_inter.mpr ⟨hwB, hwU⟩⟩
      _ = (Ubl.biUnion fun i => B i ∩ U).card := (Finset.card_biUnion hdisj').symm
      _ ≤ U.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun i _ => Finset.inter_subset_right)

  have hcard : ((Ubl ∪ T).card : ℤ) < (Finset.univ : Finset ι).card := by
    have h2 : ((Ubl ∪ T).card : ℤ) ≤ Ubl.card + T.card := by exact_mod_cast Finset.card_union_le _ _
    have h3 : (Ubl.card : ℤ) ≤ U.card := by exact_mod_cast hUblcard
    rw [Finset.card_univ]
    linarith
  obtain ⟨i, -, hi⟩ : ∃ i ∈ (Finset.univ : Finset ι), i ∉ Ubl ∪ T := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset ι) ⊆ Ubl ∪ T := fun i hi => h i hi
    have h' : ((Finset.univ : Finset ι).card : ℤ) ≤ (Ubl ∪ T).card := by exact_mod_cast Finset.card_le_card hsub
    linarith
  rw [Finset.mem_union, not_or] at hi
  obtain ⟨hiU, hiT⟩ := hi
  refine ⟨i, hiT, fun θ w hw => ?_⟩

  have hwU : w ∉ U := fun hwU => hiU (Finset.mem_filter.mpr ⟨Finset.mem_univ i, w, hw, hwU⟩)
  have hGw : (G θ + Δ θ) w = 0 := by
    by_contra hne
    exact hwU (Finset.mem_biUnion.mpr ⟨θ, Finset.mem_univ θ, Finsupp.mem_support_iff.mpr hne⟩)
  rw [Finsupp.add_apply, hΔord θ w] at hGw
  have hfnot : f θ ∉ LSpace (G θ - Finsupp.single w 1) := by
    intro h
    have h' := (mem_lSpace_iff_ord.mp h).resolve_left (hf0 θ) w
    rw [Finsupp.sub_apply, Finsupp.single_eq_same] at h'
    omega
  have hle : LSpace (G θ - Finsupp.single w 1) ≤ LSpace (G θ) := lSpace_mono (sub_single_le (G θ) w)
  have hlt' : LSpace (G θ - Finsupp.single w 1) < LSpace (G θ) :=
    lt_of_le_of_ne hle fun h => hfnot (h ▸ hfG θ)
  haveI : Module.Finite K (LSpace (G θ)) := finite_lSpace hRR w (G θ)
  exact Submodule.finrank_lt_finrank_of_lt hlt'

private theorem exists_injective_forall_transversal_ell_add_le [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} {N : ℕ} (D : Fin N → Divisor K F) (hdeg : ∀ k, Divisor.degree (D k) = r)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * r * b ^ (r - g) + (r - g) < Fintype.card ι) :
    ∀ m : ℕ, m + g ≤ r →
      ∃ a : Fin m → ι, Function.Injective a ∧
        ∀ k, ∀ v : Fin m → Place K F, (∀ j, v j ∈ B (a j)) →
          ell (D k - ∑ j : Fin m, Finsupp.single (v j) 1) + m ≤ ell (D k) := by
  classical
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun k v _ => by simp⟩
  | succ m ih =>
    intro hm
    obtain ⟨a, ha, hell⟩ := ih (by omega)

    let Θ := Fin N × (∀ j : Fin m, ↥(B (a j)))
    let G : Θ → Divisor K F := fun θ => D θ.1 - ∑ j : Fin m, Finsupp.single ((θ.2 j : Place K F)) 1
    have hdegG : ∀ θ : Θ, Divisor.degree (G θ) = r - m := fun θ => by
      rw [degree_sub_sum_univ_single (D θ.1) (fun j => (θ.2 j : Place K F)) (fun j => hB _ _ (θ.2 j).2), hdeg]
    have hGpos : ∀ θ : Θ, 0 < ell (G θ) := fun θ => by
      have h := degree_add_one_sub_le_ell hRR (G θ)
      rw [hdegG θ] at h
      have : (0 : ℤ) < ell (G θ) := by push_cast at h ⊢; linarith
      exact_mod_cast this

    have hΘcard : Fintype.card Θ ≤ N * b ^ m := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi]
      refine Nat.mul_le_mul_left N ?_
      calc ∏ j : Fin m, Fintype.card ↥(B (a j)) ≤ ∏ _j : Fin m, b :=
            Finset.prod_le_prod' fun j _ => by rw [Fintype.card_coe]; exact hb (a j)
        _ = b ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hbm : b ^ m ≤ b ^ (r - g) := Nat.pow_le_pow_right hb1 (by omega)
    have hlt : ∑ θ : Θ, Divisor.degree (G θ) + (Finset.univ.image a).card < Fintype.card ι := by
      rw [Finset.sum_congr rfl fun θ _ => hdegG θ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
      have hΘ : ((Fintype.card Θ : ℕ) : ℤ) ≤ (N : ℤ) * (b ^ (r - g) : ℕ) := by
        exact_mod_cast hΘcard.trans (Nat.mul_le_mul_left N hbm)
      have hrm : (0 : ℤ) ≤ (r : ℤ) - m := by omega
      have hmr : (m : ℤ) ≤ r := by omega
      have h1 : ((Fintype.card Θ : ℕ) : ℤ) * ((r : ℤ) - m) ≤ (N : ℤ) * (b ^ (r - g) : ℕ) * r := by
        calc ((Fintype.card Θ : ℕ) : ℤ) * ((r : ℤ) - m) ≤ (N : ℤ) * (b ^ (r - g) : ℕ) * ((r : ℤ) - m) :=
              mul_le_mul_of_nonneg_right hΘ hrm
          _ ≤ (N : ℤ) * (b ^ (r - g) : ℕ) * r := by
              apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h2 : ((N * r * b ^ (r - g) + (r - g) : ℕ) : ℤ) < (Fintype.card ι : ℤ) := by exact_mod_cast hcard
      have hmX : (m : ℤ) ≤ ((r - g : ℕ) : ℤ) := by exact_mod_cast (show m ≤ r - g by omega)
      have h3 : ((N * r * b ^ (r - g) + (r - g) : ℕ) : ℤ) = (N : ℤ) * (b ^ (r - g) : ℕ) * r + ((r - g : ℕ) : ℤ) := by
        push_cast; ring
      rw [h3] at h2
      linarith
    obtain ⟨i, hiT, hgood⟩ := exists_forall_forall_mem_ell_sub_single_lt hRR hGpos B hdisj (Finset.univ.image a) hlt

    refine ⟨Fin.snoc a i, ?_, ?_⟩
    ·
      intro j j' hjj
      induction j using Fin.lastCases with
      | last =>
        induction j' using Fin.lastCases with
        | last => rfl
        | cast j' =>
          exfalso; apply hiT
          rw [Fin.snoc_last, Fin.snoc_castSucc] at hjj
          exact Finset.mem_image.mpr ⟨j', Finset.mem_univ _, hjj.symm⟩
      | cast j =>
        induction j' using Fin.lastCases with
        | last =>
          exfalso; apply hiT
          rw [Fin.snoc_last, Fin.snoc_castSucc] at hjj
          exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hjj⟩
        | cast j' =>
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hjj
          rw [ha hjj]
    · intro k v hv

      let θ : Θ := ⟨k, fun j => ⟨v (Fin.castSucc j), by have := hv (Fin.castSucc j); rwa [Fin.snoc_castSucc] at this⟩⟩
      have hw : v (Fin.last m) ∈ B i := by have := hv (Fin.last m); rwa [Fin.snoc_last] at this
      have hdrop := hgood θ (v (Fin.last m)) hw
      have hprev := hell k (fun j => v (Fin.castSucc j)) (fun j => (θ.2 j).2)
      rw [Fin.sum_univ_castSucc,
        show D k - (∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1 + Finsupp.single (v (Fin.last m)) 1)
            = D k - ∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1 - Finsupp.single (v (Fin.last m)) 1 from by abel]
      change ell (D k - ∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1 - Finsupp.single (v (Fin.last m)) 1) <
        ell (D k - ∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1) at hdrop
      change ell (D k - ∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1) + m ≤ ell (D k) at hprev
      omega

theorem exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card_impl [IsCurveOver K F]
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    {N : ℕ} (D : Fin N → Divisor K F) (hdeg : ∀ k, Divisor.degree (D k) = r)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * r * b ^ (r - g) + (r - g) < Fintype.card ι) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin (r - g) → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) = 1 := by
  classical
  have hKc : Divisor.degree Kc = 2 * (g : ℤ) - 2 := by
    have h0 := hRR 0
    have h1 := hRR Kc
    rw [sub_zero, map_zero] at h0
    rw [sub_self] at h1
    linarith
  have hellD : ∀ k, (ell (D k) : ℤ) = r + 1 - g := fun k => by
    have hz : ell (Kc - D k) = 0 :=
      ell_eq_zero_of_degree_neg (by rw [map_sub, hKc, hdeg k]; omega)
    have h := hRR (D k)
    rw [hz, hdeg k] at h
    push_cast at h
    linarith
  have hgr' : g ≤ r := by omega
  obtain ⟨a, ha, hell⟩ :=
    exists_injective_forall_transversal_ell_add_le hRR D hdeg B hB hdisj hb1 hb hcard (r - g) (by omega)
  refine ⟨a, ha, fun k v hv => ?_⟩
  apply le_antisymm
  · have h1 := hell k v hv
    have h3 : (ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) : ℤ) + (r - g : ℕ) ≤ ell (D k) := by
      exact_mod_cast h1
    push_cast [Nat.cast_sub hgr'] at h3
    have := hellD k
    have : (ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) : ℤ) ≤ 1 := by linarith
    exact_mod_cast this
  · have h := degree_add_one_sub_le_ell hRR (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1)
    rw [degree_sub_sum_univ_single (D k) v (fun j => hB _ _ (hv j)), hdeg k] at h
    push_cast [Nat.cast_sub hgr'] at h
    have : (1 : ℤ) ≤ ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) := by linarith
    exact_mod_cast this

end WithPack

end RROpensFinPoolBlockImpl

end AlgebraicCurve

end

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card.AlgebraicCurve"

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {Kc : Divisor K F} {g : ℕ}
    (hRR : ∀ D : Divisor K F, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g)
    {r : ℕ} (hgr : 2 * g ≤ r + 1)
    {N : ℕ} (D : Fin N → Divisor K F) (hdeg : ∀ k, Divisor.degree (D k) = r)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * r * b ^ (r - g) + (r - g) < Fintype.card ι) :
    ∃ a : Fin (r - g) → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin (r - g) → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin (r - g), Finsupp.single (v j) 1) = 1 :=
  AlgebraicCurve.RROpensFinPoolBlockImpl.exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card_impl
    hRR hgr D hdeg B hB hdisj hb1 hb hcard

end S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_eq_one_of_lt_card (solution)
