-- Prove2me | solution 1 for AlgebraicCurve.RROpens.exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/3cce2373-d6f7-573f-b82e-3e95d2db5b4f

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_AlgebraicCurve_ell_le_ell_sub_single_add_deg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card

universe u v w

noncomputable section

open Module

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Divisor Divisor.degree Divisor.degree_single HasPrincipalDivisors HasPrincipalDivisors.exists_divisor IsCurveOver IsCurveOver.finite_residueField LSpace ell mem_lSpace_iff_ord lSpace_mono ell_le_ell_sub_single_add_deg"
p2m_open "AlgebraicCurve"

namespace RROpensExactDropImpl

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

private theorem degree_sub_sum_univ_single [IsCurveOver K F] (D : Divisor K F) {m : ℕ} (v : Fin m → Place K F)
    (hv : ∀ j, (v j).deg = 1) :
    Divisor.degree (D - ∑ j : Fin m, Finsupp.single (v j) 1) = Divisor.degree D - m := by
  have h : ∀ j ∈ (Finset.univ : Finset (Fin m)), Divisor.degree (Finsupp.single (v j) (1 : ℤ)) = 1 := fun j _ => by
    rw [Divisor.degree_single, hv j, Nat.cast_one, mul_one]
  rw [map_sub, map_sum, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

private theorem ell_le_ell_sub_sum_add [IsCurveOver K F] (D : Divisor K F) {m : ℕ} (v : Fin m → Place K F)
    (hv : ∀ j, (v j).deg = 1) :
    ell D ≤ ell (D - ∑ j : Fin m, Finsupp.single (v j) 1) + m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : ell D ≤ ell (D - ∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1) + m :=
      ih (fun j => v (Fin.castSucc j)) (fun j => hv _)
    have h2 := ell_le_ell_sub_single_add_deg
      (D - ∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1) (v (Fin.last m))
    rw [hv] at h2
    rw [Fin.sum_univ_castSucc,
      show D - (∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1 + Finsupp.single (v (Fin.last m)) 1)
          = D - ∑ j : Fin m, Finsupp.single (v (Fin.castSucc j)) 1 - Finsupp.single (v (Fin.last m)) 1 from by abel]
    omega

private theorem exists_forall_forall_mem_ell_sub_single_lt [IsCurveOver K F]
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
  haveI : Module.Finite K (LSpace (G θ)) := Module.finite_of_finrank_pos (by simpa [ell] using hG θ)
  exact Submodule.finrank_lt_finrank_of_lt hlt'

private theorem exists_injective_forall_transversal_ell_add_le [IsCurveOver K F]
    {N : ℕ} (D : Fin N → Divisor K F) (e ρ : ℕ)
    (hℓ : ∀ k, e ≤ ell (D k)) (hdeg : ∀ k, Divisor.degree (D k) ≤ ρ)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * ρ * b ^ e + e < Fintype.card ι) :
    ∀ m : ℕ, m ≤ e →
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
    have hdegG : ∀ θ : Θ, Divisor.degree (G θ) = Divisor.degree (D θ.1) - m := fun θ => by
      change Divisor.degree (D θ.1 - ∑ j : Fin m, Finsupp.single ((θ.2 j : Place K F)) 1) = _
      rw [degree_sub_sum_univ_single (D θ.1) (fun j => (θ.2 j : Place K F)) (fun j => hB _ _ (θ.2 j).2)]
    have hGpos : ∀ θ : Θ, 0 < ell (G θ) := fun θ => by
      have h := ell_le_ell_sub_sum_add (D θ.1) (fun j => (θ.2 j : Place K F)) (fun j => hB _ _ (θ.2 j).2)
      have := hℓ θ.1
      change ell (D θ.1) ≤ ell (G θ) + m at h
      omega

    have hΘcard : Fintype.card Θ ≤ N * b ^ m := by
      rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_pi]
      refine Nat.mul_le_mul_left N ?_
      calc ∏ j : Fin m, Fintype.card ↥(B (a j)) ≤ ∏ _j : Fin m, b :=
            Finset.prod_le_prod' fun j _ => by rw [Fintype.card_coe]; exact hb (a j)
        _ = b ^ m := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hbm : b ^ m ≤ b ^ e := Nat.pow_le_pow_right hb1 (by omega)
    have hlt : ∑ θ : Θ, Divisor.degree (G θ) + (Finset.univ.image a).card < Fintype.card ι := by
      rw [Finset.card_image_of_injective _ ha, Finset.card_univ, Fintype.card_fin]
      have hsum : ∑ θ : Θ, Divisor.degree (G θ) ≤ (Fintype.card Θ : ℤ) * ρ := by
        calc ∑ θ : Θ, Divisor.degree (G θ) ≤ ∑ _θ : Θ, (ρ : ℤ) := Finset.sum_le_sum fun θ _ => by
              rw [hdegG θ]; have := hdeg θ.1; have : (0 : ℤ) ≤ m := Int.natCast_nonneg _; linarith
          _ = (Fintype.card Θ : ℤ) * ρ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hΘ : ((Fintype.card Θ : ℕ) : ℤ) ≤ (N : ℤ) * (b ^ e : ℕ) := by
        exact_mod_cast hΘcard.trans (Nat.mul_le_mul_left N hbm)
      have hΘρ : ((Fintype.card Θ : ℕ) : ℤ) * ρ ≤ (N : ℤ) * (b ^ e : ℕ) * ρ :=
        mul_le_mul_of_nonneg_right hΘ (Int.natCast_nonneg _)
      have h2 : ((N * ρ * b ^ e + e : ℕ) : ℤ) < (Fintype.card ι : ℤ) := by exact_mod_cast hcard
      have h3 : ((N * ρ * b ^ e + e : ℕ) : ℤ) = (N : ℤ) * (b ^ e : ℕ) * ρ + e := by push_cast; ring
      rw [h3] at h2
      have hme : (m : ℤ) ≤ e := by exact_mod_cast (show m ≤ e by omega)
      linarith
    obtain ⟨i, hiT, hgood⟩ := exists_forall_forall_mem_ell_sub_single_lt hGpos B hdisj (Finset.univ.image a) hlt

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

theorem exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card_impl [IsCurveOver K F]
    {N : ℕ} (D : Fin N → Divisor K F) (e ρ : ℕ)
    (hℓ : ∀ k, e ≤ ell (D k)) (hdeg : ∀ k, Divisor.degree (D k) ≤ ρ)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * ρ * b ^ e + e < Fintype.card ι) :
    ∃ a : Fin e → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin e → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin e, Finsupp.single (v j) 1) + e = ell (D k) := by
  classical
  obtain ⟨a, ha, hell⟩ :=
    exists_injective_forall_transversal_ell_add_le D e ρ hℓ hdeg B hB hdisj hb1 hb hcard e le_rfl
  refine ⟨a, ha, fun k v hv => le_antisymm (hell k v hv) ?_⟩
  exact ell_le_ell_sub_sum_add (D k) v (fun j => hB _ _ (hv j))

end RROpensExactDropImpl

end AlgebraicCurve

end

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card.AlgebraicCurve"

theorem solution
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    {N : ℕ} (D : Fin N → Divisor K F) (e ρ : ℕ)
    (hℓ : ∀ k, e ≤ ell (D k)) (hdeg : ∀ k, Divisor.degree (D k) ≤ ρ)
    {ι : Type w} [Fintype ι] [DecidableEq ι] (B : ι → Finset (Place K F))
    (hB : ∀ i, ∀ v ∈ B i, v.deg = 1) (hdisj : ∀ i i', i ≠ i' → Disjoint (B i) (B i'))
    {b : ℕ} (hb1 : 1 ≤ b) (hb : ∀ i, (B i).card ≤ b)
    (hcard : N * ρ * b ^ e + e < Fintype.card ι) :
    ∃ a : Fin e → ι, Function.Injective a ∧
      ∀ k, ∀ v : Fin e → Place K F, (∀ j, v j ∈ B (a j)) →
        ell (D k - ∑ j : Fin e, Finsupp.single (v j) 1) + e = ell (D k) :=
  AlgebraicCurve.RROpensExactDropImpl.exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card_impl
    D e ρ hℓ hdeg B hB hdisj hb1 hb hcard

end S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card
end P2MW
export P2MW.S_AlgebraicCurve_RROpens_exists_injective_forall_forall_mem_ell_sub_sum_single_add_eq_ell_of_lt_card (solution)
