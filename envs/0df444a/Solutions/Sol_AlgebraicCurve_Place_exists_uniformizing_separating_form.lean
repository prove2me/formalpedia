-- Prove2me | solution 1 for AlgebraicCurve.Place.exists_uniformizing_separating_form
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/d4e43d9b-8c8c-52d3-be34-da860192d934

import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Theorems.Thm_AlgebraicCurve_Place_min_ord_le_ord_add
import Mathlib.LinearAlgebra.Lagrange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_Place_exists_uniformizing_separating_form

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_AlgebraicCurve_Place_exists_uniformizing_separating_form.AlgebraicCurve Polynomial"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ord ord_zero ord_mul ord_coe_unit algebraMap_mem' toValuationSubring min_ord_le_ord_add"
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

private theorem mwALGN_ord_algebraMap (v : Place k F) {c : k} (hc : c ≠ 0) :
    v.ord (algebraMap k F c) = 0 := by
  have hu : IsUnit (⟨algebraMap k F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
    refine IsUnit.of_mul_eq_one ⟨algebraMap k F c⁻¹, v.algebraMap_mem' _⟩ (Subtype.ext ?_)
    push_cast
    rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have h := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec] at h

private def mwALGN_ordGe (v : Place k F) (m : ℤ) : Submodule k F where
  carrier := {x | x = 0 ∨ m ≤ v.ord x}
  zero_mem' := Or.inl rfl
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    by_cases hx0 : x = 0
    · subst hx0
      simpa using hy
    by_cases hy0 : y = 0
    · subst hy0
      simpa using hx
    by_cases hxy : x + y = 0
    · exact Or.inl hxy
    right
    have hx' : m ≤ v.ord x := hx.resolve_left hx0
    have hy' : m ≤ v.ord y := hy.resolve_left hy0
    have h := v.min_ord_le_ord_add hx0 hy0 hxy
    omega
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    by_cases hc : c = 0
    · subst hc
      simp
    by_cases hx0 : x = 0
    · subst hx0
      simp
    right
    rw [Algebra.smul_def, v.ord_mul ((_root_.map_ne_zero _).mpr hc) hx0,
      mwALGN_ord_algebraMap v hc, zero_add]
    exact hx.resolve_left hx0

private theorem mwALGN_mem_ordGe_iff (v : Place k F) (m : ℤ) (x : F) :
    x ∈ mwALGN_ordGe v m ↔ x = 0 ∨ m ≤ v.ord x := Iff.rfl

private theorem mwALGN_mem_of_forall_sum_pow_smul_mem (W : Submodule k F) {m : ℕ}
    (z : Fin (m + 1) → F) (θ : Fin (m + 1) → k) (hθ : Function.Injective θ)
    (h : ∀ l, (∑ i : Fin (m + 1), θ l ^ (i : ℕ) • z i) ∈ W) (i : Fin (m + 1)) : z i ∈ W := by
  classical
  set B : Fin (m + 1) → Polynomial k := fun l => Lagrange.basis Finset.univ θ l with hB
  have hvs : Set.InjOn θ (Finset.univ : Finset (Fin (m + 1))) := hθ.injOn
  have hid : ∀ i' : Fin (m + 1),
      (X ^ (i' : ℕ) : Polynomial k) = ∑ l, C (θ l ^ (i' : ℕ)) * B l := by
    intro i'
    have hdeg : (X ^ (i' : ℕ) : Polynomial k).degree
        < (Finset.univ : Finset (Fin (m + 1))).card := by
      rw [Polynomial.degree_X_pow, Finset.card_univ, Fintype.card_fin]
      exact_mod_cast i'.2
    have h1 := Lagrange.eq_interpolate hvs hdeg
    rw [Lagrange.interpolate_apply] at h1
    simpa only [Polynomial.eval_pow, Polynomial.eval_X] using h1
  have hδ : ∀ i' : Fin (m + 1),
      (∑ l, (B l).coeff i * θ l ^ (i' : ℕ)) = if i = i' then 1 else 0 := by
    intro i'
    have h1 := congrArg (fun p : Polynomial k => p.coeff i) (hid i')
    simp only [Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul] at h1
    have h2 : (∑ l, (B l).coeff i * θ l ^ (i' : ℕ)) = ∑ l, θ l ^ (i' : ℕ) * (B l).coeff i :=
      Finset.sum_congr rfl fun l _ => mul_comm _ _
    rw [h2, ← h1]
    by_cases hii : i = i'
    · rw [if_pos hii, if_pos (congrArg Fin.val hii)]
    · rw [if_neg hii, if_neg fun h => hii (Fin.ext h)]
  have hcomb : ∑ l, (B l).coeff i • (∑ i' : Fin (m + 1), θ l ^ (i' : ℕ) • z i') = z i := by
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, hδ, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
  rw [← hcomb]
  exact W.sum_mem fun l _ => W.smul_mem _ (h l)

end AlgebraicCurve.Place

open _root_.AlgebraicCurve.Place _root_.P2MW.S_AlgebraicCurve_Place_exists_uniformizing_separating_form.AlgebraicCurve.Place in
theorem solution
    {k F : Type*} [Field k] [Field F] [Algebra k F]
    (v : Place k F) {j : F} {n : ℕ} (β : Fin n → F)
    (cv : k) (hcv : 0 < v.ord (j - algebraMap k F cv))
    (βv : Fin n → k)
    (hβv : ∀ i, β i = algebraMap k F (βv i) ∨ 0 < v.ord (β i - algebraMap k F (βv i)))
    (hU1 : v.ord (j - algebraMap k F cv) = 1 ∨ ∃ i, v.ord (β i - algebraMap k F (βv i)) = 1)
    {r : ℕ} (pt : Fin r → Place k F) (cpt : Fin r → k) (βpt : Fin r → Fin n → k)
    (hS1 : ∀ t, pt t ≠ v → cpt t ≠ cv ∨ βpt t ≠ βv)
    {a : ℕ} (θ : Fin a → k) (hθ : Function.Injective θ) (ha : n * (r + 1) < a) :
    ∃ s : Fin a,
      v.ord ((j + ∑ i : Fin n, algebraMap k F (θ s ^ (i.val + 1)) * β i)
          - algebraMap k F (cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i)) = 1 ∧
      ∀ t, pt t ≠ v →
        cpt t + ∑ i : Fin n, θ s ^ (i.val + 1) * βpt t i
          ≠ cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i := by
  classical

  let z : Fin (n + 1) → F :=
    Fin.cons (j - algebraMap k F cv) fun i => β i - algebraMap k F (βv i)
  let Z : Fin a → F := fun s => ∑ i : Fin (n + 1), θ s ^ (i : ℕ) • z i
  have hZ : ∀ s, (j + ∑ i : Fin n, algebraMap k F (θ s ^ (i.val + 1)) * β i)
      - algebraMap k F (cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i) = Z s := by
    intro s
    simp only [Z, z, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
      Fin.val_succ, Algebra.smul_def, map_pow, map_add, map_sum, map_mul, mul_sub,
      Finset.sum_sub_distrib, one_mul]
    ring

  have hz1 : ∀ i, z i ∈ mwALGN_ordGe v 1 := by
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [z, Fin.cons_zero, mwALGN_mem_ordGe_iff]
      exact Or.inr hcv
    · simp only [z, Fin.cons_succ, mwALGN_mem_ordGe_iff]
      rcases hβv i with h | h
      · exact Or.inl (by rw [h, sub_self])
      · exact Or.inr h
  have hZ1 : ∀ s, Z s ∈ mwALGN_ordGe v 1 := fun s =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hz1 i)
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, v.ord (z i₀) = 1 := by
    rcases hU1 with h | ⟨i, h⟩
    · exact ⟨0, by simpa [z] using h⟩
    · exact ⟨i.succ, by simpa [z] using h⟩
  have hi₀W : z i₀ ∉ mwALGN_ordGe v 2 := by
    rw [mwALGN_mem_ordGe_iff]
    rintro (h | h)
    · rw [h, ord_zero] at hi₀
      exact zero_ne_one hi₀
    · omega

  let B₀ : Finset (Fin a) := Finset.univ.filter fun s => Z s ∈ mwALGN_ordGe v 2
  have hB₀ : B₀.card ≤ n := by
    by_contra hlt
    obtain ⟨T, hTB, hTcard⟩ := Finset.exists_subset_card_eq (show n + 1 ≤ B₀.card by omega)
    let e : Fin (n + 1) ≃ T := (T.equivFinOfCardEq hTcard).symm
    have hθ' : Function.Injective (fun l => θ (e l)) :=
      hθ.comp (Subtype.val_injective.comp e.injective)
    have hall : ∀ l, (∑ i : Fin (n + 1), θ (e l) ^ (i : ℕ) • z i) ∈ mwALGN_ordGe v 2 := by
      intro l
      have hmem : ((e l : T) : Fin a) ∈ B₀ := hTB (e l).2
      exact (Finset.mem_filter.mp hmem).2
    exact hi₀W (mwALGN_mem_of_forall_sum_pow_smul_mem _ z _ hθ' hall i₀)

  let P : Fin r → Polynomial k := fun t =>
    C (cpt t - cv) + ∑ i : Fin n, C (βpt t i - βv i) * X ^ (i.val + 1)
  have hPeval : ∀ t s, (P t).eval (θ s)
      = (cpt t + ∑ i : Fin n, θ s ^ (i.val + 1) * βpt t i)
        - (cv + ∑ i : Fin n, θ s ^ (i.val + 1) * βv i) := by
    intro t s
    simp only [P, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    rw [Finset.sum_congr rfl fun (x : Fin n) _ =>
      show (βpt t x - βv x) * θ s ^ (x.val + 1)
        = θ s ^ (x.val + 1) * βpt t x - θ s ^ (x.val + 1) * βv x by ring,
      Finset.sum_sub_distrib]
    ring
  have hPdeg : ∀ t, (P t).degree < (n + 1 : ℕ) := by
    intro t
    refine (Polynomial.degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · exact (Polynomial.degree_C_le).trans_lt (by exact_mod_cast Nat.succ_pos n)
    · refine (Polynomial.degree_sum_le _ _).trans_lt ?_
      refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr fun i _ => ?_
      refine (Polynomial.degree_C_mul_X_pow_le _ _).trans_lt ?_
      exact_mod_cast Nat.succ_lt_succ i.2
  have hPne : ∀ t, pt t ≠ v → P t ≠ 0 := by
    intro t ht hP0
    rcases hS1 t ht with h | h
    · apply h
      have h0 := congrArg (fun p : Polynomial k => p.coeff 0) hP0
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_zero] at h0
      exact sub_eq_zero.mp (by simpa using h0)
    · apply h
      funext i
      have h0 := congrArg (fun p : Polynomial k => p.coeff (i.val + 1)) hP0
      simp only [P, Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.finsetSum_coeff,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_zero,
        Nat.succ_ne_zero, if_false, zero_add] at h0
      rw [Finset.sum_eq_single i (fun i' _ hne => by
          rw [if_neg (fun h' => hne (Fin.ext (by omega))), mul_zero])
        (fun h' => absurd (Finset.mem_univ i) h')] at h0
      simpa [sub_eq_zero] using h0
  let Bt : Fin r → Finset (Fin a) := fun t => Finset.univ.filter fun s => (P t).eval (θ s) = 0
  have hBt : ∀ t, pt t ≠ v → (Bt t).card ≤ n := by
    intro t ht
    by_contra hlt
    have hdeg : (P t).degree < (Bt t).card :=
      (hPdeg t).trans_le (by exact_mod_cast (show n + 1 ≤ (Bt t).card by omega))
    exact hPne t ht (Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (v := θ) (Bt t)
      hθ.injOn hdeg fun s hs => (Finset.mem_filter.mp hs).2)

  let bad : Finset (Fin a) :=
    B₀ ∪ (Finset.univ.filter fun t => pt t ≠ v).biUnion Bt
  have hbad : bad.card < (Finset.univ : Finset (Fin a)).card := by
    calc bad.card ≤ B₀.card + ((Finset.univ.filter fun t => pt t ≠ v).biUnion Bt).card :=
          Finset.card_union_le _ _
      _ ≤ n + (Finset.univ.filter fun t => pt t ≠ v).card * n := by
          refine add_le_add hB₀ (Finset.card_biUnion_le_card_mul _ _ _ fun t ht => ?_)
          exact hBt t (Finset.mem_filter.mp ht).2
      _ ≤ n + r * n := by
          gcongr
          exact (Finset.card_filter_le _ _).trans (by simp)
      _ = n * (r + 1) := by ring
      _ < a := ha
      _ = (Finset.univ : Finset (Fin a)).card := by simp
  obtain ⟨s, -, hs⟩ := Finset.exists_mem_notMem_of_card_lt_card hbad
  have hs₀ : Z s ∉ mwALGN_ordGe v 2 := fun h =>
    hs (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have hst : ∀ t, pt t ≠ v → (P t).eval (θ s) ≠ 0 := fun t ht h =>
    hs (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩))
  refine ⟨s, ?_, fun t ht => ?_⟩
  · rw [hZ]
    have h1 := hZ1 s
    rw [mwALGN_mem_ordGe_iff] at h1 hs₀
    push Not at hs₀
    rcases h1 with h | h
    · exact absurd h hs₀.1
    · have h2 := hs₀.2
      omega
  · have h := hst t ht
    rw [hPeval] at h
    exact sub_ne_zero.mp h

end S_AlgebraicCurve_Place_exists_uniformizing_separating_form
end P2MW
export P2MW.S_AlgebraicCurve_Place_exists_uniformizing_separating_form (solution)
