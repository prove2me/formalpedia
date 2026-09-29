-- Prove2me | solution 1 for ApproxMWM.Scaling.rescaling_approx_mwm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:59:49.163206+00:00
-- url     : https://prove2.me/submissions/47f1e854-f299-4633-a69f-eb5e940b0f35

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Matching

namespace ApproxMWM.Scaling

theorem aux_rs_card_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : Finset (Sym2 V)) (hM : IsMatching G M) : 2 * M.card ≤ Fintype.card V := by
  classical
  let t : Sym2 V → Finset V := fun e => Finset.univ.filter (fun v => v ∈ e)
  have h2 : ∀ e ∈ M, (t e).card = 2 := by
    intro e he
    have hG := hM.1 e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := hG
      have hne : a ≠ b := G.ne_of_adj hab
      have : t s(a, b) = {a, b} := by
        ext v
        simp [t]
      rw [this, Finset.card_pair hne]
  have hdisj : (M : Set (Sym2 V)).PairwiseDisjoint t := by
    intro e he f hf hef
    rw [Function.onFun, Finset.disjoint_left]
    intro v hve hvf
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hve hvf
    exact hef (hM.2 e he f hf v hve hvf)
  have hcard := Finset.card_biUnion hdisj
  have hle : (M.biUnion t).card ≤ Fintype.card V := Finset.card_le_univ _
  rw [Finset.sum_congr rfl h2] at hcard
  simp at hcard
  omega

theorem aux_rs_floor_le {V : Type*} [Fintype V] [DecidableEq V] (w : Sym2 V → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (S : Finset (Sym2 V)) :
    γ * weight (fun e => ((⌊w e / γ⌋ : ℤ) : ℝ)) S ≤ weight w S := by
  unfold weight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have h := Int.floor_le (w e / γ)
  calc γ * ((⌊w e / γ⌋ : ℤ) : ℝ) ≤ γ * (w e / γ) := mul_le_mul_of_nonneg_left h hγ.le
    _ = w e := by field_simp

theorem aux_rs_floor_ge {V : Type*} [Fintype V] [DecidableEq V] (w : Sym2 V → ℝ) (γ : ℝ)
    (hγ : 0 < γ) (S : Finset (Sym2 V)) :
    weight w S - γ * S.card ≤ γ * weight (fun e => ((⌊w e / γ⌋ : ℤ) : ℝ)) S := by
  unfold weight
  rw [Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro e _
  have h := Int.sub_one_lt_floor (w e / γ)
  have h' : γ * (w e / γ - 1) ≤ γ * ((⌊w e / γ⌋ : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_left h.le hγ.le
  have h'' : γ * (w e / γ - 1) = w e - γ * ((1 : ℕ) : ℝ) := by
    field_simp
    push_cast
    ring
  linarith

end ApproxMWM.Scaling

open ApproxMWM.Scaling

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε wmax : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hw_nonneg : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hwmax_ge : ∀ e ∈ G.edgeSet, w e ≤ wmax)
    (hwmax_att : ∃ e ∈ G.edgeSet, w e = wmax)
    (hwmax_pos : 0 < wmax)
    (M : Finset (Sym2 V))
    (hM : IsApproxMWM G (fun e => ((⌊w e / (ε * wmax / (Fintype.card V : ℝ))⌋ : ℤ) : ℝ))
      (1 - ε / 2) M) :
    IsMatching G M ∧ ∀ M' : Finset (Sym2 V), IsMatching G M' → (1 - ε) * weight w M' < weight w M := by
  refine ⟨hM.1, ?_⟩
  intro M' hM'
  obtain ⟨e0, he0, hwe0⟩ := hwmax_att
  have hcard2 : 1 < Fintype.card V := by
    induction e0 using Sym2.ind with
    | h a b =>
      have hab : G.Adj a b := he0
      exact Fintype.one_lt_card_iff.mpr ⟨a, b, G.ne_of_adj hab⟩
  have hn2 : (2 : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hcard2
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by linarith
  have hγ : 0 < ε * wmax / (Fintype.card V : ℝ) := by positivity
  have hγn : ε * wmax / (Fintype.card V : ℝ) * (Fintype.card V : ℝ) = ε * wmax := by
    field_simp
  have hγ2 : 2 * (ε * wmax / (Fintype.card V : ℝ)) ≤ ε * wmax := by nlinarith
  have h1 := hM.2 M' hM'
  have h2 := aux_rs_floor_le w _ hγ M
  have h3 := aux_rs_floor_ge w _ hγ M'
  have h4 : 2 * (M'.card : ℝ) ≤ (Fintype.card V : ℝ) := by
    exact_mod_cast aux_rs_card_le G M' hM'
  have h6 : 0 < 1 - ε / 2 := by linarith
  generalize ε * wmax / (Fintype.card V : ℝ) = γ at hγ hγn hγ2 h1 h2 h3 hM
  have h5 : γ * M'.card ≤ ε * wmax / 2 := by nlinarith
  have hA : (1 - ε / 2) * (weight w M' - ε * wmax / 2) ≤ weight w M := by
    calc (1 - ε / 2) * (weight w M' - ε * wmax / 2)
        ≤ (1 - ε / 2) * (γ * weight (fun e => ((⌊w e / γ⌋ : ℤ) : ℝ)) M') := by
          apply mul_le_mul_of_nonneg_left _ h6.le; linarith
      _ = γ * ((1 - ε / 2) * weight (fun e => ((⌊w e / γ⌋ : ℤ) : ℝ)) M') := by ring
      _ ≤ γ * weight (fun e => ((⌊w e / γ⌋ : ℤ) : ℝ)) M :=
          mul_le_mul_of_nonneg_left h1 hγ.le
      _ ≤ weight w M := h2
  by_cases hB : wmax ≤ weight w M'
  · have hBpos : 0 < weight w M' := lt_of_lt_of_le hwmax_pos hB
    have h7 : (1 - ε / 2) * (weight w M' - ε * weight w M' / 2)
        ≤ (1 - ε / 2) * (weight w M' - ε * wmax / 2) := by
      apply mul_le_mul_of_nonneg_left _ h6.le
      nlinarith
    nlinarith
  · push_neg at hB
    have hsing : IsMatching G {e0} := by
      refine ⟨?_, ?_⟩
      · intro e he
        rw [Finset.mem_singleton] at he
        rw [he]; exact he0
      · intro e he f hf _ _ _
        rw [Finset.mem_singleton] at he hf
        rw [he, hf]
    have h7 := hM.2 {e0} hsing
    have h8 := aux_rs_floor_ge w γ hγ {e0}
    simp only [weight, Finset.sum_singleton, Finset.card_singleton, Nat.cast_one,
      mul_one] at h7 h8
    rw [hwe0] at h7 h8
    have h9 : (1 - ε / 2) * (wmax - γ) ≤ weight w M := by
      calc (1 - ε / 2) * (wmax - γ)
          ≤ (1 - ε / 2) * (γ * ((⌊wmax / γ⌋ : ℤ) : ℝ)) :=
            mul_le_mul_of_nonneg_left h8 h6.le
        _ = γ * ((1 - ε / 2) * ((⌊wmax / γ⌋ : ℤ) : ℝ)) := by ring
        _ ≤ γ * weight (fun e => ((⌊w e / γ⌋ : ℤ) : ℝ)) M :=
            mul_le_mul_of_nonneg_left h7 hγ.le
        _ ≤ weight w M := h2
    have h10 : (1 - ε / 2) * (wmax - ε * wmax / 2) ≤ (1 - ε / 2) * (wmax - γ) := by
      apply mul_le_mul_of_nonneg_left _ h6.le
      linarith
    have h11 : (1 - ε) * weight w M' < (1 - ε) * wmax := by
      apply mul_lt_mul_of_pos_left hB; linarith
    nlinarith
