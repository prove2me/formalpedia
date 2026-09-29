-- Prove2me | solution 1 for ApproxMWM.Scaling.approx_slackness_approx_mwm
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:59:33.728187+00:00
-- url     : https://prove2.me/submissions/bb7f7d98-a82d-4a24-8c4f-b48ab3f8c175

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Matching

namespace ApproxMWM.Scaling

open Finset

lemma aux_amwm_lift {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (e : Sym2 V) (he : ¬ e.IsDiag) :
    Sym2.lift ⟨fun u v => f u + f v, fun u v => add_comm (f u) (f v)⟩ e
      = ∑ v, if v ∈ e then f v else 0 := by
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using he
    simp only [Sym2.lift_mk, Sym2.mem_iff]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    have : (univ.filter fun v => v = a ∨ v = b) = {a, b} := by
      ext v; simp
    rw [this, Finset.sum_pair hab]

lemma aux_amwm_sum_incid {V : Type*} [Fintype V] [DecidableEq V] (f : V → ℝ)
    (S : Finset (Sym2 V)) :
    ∑ e ∈ S, (∑ v, if v ∈ e then f v else 0)
      = ∑ v, f v * ((S.filter (fun e => v ∈ e)).card : ℝ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

lemma aux_amwm_zsum {V : Type*} [Fintype V] [DecidableEq V] (z : Finset V → ℝ)
    (S : Finset (Sym2 V)) :
    ∑ e ∈ S, ∑ B ∈ (univ : Finset (Finset V)).filter (fun B => Odd B.card ∧ e ∈ B.sym2), z B
      = ∑ B : Finset V,
          if Odd B.card then z B * ((S.filter (fun e => e ∈ B.sym2)).card : ℝ) else 0 := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun B _ => ?_)
  split_ifs with hB
  · simp only [hB, true_and]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  · simp [hB]

lemma aux_amwm_card_le_one {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : Finset (Sym2 V)} (hM : IsMatching G M) (v : V) :
    (M.filter (fun e => v ∈ e)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter] at ha hb
  exact hM.2 a ha.1 b hb.1 v ha.2 hb.2

lemma aux_amwm_yzsum {V : Type*} [Fintype V] [DecidableEq V] (y : V → ℝ) (z : Finset V → ℝ)
    (S : Finset (Sym2 V)) (hS : ∀ e ∈ S, ¬ e.IsDiag) :
    ∑ e ∈ S, yz y z e
      = ∑ v, y v * ((S.filter (fun e => v ∈ e)).card : ℝ)
        + ∑ B : Finset V,
          if Odd B.card then z B * ((S.filter (fun e => e ∈ B.sym2)).card : ℝ) else 0 := by
  unfold yz
  rw [Finset.sum_add_distrib, aux_amwm_zsum, ← aux_amwm_sum_incid]
  congr 1
  exact Finset.sum_congr rfl (fun e he => aux_amwm_lift y e (hS e he))

lemma aux_amwm_two_mul_le {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : Finset (Sym2 V)} (hM : IsMatching G M) (B : Finset V) :
    2 * (M.filter (fun e => e ∈ B.sym2)).card ≤ B.card := by
  set T := M.filter (fun e => e ∈ B.sym2) with hT
  have h1 : ∀ e ∈ T, (B.filter (fun v => v ∈ e)).card = 2 := by
    intro e he
    rw [hT, Finset.mem_filter] at he
    have hnd : ¬ e.IsDiag := G.not_isDiag_of_mem_edgeSet (hM.1 e he.1)
    have hB := he.2
    induction e using Sym2.ind with
    | h a b =>
      have hab : a ≠ b := by simpa using hnd
      rw [Finset.mk_mem_sym2_iff] at hB
      have : (B.filter fun v => v ∈ s(a, b)) = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl)
          · exact ⟨hB.1, Or.inl rfl⟩
          · exact ⟨hB.2, Or.inr rfl⟩
      rw [this, Finset.card_pair hab]
  have h2 : ∀ v ∈ B, (T.filter (fun e => v ∈ e)).card ≤ 1 := by
    intro v _
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [hT, Finset.mem_filter] at ha hb
    exact hM.2 a ha.1.1 b hb.1.1 v ha.2 hb.2
  calc 2 * T.card = ∑ e ∈ T, (B.filter (fun v => v ∈ e)).card := by
        rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_comm]
    _ = ∑ v ∈ B, (T.filter (fun e => v ∈ e)).card := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
    _ ≤ ∑ v ∈ B, 1 := Finset.sum_le_sum h2
    _ = B.card := by simp

lemma aux_amwm_EB_sub {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : Finset (Sym2 V)} {Ω : Finset (Finset V)} {EB : Finset V → Finset (Sym2 V)}
    (hΩ : IsBlossomFamily G M Ω EB) :
    ∀ n : ℕ, ∀ B ∈ Ω, B.card ≤ n → EB B ⊆ B.sym2 := by
  intro n
  induction n with
  | zero =>
    intro B hB hc
    have := hΩ.2.2 B hB
    omega
  | succ n ih =>
    intro B hB hc
    obtain ⟨ℓ, A, a, b, _hev, hℓ, _hch, hdisj, hab, hBeq, hEB⟩ := hΩ.1 B hB
    have hsub : ∀ i, A i ⊆ B := by
      intro i
      rw [hBeq]
      exact Finset.subset_biUnion_of_mem A (Finset.mem_univ i)
    intro e he
    rw [hEB, Finset.mem_union, Finset.mem_biUnion] at he
    rcases he with ⟨i, _, hei⟩ | he
    · unfold childEB at hei
      split_ifs at hei with hAi
      · have hne : i ≠ i + 1 := by
          intro h
          have h' : (i : Fin (ℓ + 1)).val = (i + 1 : Fin (ℓ + 1)).val := congrArg Fin.val h
          rw [Fin.val_add] at h'
          have h1 : ((1 : Fin (ℓ + 1)) : ℕ) = 1 := by
            rw [Fin.val_one']
            exact Nat.mod_eq_of_lt (by omega)
          rw [h1] at h'
          have hi := i.isLt
          by_cases hlt : i.val + 1 < ℓ + 1
          · rw [Nat.mod_eq_of_lt hlt] at h'
            omega
          · have : i.val + 1 = ℓ + 1 := by omega
            rw [this, Nat.mod_self] at h'
            omega
        have hbi : b i ∈ A (i + 1) := (hab i).2.1
        have hbnot : b i ∉ A i := by
          intro h
          exact Finset.disjoint_left.mp (hdisj i (i + 1) hne) h hbi
        have hss : A i ⊂ B := by
          rw [Finset.ssubset_iff_of_subset (hsub i)]
          exact ⟨b i, hsub (i + 1) hbi, hbnot⟩
        have hcard : (A i).card ≤ n := by
          have := Finset.card_lt_card hss
          omega
        exact Finset.sym2_mono (hsub i) (ih (A i) hAi hcard hei)
      · simp at hei
    · rw [Finset.mem_image] at he
      obtain ⟨i, _, rfl⟩ := he
      rw [Finset.mk_mem_sym2_iff]
      exact ⟨hsub i (hab i).1, hsub (i + 1) (hab i).2.1⟩

end ApproxMWM.Scaling

open ApproxMWM.Scaling

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (M : Finset (Sym2 V)) (Ω : Finset (Finset V))
    (EB : Finset V → Finset (Sym2 V)) (y : V → ℝ) (z : Finset V → ℝ) (ε₀ ε₁ : ℝ)
    (hε₁ : -1 < ε₁)
    (hM : IsMatching G M) (hΩ : IsBlossomFamily G M Ω EB)
    (hz_nonneg : ∀ B : Finset V, Odd B.card → 0 ≤ z B)
    (hy_nonneg : ∀ u : V, 0 ≤ y u)
    (hy_matched : ∀ u : V, 0 < y u → IsMatched M u)
    (hz_active : ∀ B : Finset V, Odd B.card → 0 < z B → B ∈ Ω)
    (hz_root : ∀ B : Finset V, IsRoot Ω B → 0 < z B)
    (hdom : ∀ e ∈ G.edgeSet, (1 - ε₀) * w e ≤ yz y z e)
    (htight : ∀ e ∈ G.edgeSet, (e ∈ M ∨ ∃ B ∈ Ω, e ∈ EB B) → yz y z e ≤ (1 + ε₁) * w e)
    (hfree : ∀ u : V, IsFree M u → y u = 0) :
    IsApproxMWM G w ((1 + ε₁)⁻¹ * (1 - ε₀)) M := by
  refine ⟨hM, fun M' hM' => ?_⟩
  have hpos : 0 < 1 + ε₁ := by linarith
  -- lower bound for M'
  have hlow : (1 - ε₀) * weight w M' ≤ ∑ e ∈ M', yz y z e := by
    unfold weight
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e he => hdom e (hM'.1 e he))
  -- upper bound for M
  have hup : ∑ e ∈ M, yz y z e ≤ (1 + ε₁) * weight w M := by
    unfold weight
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e he => htight e (hM.1 e he) (Or.inl he))
  -- comparison
  have hmid : ∑ e ∈ M', yz y z e ≤ ∑ e ∈ M, yz y z e := by
    rw [aux_amwm_yzsum y z M' (fun e he => G.not_isDiag_of_mem_edgeSet (hM'.1 e he)),
      aux_amwm_yzsum y z M (fun e he => G.not_isDiag_of_mem_edgeSet (hM.1 e he))]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro v _
      rcases (hy_nonneg v).lt_or_eq with hv | hv
      · have h1 : (M.filter (fun e => v ∈ e)).card = 1 := by
          have hle := aux_amwm_card_le_one hM v
          obtain ⟨e, he, hve⟩ := hy_matched v hv
          have : 0 < (M.filter (fun e => v ∈ e)).card :=
            Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩⟩
          omega
        have h2 : ((M'.filter (fun e => v ∈ e)).card : ℝ) ≤ 1 := by
          exact_mod_cast aux_amwm_card_le_one hM' v
        rw [h1, Nat.cast_one]
        exact mul_le_mul_of_nonneg_left h2 hv.le
      · rw [← hv]; simp
    · apply Finset.sum_le_sum
      intro B _
      split_ifs with hodd
      · rcases (hz_nonneg B hodd).lt_or_eq with hzB | hzB
        · have hBΩ := hz_active B hodd hzB
          have hfull := hΩ.2.2 B hBΩ
          have hsub : M ∩ EB B ⊆ M.filter (fun e => e ∈ B.sym2) := by
            intro e he
            rw [Finset.mem_inter] at he
            exact Finset.mem_filter.mpr ⟨he.1, aux_amwm_EB_sub hΩ B.card B hBΩ le_rfl he.2⟩
          have hc1 := Finset.card_le_card hsub
          have hc2 := aux_amwm_two_mul_le hM' B
          have hk : (M'.filter (fun e => e ∈ B.sym2)).card
              ≤ (M.filter (fun e => e ∈ B.sym2)).card := by omega
          have hk' : ((M'.filter (fun e => e ∈ B.sym2)).card : ℝ)
              ≤ ((M.filter (fun e => e ∈ B.sym2)).card : ℝ) := by exact_mod_cast hk
          exact mul_le_mul_of_nonneg_left hk' hzB.le
        · rw [← hzB]; simp
      · exact le_rfl
  have key : (1 - ε₀) * weight w M' ≤ (1 + ε₁) * weight w M := by linarith
  calc (1 + ε₁)⁻¹ * (1 - ε₀) * weight w M'
      = (1 + ε₁)⁻¹ * ((1 - ε₀) * weight w M') := by ring
    _ ≤ (1 + ε₁)⁻¹ * ((1 + ε₁) * weight w M) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hpos.le)
    _ = weight w M := by rw [inv_mul_cancel_left₀ hpos.ne']
