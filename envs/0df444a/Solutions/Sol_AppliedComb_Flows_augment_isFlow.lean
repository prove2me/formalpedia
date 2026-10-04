-- Prove2me | solution 1 for AppliedComb.Flows.augment_isFlow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T21:07:37.859339+00:00
-- url     : https://prove2.me/submissions/7ba1c8b7-797e-4b74-9254-e920413b2d47

import Mathlib
import Definitions.Def_AppliedComb_Flows_Network
import Definitions.Def_AppliedComb_Flows_AugmentingPath

set_option autoImplicit false

namespace AppliedComb.Flows.AugAux1e
open AppliedComb.Flows AppliedComb.Flows.Network

lemma tele : ∀ (m : ℕ) (f : Fin (m + 1) → ℝ),
    ∑ i : Fin m, (f i.castSucc - f i.succ) = f 0 - f (Fin.last m)
  | 0, f => by simp
  | m + 1, f => by
    rw [Fin.sum_univ_castSucc]
    have h := tele m (fun j => f j.castSucc)
    simp only [Fin.succ_castSucc] at h ⊢
    rw [h]
    simp

lemma sum_ite_unique {m : ℕ} (P : Fin m → Prop) [DecidablePred P] [Decidable (∃ i, P i)]
    (h : ∀ i j, P i → P j → i = j) :
    (∑ i, if P i then (1:ℝ) else 0) = if ∃ i, P i then 1 else 0 := by
  split_ifs with hex
  · obtain ⟨i, hi⟩ := hex
    rw [Finset.sum_eq_single i (fun j _ hj => if_neg (fun hpj => hj (h j i hpj hi))) (by simp)]
    simp [hi]
  · exact Finset.sum_eq_zero (fun j _ => if_neg (fun hpj => hex ⟨j, hpj⟩))

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical

noncomputable def D (N : Network V) {m : ℕ} (x : Fin (m + 1) → V) (a b : V) : ℝ :=
  (∑ i : Fin m, if N.adj a b ∧ a = x i.castSucc ∧ b = x i.succ then (1:ℝ) else 0) -
  (∑ i : Fin m, if N.adj a b ∧ a = x i.succ ∧ b = x i.castSucc then (1:ℝ) else 0)

lemma step_cases (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V)
    (hP : N.IsAugmentingPath ϕ x) (i : Fin m) :
    (N.adj (x i.castSucc) (x i.succ) ∧ ϕ (x i.castSucc) (x i.succ) < N.cap (x i.castSucc) (x i.succ)
      ∧ ¬ N.adj (x i.succ) (x i.castSucc)) ∨
    (N.adj (x i.succ) (x i.castSucc) ∧ 0 < ϕ (x i.succ) (x i.castSucc)
      ∧ ¬ N.adj (x i.castSucc) (x i.succ)) := by
  rcases hP.2.2.2 i with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, N.oriented _ _ h1⟩
  · exact Or.inr ⟨h1, h2, N.oriented _ _ h1⟩

lemma augment_eq (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V)
    (hP : N.IsAugmentingPath ϕ x) (δ : ℝ) (a b : V) :
    N.augment ϕ x δ a b = ϕ a b + δ * D N x a b := by
  classical
  have hinj := hP.1
  unfold augment D
  rw [sum_ite_unique _ (fun i j hi hj => by
        have := hinj (hi.2.1.symm.trans hj.2.1)
        exact Fin.castSucc_injective _ this),
      sum_ite_unique _ (fun i j hi hj => by
        have := hinj (hi.2.1.symm.trans hj.2.1)
        exact Fin.succ_injective _ this)]
  split_ifs with h1 h2 h3 h4 h5 <;> try ring
  all_goals first
    | (exfalso
       obtain ⟨i, -, hi1, hi2⟩ := h1
       obtain ⟨j, -, hj1, hj2⟩ := ‹∃ j : Fin m, N.adj a b ∧ a = x j.succ ∧ b = x j.castSucc›
       have e1 := hinj (hi1.symm.trans hj1)
       have e2 := hinj (hi2.symm.trans hj2)
       have := congrArg Fin.val e1
       have := congrArg Fin.val e2
       simp at *
       omega)
    | (exfalso; tauto)

lemma sum_out_single (N : Network V) (v p q : V) :
    (∑ b, if N.adj v b ∧ v = p ∧ b = q then (1:ℝ) else 0) = if N.adj p q ∧ v = p then 1 else 0 := by
  rw [Finset.sum_eq_single q (fun b _ hb => if_neg (fun h => hb h.2.2)) (by simp)]
  by_cases hv : v = p
  · subst hv; simp
  · simp [hv]

lemma sum_in_single (N : Network V) (v p q : V) :
    (∑ a, if N.adj a v ∧ a = p ∧ v = q then (1:ℝ) else 0) = if N.adj p q ∧ v = q then 1 else 0 := by
  rw [Finset.sum_eq_single p (fun b _ hb => if_neg (fun h => hb h.2.1)) (by simp)]
  by_cases hv : v = q
  · subst hv; simp
  · simp [hv]

lemma net_D (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V)
    (hP : N.IsAugmentingPath ϕ x) (v : V) :
    (∑ b, D N x v b) - (∑ a, D N x a v) =
      (if v = x 0 then (1:ℝ) else 0) - (if v = x (Fin.last m) then 1 else 0) := by
  classical
  have e1 : (∑ b, ∑ i : Fin m, if N.adj v b ∧ v = x i.castSucc ∧ b = x i.succ then (1:ℝ) else 0)
      = ∑ i : Fin m, if N.adj (x i.castSucc) (x i.succ) ∧ v = x i.castSucc then (1:ℝ) else 0 := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => sum_out_single N v _ _
  have e2 : (∑ b, ∑ i : Fin m, if N.adj v b ∧ v = x i.succ ∧ b = x i.castSucc then (1:ℝ) else 0)
      = ∑ i : Fin m, if N.adj (x i.succ) (x i.castSucc) ∧ v = x i.succ then (1:ℝ) else 0 := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => sum_out_single N v _ _
  have e3 : (∑ a, ∑ i : Fin m, if N.adj a v ∧ a = x i.castSucc ∧ v = x i.succ then (1:ℝ) else 0)
      = ∑ i : Fin m, if N.adj (x i.castSucc) (x i.succ) ∧ v = x i.succ then (1:ℝ) else 0 := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => sum_in_single N v _ _
  have e4 : (∑ a, ∑ i : Fin m, if N.adj a v ∧ a = x i.succ ∧ v = x i.castSucc then (1:ℝ) else 0)
      = ∑ i : Fin m, if N.adj (x i.succ) (x i.castSucc) ∧ v = x i.castSucc then (1:ℝ) else 0 := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => sum_in_single N v _ _
  unfold D
  simp only [Finset.sum_sub_distrib]
  rw [e1, e2, e3, e4]
  rw [← tele m (fun j => if v = x j then (1:ℝ) else 0)]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases step_cases N ϕ x hP i with ⟨hF, -, hB⟩ | ⟨hB, -, hF⟩
  · simp only [hF, hB, true_and, false_and, if_false]
    ring
  · simp only [hF, hB, true_and, false_and, if_false]
    ring

lemma delta_bounds (N : Network V) (ϕ : V → V → ℝ) {m : ℕ} (x : Fin (m + 1) → V)
    (hP : N.IsAugmentingPath ϕ x) (δ : ℝ) (hδ : N.delta ϕ x = (δ : WithTop ℝ)) :
    0 ≤ δ ∧
    (∀ i : Fin m, N.adj (x i.castSucc) (x i.succ) →
      δ ≤ N.cap (x i.castSucc) (x i.succ) - ϕ (x i.castSucc) (x i.succ)) ∧
    (∀ i : Fin m, N.adj (x i.succ) (x i.castSucc) → δ ≤ ϕ (x i.succ) (x i.castSucc)) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · have h0 : (0 : WithTop ℝ) ≤ N.delta ϕ x := by
      unfold delta delta1 delta2
      refine le_min (Finset.le_inf fun i hi => ?_) (Finset.le_inf fun i hi => ?_)
      · have hF : N.IsForward x i := (Finset.mem_filter.mp hi).2
        rcases step_cases N ϕ x hP i with ⟨-, hlt, -⟩ | ⟨-, -, hnF⟩
        · exact_mod_cast (sub_nonneg.mpr hlt.le)
        · exact absurd hF hnF
      · have hB : N.IsBackward x i := (Finset.mem_filter.mp hi).2
        rcases step_cases N ϕ x hP i with ⟨-, -, hnB⟩ | ⟨-, hpos, -⟩
        · exact absurd hB hnB
        · exact_mod_cast hpos.le
    rw [hδ] at h0
    exact_mod_cast h0
  · intro i hi
    have h : N.delta ϕ x ≤ ((N.cap (x i.castSucc) (x i.succ) - ϕ (x i.castSucc) (x i.succ) : ℝ) :
        WithTop ℝ) := by
      unfold delta delta1
      exact (min_le_left _ _).trans
        (Finset.inf_le (f := fun i : Fin m => ((N.cap (x i.castSucc) (x i.succ)
          - ϕ (x i.castSucc) (x i.succ) : ℝ) : WithTop ℝ))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    rw [hδ] at h
    exact_mod_cast h
  · intro i hi
    have h : N.delta ϕ x ≤ ((ϕ (x i.succ) (x i.castSucc) : ℝ) : WithTop ℝ) := by
      unfold delta delta2
      exact (min_le_right _ _).trans
        (Finset.inf_le (f := fun i : Fin m => ((ϕ (x i.succ) (x i.castSucc) : ℝ) : WithTop ℝ))
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
    rw [hδ] at h
    exact_mod_cast h

end AppliedComb.Flows.AugAux1e

open AppliedComb.Flows in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (N : Network V) (ϕ : V → V → ℝ) (hϕ : N.IsFlow ϕ)
    {m : ℕ} (x : Fin (m + 1) → V) (hP : N.IsAugmentingPath ϕ x)
    (δ : ℝ) (hδ : N.delta ϕ x = (δ : WithTop ℝ)) :
    N.IsFlow (N.augment ϕ x δ) ∧ N.value (N.augment ϕ x δ) = N.value ϕ + δ := by
  classical
  obtain ⟨hcap, hzero, hST, hcons⟩ := hϕ
  obtain ⟨hδ0, hfwd, hbwd⟩ := AugAux1e.delta_bounds N ϕ x hP δ hδ
  have heq := AugAux1e.augment_eq N ϕ x hP δ
  have hx0 : x 0 = N.S := hP.2.1
  have hxl : x (Fin.last m) = N.T := hP.2.2.1
  have hST' := N.source_ne_sink
  -- D vanishes off edges
  have hDz : ∀ a b, ¬ N.adj a b → AugAux1e.D N x a b = 0 := by
    intro a b hab
    unfold AugAux1e.D
    simp [hab]
  -- D values on edges
  have hDv : ∀ a b, N.adj a b → (AugAux1e.D N x a b = 0 ∨ AugAux1e.D N x a b = 1 ∨ AugAux1e.D N x a b = -1) ∧
      (AugAux1e.D N x a b = 1 → ϕ a b + δ ≤ N.cap a b) ∧ (AugAux1e.D N x a b = -1 → 0 ≤ ϕ a b - δ) := by
    intro a b hab
    have h := heq a b
    unfold Network.augment at h
    split_ifs at h with h1 h2
    · obtain ⟨i, -, rfl, rfl⟩ := h1
      have hD : AugAux1e.D N x (x i.castSucc) (x i.succ) = 1 := by
        rcases eq_or_ne δ 0 with h0 | h0
        · -- fall back to the explicit computation
          unfold AugAux1e.D
          rw [AugAux1e.sum_ite_unique _ (fun i j hi hj => Fin.castSucc_injective _ (hP.1 (hi.2.1.symm.trans hj.2.1))),
            AugAux1e.sum_ite_unique _ (fun i j hi hj => Fin.succ_injective _ (hP.1 (hi.2.1.symm.trans hj.2.1)))]
          rw [if_pos ⟨i, hab, rfl, rfl⟩]
          rw [if_neg]
          · ring
          · rintro ⟨j, -, hj1, hj2⟩
            have e1 := congrArg Fin.val (hP.1 hj1)
            have e2 := congrArg Fin.val (hP.1 hj2)
            simp at e1 e2
            omega
        · have : δ * AugAux1e.D N x (x i.castSucc) (x i.succ) = δ * 1 := by linarith
          exact mul_left_cancel₀ h0 this
      refine ⟨Or.inr (Or.inl hD), fun _ => ?_, fun h' => by rw [hD] at h'; norm_num at h'⟩
      have := hfwd i hab
      linarith
    · obtain ⟨i, -, rfl, rfl⟩ := h2
      have hD : AugAux1e.D N x (x i.succ) (x i.castSucc) = -1 := by
        unfold AugAux1e.D
        rw [AugAux1e.sum_ite_unique _ (fun i j hi hj => Fin.castSucc_injective _ (hP.1 (hi.2.1.symm.trans hj.2.1))),
          AugAux1e.sum_ite_unique _ (fun i j hi hj => Fin.succ_injective _ (hP.1 (hi.2.1.symm.trans hj.2.1)))]
        rw [if_neg h1, if_pos ⟨i, hab, rfl, rfl⟩]
        ring
      refine ⟨Or.inr (Or.inr hD), fun h' => by rw [hD] at h'; norm_num at h', fun _ => ?_⟩
      have := hbwd i hab
      linarith
    · have hD : AugAux1e.D N x a b = 0 := by
        unfold AugAux1e.D
        rw [AugAux1e.sum_ite_unique _ (fun i j hi hj => Fin.castSucc_injective _ (hP.1 (hi.2.1.symm.trans hj.2.1))),
          AugAux1e.sum_ite_unique _ (fun i j hi hj => Fin.succ_injective _ (hP.1 (hi.2.1.symm.trans hj.2.1)))]
        rw [if_neg h1, if_neg h2]
        ring
      exact ⟨Or.inl hD, fun h' => by rw [hD] at h'; norm_num at h',
        fun h' => by rw [hD] at h'; norm_num at h'⟩
  have hsumL : ∀ y, ∑ a, N.augment ϕ x δ a y = ∑ a, ϕ a y + δ * ∑ a, AugAux1e.D N x a y := by
    intro y; simp only [heq, Finset.sum_add_distrib, Finset.mul_sum]
  have hsumR : ∀ y, ∑ b, N.augment ϕ x δ y b = ∑ b, ϕ y b + δ * ∑ b, AugAux1e.D N x y b := by
    intro y; simp only [heq, Finset.sum_add_distrib, Finset.mul_sum]
  have hinS : ∑ a, AugAux1e.D N x a N.S = 0 :=
    Finset.sum_eq_zero fun a _ => hDz a N.S (N.no_edge_into_source a)
  have houtT : ∑ b, AugAux1e.D N x N.T b = 0 :=
    Finset.sum_eq_zero fun b _ => hDz N.T b (N.no_edge_out_of_sink b)
  have hnS := AugAux1e.net_D N ϕ x hP N.S
  have hnT := AugAux1e.net_D N ϕ x hP N.T
  rw [hx0, hxl] at hnS hnT
  simp only [if_true, eq_self_iff_true, if_neg hST', if_neg hST'.symm, hinS, houtT] at hnS hnT
  have hvalue : N.value (N.augment ϕ x δ) = N.value ϕ + δ := by
    unfold Network.value
    rw [hsumR]
    have : ∑ b, AugAux1e.D N x N.S b = 1 := by linarith
    rw [this]; ring
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hvalue⟩
  · intro a b hab
    obtain ⟨h0, h0'⟩ := hcap a b hab
    obtain ⟨hcase, hup, hdown⟩ := hDv a b hab
    rw [heq]
    rcases hcase with h | h | h
    · rw [h]; constructor <;> linarith
    · have := hup h; rw [h]; constructor <;> linarith
    · have := hdown h; rw [h]; constructor <;> linarith
  · intro a b hab
    rw [heq, hzero a b hab, hDz a b hab]; ring
  · rw [hsumR, hsumL]
    have : ∑ a, AugAux1e.D N x a N.T = 1 := by linarith
    rw [this, ← hST]
    have : ∑ b, AugAux1e.D N x N.S b = 1 := by linarith
    rw [this]
  · intro y hyS hyT
    rw [hsumR, hsumL, hcons y hyS hyT]
    have hn := AugAux1e.net_D N ϕ x hP y
    rw [hx0, hxl, if_neg hyS, if_neg hyT] at hn
    have : ∑ a, AugAux1e.D N x a y = ∑ b, AugAux1e.D N x y b := by linarith
    rw [this]
