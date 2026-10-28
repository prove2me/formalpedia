-- Prove2me | solution 1 for AdWordsMSVV.LowerBound.theorem_9
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T12:34:20.49435+00:00
-- url     : https://prove2.me/submissions/db2fb54d-742e-47e7-b8e6-c7a987f11349

import Mathlib
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

set_option autoImplicit false

namespace AdWordsMSVV.LowerBound.KVVAux

open AdWordsMSVV.LowerBound Finset

theorem winner_spec {N M B : ℕ} {I : Instance N M} {a : DetAlg N M} {t : Fin M} {r : Fin N}
    (h : winner B I a t = some r) : r ∈ I t ∧ load B I a t.val r < B := by
  unfold winner at h
  cases hx : a t (reveal I t) with
  | none => rw [hx] at h; cases h
  | some r' =>
    rw [hx] at h
    simp only at h
    by_cases h1 : r' ∈ I t ∧ load B I a t.val r' < B
    · rw [if_pos h1] at h
      cases h
      exact h1
    · rw [if_neg h1] at h
      cases h

theorem load_succ {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (n : ℕ) (hn : n < M)
    (r : Fin N) :
    load B I a (n + 1) r = load B I a n r + (if winner B I a ⟨n, hn⟩ = some r then 1 else 0) := by
  rw [load]
  simp only [dif_pos hn]
  unfold winner
  cases hx : a ⟨n, hn⟩ (reveal I ⟨n, hn⟩) with
  | none => simp
  | some r' =>
    simp only
    by_cases h1 : r' ∈ I ⟨n, hn⟩ ∧ load B I a n r' < B
    · simp only [if_pos h1]
      by_cases hr : r = r'
      · subst hr; simp
      · simp [hr, Ne.symm hr]
    · simp only [if_neg h1]; simp

theorem load_stop {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (n : ℕ) (hn : ¬ n < M) :
    load B I a (n + 1) = load B I a n := by
  rw [load]
  simp only [dif_neg hn]

theorem load_le {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) :
    ∀ n r, load B I a n r ≤ B := by
  intro n
  induction n with
  | zero => intro r; rw [load]; exact Nat.zero_le _
  | succ n ih =>
    intro r
    by_cases hn : n < M
    · rw [load_succ B I a n hn r]
      split_ifs with hw
      · have := (winner_spec hw).2
        simp only at this
        omega
      · simpa using ih r
    · rw [load_stop B I a n hn]; exact ih r

theorem load_eq_sum {N M : ℕ} (B : ℕ) (I : Instance N M) (a : DetAlg N M) (r : Fin N) :
    ∀ n, load B I a n r = ∑ t : Fin M, if t.val < n ∧ winner B I a t = some r then 1 else 0 := by
  intro n
  induction n with
  | zero => rw [load]; simp
  | succ n ih =>
    by_cases hn : n < M
    · rw [load_succ B I a n hn r, ih]
      have key : ∀ t : Fin M, (if t.val < n + 1 ∧ winner B I a t = some r then 1 else 0) =
          (if t.val < n ∧ winner B I a t = some r then 1 else 0) +
          (if t = ⟨n, hn⟩ then (if winner B I a ⟨n, hn⟩ = some r then 1 else 0) else 0) := by
        intro t
        by_cases ht : t = ⟨n, hn⟩
        · subst ht; simp
        · have hne : t.val ≠ n := fun h => ht (Fin.ext h)
          have e : t.val < n + 1 ↔ t.val < n := by omega
          simp [e, ht]
      rw [Finset.sum_congr rfl (fun t _ => key t), Finset.sum_add_distrib]
      simp
    · rw [load_stop B I a n hn, ih]
      apply Finset.sum_congr rfl
      intro t _
      have := t.isLt
      have e : t.val < n + 1 ↔ t.val < n := by omega
      simp only [e]

theorem reveal_congr {N M : ℕ} {I I' : Instance N M} {u : Fin M}
    (h : ∀ s : Fin M, s ≤ u → I s = I' s) : reveal I u = reveal I' u := by
  funext j
  unfold reveal
  split_ifs with hj
  · rw [h j hj]
  · rfl

theorem load_congr {N M : ℕ} (B : ℕ) {I I' : Instance N M} (a : DetAlg N M) {u : Fin M}
    (h : ∀ s : Fin M, s ≤ u → I s = I' s) : ∀ n, n ≤ u.val → load B I a n = load B I' a n := by
  intro n
  induction n with
  | zero => intro _; rw [load, load]
  | succ n ih =>
    intro hn
    have hnM : n < M := by have := u.isLt; omega
    have hle : (⟨n, hnM⟩ : Fin M) ≤ u := by
      rw [Fin.le_def]; simp only; omega
    have h2 : ∀ s : Fin M, s ≤ ⟨n, hnM⟩ → I s = I' s := fun s hs => h s (le_trans hs hle)
    rw [load, load]
    simp only [dif_pos hnM]
    rw [ih (by omega), reveal_congr h2, h ⟨n, hnM⟩ hle]

theorem winner_congr {N M : ℕ} (B : ℕ) {I I' : Instance N M} (a : DetAlg N M) {t : Fin M}
    (h : ∀ s : Fin M, s ≤ t → I s = I' s) : winner B I a t = winner B I' a t := by
  unfold winner
  rw [reveal_congr h, h t le_rfl, load_congr B a h t.val le_rfl]

theorem mem_round {N B : ℕ} (π : Equiv.Perm (Fin N)) (t : Fin (N * B)) (r : Fin N) :
    r ∈ roundInstance N B π t ↔ t.val / B ≤ (π.symm r).val := by
  simp [roundInstance]

theorem round_swap {N B : ℕ} (π : Equiv.Perm (Fin N)) (j j' : Fin N) (s : Fin (N * B))
    (hj : s.val / B ≤ j.val) (hj' : s.val / B ≤ j'.val) :
    roundInstance N B (π * Equiv.swap j j') s = roundInstance N B π s := by
  ext r
  rw [mem_round, mem_round]
  have e : (π * Equiv.swap j j').symm r = Equiv.swap j j' (π.symm r) := by
    rw [Equiv.Perm.mul_def, Equiv.symm_trans_apply, Equiv.symm_swap]
  rw [e]
  generalize π.symm r = k
  by_cases h1 : k = j
  · subst h1; rw [Equiv.swap_apply_left]; constructor <;> intro <;> omega
  · by_cases h2 : k = j'
    · subst h2; rw [Equiv.swap_apply_right]; constructor <;> intro <;> omega
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]

theorem swap_count {N B : ℕ} (a : DetAlg N (N * B)) (t : Fin (N * B)) (j j' : Fin N)
    (hj : t.val / B ≤ j.val) (hj' : t.val / B ≤ j'.val) :
    (∑ π : Equiv.Perm (Fin N),
        if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0) =
      ∑ π : Equiv.Perm (Fin N),
        if winner B (roundInstance N B π) a t = some (π j') then (1 : ℝ) else 0 := by
  rw [← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j j'))
    (fun π => if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro π _
  have hw : winner B (roundInstance N B (π * Equiv.swap j j')) a t =
      winner B (roundInstance N B π) a t := by
    apply winner_congr
    intro s hs
    have : s.val / B ≤ t.val / B := Nat.div_le_div_right (Fin.le_def.mp hs)
    exact round_swap π j j' s (le_trans this hj) (le_trans this hj')
  simp only [Equiv.coe_mulRight]
  simp only [hw, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem sum_j_le_one {N : ℕ} (π : Equiv.Perm (Fin N)) (o : Option (Fin N)) :
    (∑ j : Fin N, if o = some (π j) then (1 : ℝ) else 0) ≤ 1 := by
  cases o with
  | none => simp
  | some r =>
    have e : ∀ j, (some r = some (π j)) ↔ (j = π.symm r) := by
      intro j
      rw [Option.some.injEq, Equiv.eq_symm_apply, eq_comm]
    simp_rw [e]
    simp

theorem cnt (n i J : ℕ) (c : ℝ) :
    ∑ k ∈ range n, (if i ≤ k ∧ k < J then c else 0) = ((min n J - i : ℕ) : ℝ) * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have e : (min (n + 1) J - i) = (min n J - i) + (if i ≤ n ∧ n < J then 1 else 0) := by
      split_ifs <;> omega
    rw [e]
    push_cast
    split_ifs <;> ring

theorem block_sum {N B : ℕ} (g : ℕ → ℝ) :
    ∑ t : Fin (N * B), g (t.val / B) = B * ∑ i ∈ range N, g i := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB; simp
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have e : ∀ (i : Fin N) (s : Fin B), (finProdFinEquiv (i, s)).val / B = i.val := by
    intro i s
    rw [finProdFinEquiv_apply_val]
    simp only
    rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt s.isLt, zero_add]
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => (B : ℝ) * g i) N, Finset.mul_sum]

theorem perm_sum_bound (N B J : ℕ) (hJ : J ≤ N) (a : DetAlg N (N * B)) :
    (∑ π : Equiv.Perm (Fin N), (revenue B (roundInstance N B π) a : ℝ)) ≤
      (N.factorial : ℝ) * B *
        (((N - J : ℕ) : ℝ) + ∑ i ∈ range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)) := by
  set K : ℝ := (N.factorial : ℝ) with hK
  have hcard : ∑ _π : Equiv.Perm (Fin N), (1 : ℝ) = K := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]; simp [hK]
  let c : Fin (N * B) → Fin N → ℝ := fun t j => ∑ π : Equiv.Perm (Fin N),
    if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0
  have hrev : ∀ π : Equiv.Perm (Fin N), (revenue B (roundInstance N B π) a : ℝ) =
      ∑ j : Fin N, (load B (roundInstance N B π) a (N * B) (π j) : ℝ) := by
    intro π
    unfold revenue
    push_cast
    exact (Equiv.sum_comp π (fun r => (load B (roundInstance N B π) a (N * B) r : ℝ))).symm
  have hload : ∀ (π : Equiv.Perm (Fin N)) (j : Fin N),
      (load B (roundInstance N B π) a (N * B) (π j) : ℝ) =
        ∑ t : Fin (N * B), if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0 := by
    intro π j
    rw [load_eq_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro t _
    simp [t.isLt]
  have hj : ∀ j : Fin N, ∑ π : Equiv.Perm (Fin N), (load B (roundInstance N B π) a (N * B) (π j) : ℝ)
      ≤ if j.val < J then ∑ t, c t j else K * B := by
    intro j
    split_ifs
    · rw [Finset.sum_congr rfl (fun π _ => hload π j), Finset.sum_comm]
    · calc _ ≤ ∑ _π : Equiv.Perm (Fin N), (B : ℝ) * 1 :=
            Finset.sum_le_sum (fun π _ => by
              rw [mul_one]; exact_mod_cast load_le B _ a _ _)
        _ = K * B := by rw [← Finset.mul_sum, hcard, mul_comm]
  have ht : ∀ t : Fin (N * B), ∑ j : Fin N, (if j.val < J then c t j else 0) ≤
      K * (((J - t.val / B : ℕ) : ℝ) / ((N - t.val / B : ℕ) : ℝ)) := by
    intro t
    have hiN : t.val / B < N :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_eq t.isLt (Nat.mul_comm N B))
    set i := t.val / B with hi
    let j₀ : Fin N := ⟨i, hiN⟩
    have hc : ∀ j : Fin N, c t j = if i ≤ j.val then c t j₀ else 0 := by
      intro j
      split_ifs with h
      · exact swap_count a t j j₀ h le_rfl
      · apply Finset.sum_eq_zero
        intro π _
        rw [if_neg]
        intro hw
        have := (winner_spec hw).1
        rw [mem_round, Equiv.symm_apply_apply] at this
        omega
    have htot : ∑ j : Fin N, c t j ≤ K := by
      calc ∑ j : Fin N, c t j = ∑ π : Equiv.Perm (Fin N), ∑ j : Fin N,
            (if winner B (roundInstance N B π) a t = some (π j) then (1 : ℝ) else 0) :=
            Finset.sum_comm
        _ ≤ ∑ _π : Equiv.Perm (Fin N), (1 : ℝ) :=
            Finset.sum_le_sum (fun π _ => sum_j_le_one π _)
        _ = K := hcard
    have e1 : ∑ j : Fin N, c t j = ((N - i : ℕ) : ℝ) * c t j₀ := by
      rw [Finset.sum_congr rfl (fun j _ => hc j)]
      have := Fin.sum_univ_eq_sum_range (fun k => if i ≤ k ∧ k < N then c t j₀ else 0) N
      rw [cnt, min_self] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _
      simp [j.isLt]
    have e2 : ∑ j : Fin N, (if j.val < J then c t j else 0) = ((J - i : ℕ) : ℝ) * c t j₀ := by
      have := Fin.sum_univ_eq_sum_range (fun k => if i ≤ k ∧ k < J then c t j₀ else 0) N
      rw [cnt, min_eq_right hJ] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro j _
      rw [hc j]
      by_cases h1 : j.val < J <;> by_cases h2 : i ≤ j.val <;> simp [h1, h2]
    rw [e2]
    have hNi : (0 : ℝ) < ((N - i : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hiN
    have hc0 : c t j₀ ≤ K / ((N - i : ℕ) : ℝ) := by
      rw [le_div_iff₀ hNi]; rw [e1] at htot; linarith
    calc ((J - i : ℕ) : ℝ) * c t j₀ ≤ ((J - i : ℕ) : ℝ) * (K / ((N - i : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hc0 (by positivity)
      _ = _ := by ring
  have hcount : ∑ j : Fin N, (if j.val < J then (0 : ℝ) else K * B) = ((N - J : ℕ) : ℝ) * (K * B) := by
    have := Fin.sum_univ_eq_sum_range (fun k => if J ≤ k ∧ k < N then K * B else 0) N
    rw [cnt, min_self] at this
    rw [← this]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h1 : j.val < J
    · simp [h1]
    · have : J ≤ j.val := by omega
      simp [h1, this, j.isLt]
  have hb := block_sum (N := N) (B := B)
    (fun i => K * (((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)))
  calc (∑ π : Equiv.Perm (Fin N), (revenue B (roundInstance N B π) a : ℝ))
      = ∑ j : Fin N, ∑ π : Equiv.Perm (Fin N),
          (load B (roundInstance N B π) a (N * B) (π j) : ℝ) := by
        rw [Finset.sum_congr rfl (fun π _ => hrev π)]
        exact Finset.sum_comm
    _ ≤ ∑ j : Fin N, (if j.val < J then ∑ t, c t j else K * B) :=
        Finset.sum_le_sum (fun j _ => hj j)
    _ = ∑ j : Fin N, ((∑ t, (if j.val < J then c t j else 0)) +
          (if j.val < J then (0 : ℝ) else K * B)) := by
        apply Finset.sum_congr rfl
        intro j _
        split_ifs <;> simp
    _ = ∑ t, ∑ j : Fin N, (if j.val < J then c t j else 0) +
          ∑ j : Fin N, (if j.val < J then (0 : ℝ) else K * B) := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ ∑ t : Fin (N * B), K * (((J - t.val / B : ℕ) : ℝ) / ((N - t.val / B : ℕ) : ℝ)) +
          ((N - J : ℕ) : ℝ) * (K * B) :=
        add_le_add (Finset.sum_le_sum (fun t _ => ht t)) (le_of_eq hcount)
    _ = K * B * (((N - J : ℕ) : ℝ) + ∑ i ∈ range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)) := by
        rw [hb, ← Finset.mul_sum]; ring

theorem harm_log (m : ℕ) : ∀ J : ℕ, Real.log (((m + J + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) ≤
    ∑ i ∈ range J, (1 : ℝ) / ((m + J - i : ℕ) : ℝ) := by
  intro J
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ']
    have h1 : ∀ i ∈ range J, (1 : ℝ) / ((m + (J + 1) - (i + 1) : ℕ) : ℝ) =
        1 / ((m + J - i : ℕ) : ℝ) := by
      intro i _
      rw [show m + (J + 1) - (i + 1) = m + J - i by omega]
    rw [Finset.sum_congr rfl h1]
    have hp1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hp2 : (0 : ℝ) < ((m + J + 1 : ℕ) : ℝ) := by positivity
    have hp3 : (0 : ℝ) < ((m + (J + 1) + 1 : ℕ) : ℝ) := by positivity
    have e : ((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) =
        (((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + J + 1 : ℕ) : ℝ)) *
          (((m + J + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
      field_simp
    rw [e, Real.log_mul (by positivity) (by positivity)]
    have h2 : Real.log (((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + J + 1 : ℕ) : ℝ)) ≤
        1 / ((m + (J + 1) - 0 : ℕ) : ℝ) := by
      have := Real.log_le_sub_one_of_pos
        (x := ((m + (J + 1) + 1 : ℕ) : ℝ) / ((m + J + 1 : ℕ) : ℝ)) (by positivity)
      calc _ ≤ _ := this
        _ = _ := by
          rw [Nat.sub_zero]
          push_cast
          field_simp
          ring
    linarith

theorem core (m J : ℕ) (h : Real.exp 1 * ((m : ℝ) + 1) ≤ (m : ℝ) + J + 1) :
    (m : ℝ) + ∑ i ∈ range (m + J), ((J - i : ℕ) : ℝ) / ((m + J - i : ℕ) : ℝ) ≤ J := by
  have hsplit : ∑ i ∈ range (m + J), ((J - i : ℕ) : ℝ) / ((m + J - i : ℕ) : ℝ) =
      ∑ i ∈ range J, (1 - (m : ℝ) * (1 / ((m + J - i : ℕ) : ℝ))) := by
    rw [← Finset.sum_range_add_sum_Ico _ (show J ≤ m + J by omega)]
    rw [Finset.sum_eq_zero (s := Ico J (m + J)) (fun i hi => by
        rw [Finset.mem_Ico] at hi
        rw [show J - i = 0 by omega]
        simp), add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ((J - i : ℕ) : ℝ) = (J : ℝ) - i := by rw [Nat.cast_sub hi.le]
    have h2 : ((m + J - i : ℕ) : ℝ) = (m : ℝ) + J - i := by
      rw [Nat.cast_sub (by omega : i ≤ m + J)]; push_cast; ring
    have h3 : (0 : ℝ) < (m : ℝ) + J - i := by
      have : (i : ℝ) < J := by exact_mod_cast hi
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    rw [h1, h2]
    field_simp
    ring
  rw [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hS := harm_log m J
  have hlog : 1 ≤ Real.log (((m + J + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ)) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    rw [le_div_iff₀ (by positivity)]
    push_cast
    linarith
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have : (m : ℝ) * 1 ≤ (m : ℝ) * ∑ i ∈ range J, (1 : ℝ) / ((m + J - i : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left (le_trans hlog hS) hm
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this ⊢
  linarith

theorem analytic (δ : ℝ) (hδ : 0 < δ) (N : ℕ) (hN : ⌈2 / δ⌉₊ + 2 ≤ N) :
    ∃ J : ℕ, J ≤ N ∧ ((N - J : ℕ) : ℝ) + ∑ i ∈ range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ) ≤
      (1 - Real.exp (-1) + δ) * N := by
  set e := Real.exp 1 with he
  have he3 : e < 3 := by
    have := Real.exp_one_lt_d9
    rw [he]; linarith
  have he1 : 1 < e := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    rw [he]; linarith
  have hepos : 0 < e := by linarith
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hδN : 2 ≤ δ * N := by
    have h1 : 2 / δ ≤ (⌈2 / δ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 / δ⌉₊ : ℝ) ≤ N := by exact_mod_cast (by omega : ⌈2 / δ⌉₊ ≤ N)
    have h3 : 2 / δ ≤ N := le_trans h1 h2
    rw [div_le_iff₀ hδ] at h3
    linarith
  obtain ⟨m, hmle, hmlow⟩ : ∃ m : ℕ, e * ((m : ℝ) + 1) ≤ (N : ℝ) + 1 ∧
      ((N : ℝ) + 1) / e - 2 < m := by
    set F := ⌊((N : ℝ) + 1) / e⌋₊ with hF
    have hF1 : 1 ≤ F := by
      apply Nat.le_floor
      rw [le_div_iff₀ hepos]
      push_cast
      linarith
    have hFle : (F : ℝ) ≤ ((N : ℝ) + 1) / e := Nat.floor_le (by positivity)
    have hFgt : ((N : ℝ) + 1) / e < F + 1 := Nat.lt_floor_add_one _
    refine ⟨F - 1, ?_, ?_⟩
    · have : ((F - 1 : ℕ) : ℝ) + 1 = F := by
        rw [Nat.cast_sub hF1]; push_cast; ring
      rw [this]
      rw [le_div_iff₀ hepos] at hFle
      linarith
    · rw [Nat.cast_sub hF1]; push_cast; linarith
  have hmN : m ≤ N := by
    have : (m : ℝ) + 1 ≤ (N : ℝ) + 1 := by nlinarith
    have : (m : ℝ) ≤ N := by linarith
    exact_mod_cast this
  obtain ⟨J, rfl⟩ : ∃ J, N = m + J := ⟨N - m, by omega⟩
  refine ⟨J, by omega, ?_⟩
  rw [show m + J - J = m by omega]
  have hc := core m J (by push_cast at hmle; linarith)
  have hinv : Real.exp (-1) = e⁻¹ := by rw [he, Real.exp_neg]
  rw [hinv]
  push_cast at hmlow hδN ⊢
  rw [div_eq_mul_inv] at hmlow
  nlinarith [inv_pos.mpr hepos]

theorem avg_le {α : Type} (A : PMF α) (s : Finset α) (hs : ∀ a, a ∈ s) {ι : Type} [Fintype ι]
    (f : α → ι → ℝ) (C : ℝ) (h : ∀ a, ∑ π, f a π ≤ C) :
    ∑ π, ∑ a ∈ s, (A a).toReal * f a π ≤ C := by
  have hA : ∑ a ∈ s, (A a).toReal = 1 := by
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top A a)]
    have h1 : ∑' a, A a = ∑ a ∈ s, A a := tsum_eq_sum (fun b hb => absurd (hs b) hb)
    rw [← h1, PMF.tsum_coe, ENNReal.toReal_one]
  rw [Finset.sum_comm]
  calc ∑ a ∈ s, ∑ π, (A a).toReal * f a π = ∑ a ∈ s, (A a).toReal * ∑ π, f a π := by
        simp_rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ s, (A a).toReal * C :=
        Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    _ = C := by rw [← Finset.sum_mul, hA, one_mul]

theorem offline_eq (N B : ℕ) (hB : 1 ≤ B) (π : Equiv.Perm (Fin N)) :
    offlineRevenue B (roundInstance N B π) (roundAllocation N B π) = N * B := by
  unfold offlineRevenue
  have hBpos : 0 < B := hB
  have key : ∀ r : Fin N, min B ((univ.filter (fun t => roundAllocation N B π t = some r ∧
      r ∈ roundInstance N B π t)).card) = B := by
    intro r
    apply min_eq_left
    have hv : ∀ s : Fin B, (finProdFinEquiv (π.symm r, s)).val / B = (π.symm r).val := by
      intro s
      rw [finProdFinEquiv_apply_val]
      simp only
      rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt s.isLt, zero_add]
    have hcard := Finset.card_le_card_of_injOn (s := (univ : Finset (Fin B)))
      (t := univ.filter (fun t => roundAllocation N B π t = some r ∧ r ∈ roundInstance N B π t))
      (fun s => finProdFinEquiv (π.symm r, s)) ?_ ?_
    · simpa using hcard
    · intro s _
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · unfold roundAllocation
        rw [dif_pos (by rw [hv s]; exact (π.symm r).isLt)]
        congr 1
        have : (⟨(finProdFinEquiv (π.symm r, s)).val / B, by rw [hv s]; exact (π.symm r).isLt⟩ :
            Fin N) = π.symm r := Fin.ext (hv s)
        rw [this, Equiv.apply_symm_apply]
      · rw [mem_round, hv s]
    · intro s₁ _ s₂ _ h
      have := finProdFinEquiv.injective h
      simpa using this
  rw [Finset.sum_congr rfl (fun r _ => key r)]
  simp

end AdWordsMSVV.LowerBound.KVVAux

open AdWordsMSVV.LowerBound in
theorem solution :
    ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ B : ℕ, 1 ≤ B →
      ∀ A : RandAlg N (N * B), ∃ (I : Instance N (N * B)) (τ : Fin (N * B) → Option (Fin N)),
        offlineRevenue B I τ = N * B ∧
        expectedRevenue B I A ≤ (1 - Real.exp (-1) + δ) * ((N : ℝ) * B) := by
  intro δ hδ
  refine ⟨⌈2 / δ⌉₊ + 2, ?_⟩
  intro N hN B hB A
  obtain ⟨J, hJN, hX⟩ := KVVAux.analytic δ hδ N hN
  set X : ℝ := ((N - J : ℕ) : ℝ) + ∑ i ∈ Finset.range N, ((J - i : ℕ) : ℝ) / ((N - i : ℕ) : ℝ)
    with hXdef
  have hsum : ∑ π : Equiv.Perm (Fin N), expectedRevenue B (roundInstance N B π) A ≤
      ∑ _π : Equiv.Perm (Fin N), ((B : ℝ) * X) := by
    have hconst : ∑ _π : Equiv.Perm (Fin N), ((B : ℝ) * X) = (N.factorial : ℝ) * B * X := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [hconst]
    unfold expectedRevenue
    exact KVVAux.avg_le A _ (fun a => by simp) (fun a π => (revenue B (roundInstance N B π) a : ℝ))
      _ (fun a => KVVAux.perm_sum_bound N B J hJN a)
  obtain ⟨π, _, hπ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨roundInstance N B π, roundAllocation N B π, KVVAux.offline_eq N B hB π, ?_⟩
  calc expectedRevenue B (roundInstance N B π) A ≤ (B : ℝ) * X := hπ
    _ ≤ (B : ℝ) * ((1 - Real.exp (-1) + δ) * N) :=
        mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg B)
    _ = (1 - Real.exp (-1) + δ) * ((N : ℝ) * B) := by ring
