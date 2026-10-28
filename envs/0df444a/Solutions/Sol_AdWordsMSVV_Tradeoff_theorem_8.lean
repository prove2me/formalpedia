-- Prove2me | solution 1 for AdWordsMSVV.Tradeoff.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T13:22:36.238728+00:00
-- url     : https://prove2.me/submissions/76991601-e7cd-4058-a910-77222fbaf856

import Mathlib
import Definitions.Def_AdWordsMSVV_Tradeoff_Setting
import Definitions.Def_AdWordsMSVV_Tradeoff_LP

set_option autoImplicit false

namespace AdWordsMSVV.Tradeoff.T8Aux

open AdWordsMSVV.Tradeoff Finset

/-- `R k = 1 - 1/k`. -/
noncomputable def R (k : ℕ) : ℝ := 1 - 1 / (k : ℝ)

lemma R_nonneg {k : ℕ} (hk : 1 ≤ k) : 0 ≤ R k := by
  unfold R
  have h1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have h2 : 1 / (k:ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact h1
  linarith

lemma R_le_one (k : ℕ) : R k ≤ 1 := by
  unfold R
  have : (0:ℝ) ≤ 1 / (k:ℝ) := by positivity
  linarith

lemma psi_eq {k : ℕ} (hk : 1 ≤ k) (j : ℕ) : psi k j = 1 - R k ^ (k - j) := by
  suffices h : ∀ n j, k - j = n → psi k j = 1 - R k ^ n from h _ j rfl
  intro n
  induction n with
  | zero =>
    intro j hj
    have hkj : k ≤ j := by omega
    have he : Icc j (k - 1) = ∅ := by
      ext x
      simp only [mem_Icc, Finset.notMem_empty, iff_false, not_and, not_le]
      intro _; omega
    simp [psi, he]
  | succ n ih =>
    intro j hj
    have hsplit : Icc j (k - 1) = insert j (Icc (j + 1) (k - 1)) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    have hnot : j ∉ Icc (j + 1) (k - 1) := by simp
    have h1 : psi k (j + 1) = 1 - R k ^ n := ih (j + 1) (by omega)
    unfold psi at h1 ⊢
    rw [hsplit, sum_insert hnot, h1]
    have he : k - j - 1 = n := by omega
    unfold yStar
    rw [he, pow_succ]
    unfold R
    ring

lemma psi_nonneg {k : ℕ} (hk : 1 ≤ k) (j : ℕ) : 0 ≤ psi k j := by
  rw [psi_eq hk]
  have := pow_le_one₀ (n := k - j) (R_nonneg hk) (R_le_one k)
  linarith

lemma psi_anti {k : ℕ} (hk : 1 ≤ k) {j j' : ℕ} (h : j ≤ j') : psi k j' ≤ psi k j := by
  rw [psi_eq hk, psi_eq hk]
  have := pow_le_pow_of_le_one (R_nonneg hk) (R_le_one k) (Nat.sub_le_sub_left h k)
  linarith

lemma slab_ge_one (k : ℕ) (s : ℝ) : 1 ≤ slabOf k s := le_max_left _ _

lemma slab_mono (k : ℕ) {s s' : ℝ} (h : s ≤ s') : slabOf k s ≤ slabOf k s' := by
  unfold slabOf
  exact max_le_max le_rfl (Nat.ceil_mono (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg k)))

lemma slab_le_k {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs1 : s ≤ 1) : slabOf k s ≤ k := by
  unfold slabOf
  apply max_le hk
  apply Nat.ceil_le.mpr
  have : (0:ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

lemma slab_upper {k : ℕ} (hk : 1 ≤ k) {s : ℝ} : s ≤ (slabOf k s : ℝ) / k := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [le_div_iff₀ hkpos]
  unfold slabOf
  calc s * k = k * s := mul_comm _ _
    _ ≤ (⌈(k:ℝ) * s⌉₊ : ℝ) := Nat.le_ceil _
    _ ≤ _ := by exact_mod_cast le_max_right _ _

lemma slab_lower {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) :
    (slabOf k s : ℝ) / k - 1 / k ≤ s := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  rw [← sub_div, div_le_iff₀ hkpos]
  unfold slabOf
  rcases le_total 1 ⌈(k:ℝ) * s⌉₊ with h | h
  · rw [max_eq_right h]
    have := Nat.ceil_lt_add_one (show 0 ≤ (k:ℝ) * s by positivity)
    linarith [mul_comm (k:ℝ) s]
  · rw [max_eq_left h]
    simp only [Nat.cast_one, sub_self]
    positivity

lemma slab_zero (k : ℕ) : slabOf k 0 = 1 := by
  unfold slabOf; simp

lemma slab_one {k : ℕ} (hk : 1 ≤ k) : slabOf k 1 = k := by
  unfold slabOf
  rw [mul_one, Nat.ceil_natCast]
  exact max_eq_right hk

/-- The potential: the integral of `1 - ψ(slab x)` from `0` to `s`, in closed form. -/
noncomputable def G (k : ℕ) (s : ℝ) : ℝ :=
  R k ^ (k - slabOf k s) * (1 - (slabOf k s : ℝ) / k + s) - R k ^ k

lemma G_zero {k : ℕ} (hk : 1 ≤ k) : G k 0 = 0 := by
  unfold G
  rw [slab_zero]
  have h : R k ^ k = R k ^ (k - 1) * R k := by
    rw [← pow_succ]; congr 1; omega
  rw [h]
  simp only [Nat.cast_one]
  unfold R
  ring

lemma G_nonneg {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : 0 ≤ G k s := by
  unfold G
  have h1 : 1 ≤ slabOf k s := slab_ge_one k s
  have hl := slab_lower hk hs0
  have hR0 := R_nonneg hk
  have hR1 := R_le_one k
  have hp : R k ^ k ≤ R k ^ (k - slabOf k s) * R k := by
    rw [← pow_succ]; exact pow_le_pow_of_le_one hR0 hR1 (by omega)
  have hu : R k ≤ 1 - (slabOf k s : ℝ) / k + s := by unfold R; linarith
  have : R k ^ (k - slabOf k s) * R k ≤ R k ^ (k - slabOf k s) * (1 - (slabOf k s : ℝ) / k + s) :=
    mul_le_mul_of_nonneg_left hu (pow_nonneg hR0 _)
  linarith

lemma bern {k : ℕ} (hk : 1 ≤ k) (d : ℕ) : 1 - (d:ℝ) / k ≤ R k ^ d := by
  induction d with
  | zero => simp
  | succ n ih =>
    have hR0 := R_nonneg hk
    rw [pow_succ]
    have h1 : (1 - (n:ℝ) / k) * R k ≤ R k ^ n * R k := mul_le_mul_of_nonneg_right ih hR0
    have h2 : 1 - ((n + 1 : ℕ) : ℝ) / k ≤ (1 - (n:ℝ) / k) * R k := by
      unfold R
      push_cast
      have : 0 ≤ (n:ℝ) / k * (1 / k) := by positivity
      have e : ((n:ℝ) + 1) / k = (n:ℝ) / k + 1 / k := by ring
      rw [e]
      nlinarith
    linarith

lemma core_step {k i i' : ℕ} (hk : 1 ≤ k) (hii' : i ≤ i') (hi'k : i' ≤ k) {s : ℝ}
    (hu0 : 0 ≤ 1 - (i:ℝ) / k + s) (hu1 : s ≤ (i:ℝ) / k) :
    R k ^ (k - i') * (1 - (i':ℝ) / k + s) ≤ R k ^ (k - i) * (1 - (i:ℝ) / k + s) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hii'
  have hpow : R k ^ (k - i) = R k ^ (k - (i + d)) * R k ^ d := by
    rw [← pow_add]; congr 1; omega
  have hR0 := R_nonneg hk
  have hR1 := R_le_one k
  have hbern := bern hk d
  have hRd1 : R k ^ d ≤ 1 := pow_le_one₀ hR0 hR1
  rw [hpow]
  have hX1 : 1 - (i:ℝ) / k + s ≤ 1 := by linarith
  have hin : 1 - ((i + d : ℕ) : ℝ) / k + s ≤ R k ^ d * (1 - (i:ℝ) / k + s) := by
    have e : 1 - ((i + d : ℕ) : ℝ) / k + s = (1 - (i:ℝ) / k + s) - (d:ℝ) / k := by
      push_cast; ring
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.mpr hX1) (sub_nonneg.mpr hRd1)]
  calc R k ^ (k - (i + d)) * (1 - ((i + d : ℕ) : ℝ) / k + s)
      ≤ R k ^ (k - (i + d)) * (R k ^ d * (1 - (i:ℝ) / k + s)) :=
        mul_le_mul_of_nonneg_left hin (pow_nonneg hR0 _)
    _ = _ := by ring

lemma G_step {k : ℕ} (hk : 1 ≤ k) {s s' : ℝ} (hs0 : 0 ≤ s) (hss' : s ≤ s') (hs'1 : s' ≤ 1) :
    G k s' - G k s ≤ (s' - s) * R k ^ (k - slabOf k s') := by
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hik : ((slabOf k s : ℕ) : ℝ) / k ≤ 1 :=
    (div_le_one hkpos).mpr (by exact_mod_cast slab_le_k hk (le_trans hss' hs'1))
  have hcore := core_step hk (slab_mono k hss') (slab_le_k hk hs'1) (s := s) (by linarith)
    (slab_upper hk)
  unfold G
  nlinarith [hcore]

lemma G_step2 {k : ℕ} (hk : 1 ≤ k) {s c η : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) (hc0 : 0 ≤ c)
    (hcη : c ≤ η) :
    G k (min 1 (s + c)) ≤ G k s + c * R k ^ (k - slabOf k s)
      + η * (R k ^ (k - slabOf k (min 1 (s + c))) - R k ^ (k - slabOf k s)) := by
  have hss' : s ≤ min 1 (s + c) := le_min hs1.le (by linarith)
  have hs'1 : min 1 (s + c) ≤ 1 := min_le_left _ _
  have h := G_step hk hs0 hss' hs'1
  have hdc : min 1 (s + c) - s ≤ c := by have := min_le_right 1 (s + c); linarith
  have hR0 := R_nonneg hk
  have hR1 := R_le_one k
  have hmono : R k ^ (k - slabOf k s) ≤ R k ^ (k - slabOf k (min 1 (s + c))) :=
    pow_le_pow_of_le_one hR0 hR1 (Nat.sub_le_sub_left (slab_mono k hss') k)
  have hA0 : 0 ≤ R k ^ (k - slabOf k s) := pow_nonneg hR0 _
  nlinarith [mul_le_mul_of_nonneg_right hdc hA0,
    mul_le_mul_of_nonneg_right (le_trans hdc hcη) (sub_nonneg.mpr hmono)]

lemma key_alive {k : ℕ} (hk : 1 ≤ k) {s : ℝ} (hs0 : 0 ≤ s) :
    1 - R k ^ k - 1 / k ≤ G k s + psi k (slabOf k s) := by
  rw [psi_eq hk]
  unfold G
  have hl := slab_lower hk hs0
  have hR0 := R_nonneg hk
  have hR1 := R_le_one k
  have hA0 : 0 ≤ R k ^ (k - slabOf k s) := pow_nonneg hR0 _
  have hA1 : R k ^ (k - slabOf k s) ≤ 1 := pow_le_one₀ hR0 hR1
  have hk1 : 0 ≤ 1 / (k:ℝ) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (show (slabOf k s : ℝ) / k - s ≤ 1 / k by linarith) hA0,
    mul_le_mul_of_nonneg_right hA1 hk1]

lemma err_bound {k : ℕ} (hk : 1 ≤ k) {F : ℝ} (hF0 : 0 ≤ F) :
    R k ^ (k - slabOf k F) - R k ^ (k - 1) ≤ k * F := by
  have hR0 := R_nonneg hk
  have hR1 := R_le_one k
  by_cases h : slabOf k F = 1
  · rw [h, sub_self]; positivity
  · have h2 : 1 < ⌈(k:ℝ) * F⌉₊ := by
      unfold slabOf at h
      by_contra hc
      push_neg at hc
      exact h (max_eq_left hc)
    have h3 : (1:ℝ) < k * F := by exact_mod_cast Nat.lt_ceil.mp h2
    have h4 : R k ^ (k - slabOf k F) ≤ 1 := pow_le_one₀ hR0 hR1
    have h5 : 0 ≤ R k ^ (k - 1) := pow_nonneg hR0 _
    linarith

lemma sum_before_succ {M : ℕ} (P : Fin M → Prop) [DecidablePred P] (f : Fin M → ℝ) (t : ℕ)
    (ht : t < M) :
    ∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < t + 1 ∧ P j), f j
      = ∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < t ∧ P j), f j
        + (if P ⟨t, ht⟩ then f ⟨t, ht⟩ else 0) := by
  rw [sum_filter, sum_filter]
  have h0 : (if P ⟨t, ht⟩ then f ⟨t, ht⟩ else 0)
      = ∑ j : Fin M, if (j:ℕ) = t ∧ P j then f j else 0 := by
    rw [Finset.sum_eq_single (⟨t, ht⟩ : Fin M)]
    · simp
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h1, _⟩
      exact hj (Fin.ext h1)
    · intro h; exact absurd (mem_univ _) h
  rw [h0, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  by_cases h1 : (j:ℕ) < t
  · have h2 : (j:ℕ) ≠ t := by omega
    have h3 : (j:ℕ) < t + 1 := by omega
    simp [h1, h2, h3]
  · by_cases h2 : (j:ℕ) = t
    · simp [h1, h2]
    · have h3 : ¬ (j:ℕ) < t + 1 := by omega
      simp [h1, h2, h3]

section bidder

variable {N M : ℕ}

lemma assigned_nonneg {bid : Fin N → Fin M → ℝ} (hb0 : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (b : Fin N) (t : ℕ) : 0 ≤ assignedBefore bid σ b t :=
  sum_nonneg (fun j _ => hb0 b j)

lemma spend_nonneg {bid : Fin N → Fin M → ℝ} (hb0 : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (b : Fin N) (t : ℕ) : 0 ≤ spend bid σ b t :=
  le_min zero_le_one (assigned_nonneg hb0 σ b t)

lemma spend_le_one (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N)) (b : Fin N) (t : ℕ) :
    spend bid σ b t ≤ 1 := min_le_left _ _

lemma assigned_mono {bid : Fin N → Fin M → ℝ} (hb0 : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (b : Fin N) {t t' : ℕ} (h : t ≤ t') :
    assignedBefore bid σ b t ≤ assignedBefore bid σ b t' := by
  unfold assignedBefore
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj ⊢
    exact ⟨lt_of_lt_of_le hj.1 h, hj.2⟩
  · intro j _ _; exact hb0 b j

lemma spend_mono {bid : Fin N → Fin M → ℝ} (hb0 : ∀ b t, 0 ≤ bid b t)
    (σ : Fin M → Option (Fin N)) (b : Fin N) {t t' : ℕ} (h : t ≤ t') :
    spend bid σ b t ≤ spend bid σ b t' :=
  min_le_min le_rfl (assigned_mono hb0 σ b h)

/-- The dual variable of a query: the bid times `ψ(slab)` of the run's choice. -/
noncomputable def betaQ (k : ℕ) (bid : Fin N → Fin M → ℝ) (σ : Fin M → Option (Fin N))
    (j : Fin M) : ℝ :=
  ∑ b, if σ j = some b then bid b j * psi k (slabOf k (spend bid σ b j)) else 0

lemma betaQ_nonneg {k : ℕ} (hk : 1 ≤ k) {bid : Fin N → Fin M → ℝ} (hb0 : ∀ b t, 0 ≤ bid b t)
    {σ : Fin M → Option (Fin N)} (j : Fin M) : 0 ≤ betaQ k bid σ j := by
  unfold betaQ
  apply sum_nonneg
  intro b _
  split_ifs
  · exact mul_nonneg (hb0 b j) (psi_nonneg hk _)
  · exact le_refl 0

lemma inv_run {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 ≤ η) {bid : Fin N → Fin M → ℝ}
    (hbid : ∀ b t, 0 ≤ bid b t ∧ bid b t ≤ η) {σ : Fin M → Option (Fin N)}
    (hrun : IsRun (psi k) k bid σ) (b : Fin N) :
    ∀ t, t ≤ M →
      G k (spend bid σ b t) ≤ (∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < t ∧ σ j = some b),
          bid b j * R k ^ (k - slabOf k (spend bid σ b j)))
        + η * (R k ^ (k - slabOf k (spend bid σ b t)) - R k ^ (k - 1)) ∧
      assignedBefore bid σ b t ≤ 1 + η := by
  have hb0 : ∀ b t, 0 ≤ bid b t := fun b t => (hbid b t).1
  intro t
  induction t with
  | zero =>
    intro _
    have h0 : assignedBefore bid σ b 0 = 0 := by simp [assignedBefore]
    have hs : spend bid σ b 0 = 0 := by simp [spend, h0]
    rw [hs, G_zero hk, slab_zero, h0]
    constructor
    · simp
    · linarith
  | succ t ih =>
    intro ht
    have htM : t < M := by omega
    obtain ⟨I1, I2⟩ := ih (by omega)
    have hAsucc : assignedBefore bid σ b (t + 1) = assignedBefore bid σ b t +
        (if σ ⟨t, htM⟩ = some b then bid b ⟨t, htM⟩ else 0) := by
      unfold assignedBefore
      exact sum_before_succ (fun j => σ j = some b) (fun j => bid b j) t htM
    have hasucc : (∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < t + 1 ∧ σ j = some b),
          bid b j * R k ^ (k - slabOf k (spend bid σ b j)))
        = (∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < t ∧ σ j = some b),
          bid b j * R k ^ (k - slabOf k (spend bid σ b j)))
          + (if σ ⟨t, htM⟩ = some b
              then bid b ⟨t, htM⟩ * R k ^ (k - slabOf k (spend bid σ b t)) else 0) :=
      sum_before_succ (fun j => σ j = some b)
        (fun j => bid b j * R k ^ (k - slabOf k (spend bid σ b j))) t htM
    by_cases hσ : σ ⟨t, htM⟩ = some b
    · rw [if_pos hσ] at hAsucc hasucc
      have hr := hrun ⟨t, htM⟩
      simp only [hσ] at hr
      have halive : spend bid σ b t < 1 := hr.1
      have hA : assignedBefore bid σ b t < 1 := by
        unfold spend at halive
        rcases min_lt_iff.mp halive with h | h
        · exact absurd h (lt_irrefl 1)
        · exact h
      have hspend_t : spend bid σ b t = assignedBefore bid σ b t := min_eq_right hA.le
      have hspend_succ : spend bid σ b (t + 1) = min 1 (spend bid σ b t + bid b ⟨t, htM⟩) := by
        show min 1 (assignedBefore bid σ b (t + 1)) = _
        rw [hAsucc, hspend_t]
      have hstep := G_step2 hk (spend_nonneg hb0 σ b t) halive (hbid b ⟨t, htM⟩).1
        (hbid b ⟨t, htM⟩).2
      rw [← hspend_succ] at hstep
      constructor
      · rw [hasucc]
        linarith
      · rw [hAsucc]
        linarith [(hbid b ⟨t, htM⟩).2]
    · rw [if_neg hσ, add_zero] at hAsucc hasucc
      have hs : spend bid σ b (t + 1) = spend bid σ b t := by
        show min 1 (assignedBefore bid σ b (t + 1)) = min 1 (assignedBefore bid σ b t)
        rw [hAsucc]
      rw [hs, hasucc, hAsucc]
      exact ⟨I1, I2⟩

lemma lower_b {k : ℕ} (hk : 1 ≤ k) {bid : Fin N → Fin M → ℝ}
    (hb0 : ∀ b t, 0 ≤ bid b t) {σ : Fin M → Option (Fin N)}
    (hrun : IsRun (psi k) k bid σ) (τ : Fin M → Option (Fin N)) (b : Fin N) :
    (1 - R k ^ k - 1 / k) * min 1 (∑ j ∈ univ.filter (fun j : Fin M => τ j = some b), bid b j)
      ≤ G k (spend bid σ b M)
        + ∑ j ∈ univ.filter (fun j : Fin M => τ j = some b), betaQ k bid σ j := by
  set X := ∑ j ∈ univ.filter (fun j : Fin M => τ j = some b), bid b j with hX
  have hX0 : 0 ≤ X := sum_nonneg (fun j _ => hb0 b j)
  have hm0 : 0 ≤ min 1 X := le_min zero_le_one hX0
  have hm1 : min 1 X ≤ 1 := min_le_left _ _
  have hmX : min 1 X ≤ X := min_le_right _ _
  have hF0 := spend_nonneg hb0 σ b M
  have hF1 := spend_le_one bid σ b M
  have hkey := key_alive hk hF0
  have hG0 := G_nonneg hk hF0 hF1
  have hβ0 : ∀ j, 0 ≤ betaQ k bid σ j := fun j => betaQ_nonneg hk hb0 j
  have hs := sum_nonneg (fun j (_ : j ∈ univ.filter (fun j : Fin M => τ j = some b)) => hβ0 j)
  by_cases hlt : spend bid σ b M < 1
  · have hψ0 := psi_nonneg hk (slabOf k (spend bid σ b M))
    have hβ : ∀ j ∈ univ.filter (fun j : Fin M => τ j = some b),
        bid b j * psi k (slabOf k (spend bid σ b M)) ≤ betaQ k bid σ j := by
      intro j _
      have hle : spend bid σ b j ≤ spend bid σ b M := spend_mono hb0 σ b (le_of_lt j.isLt)
      have halive : Alive bid σ b (j:ℕ) := lt_of_le_of_lt hle hlt
      have hr := hrun j
      rcases hσj : σ j with _ | b''
      · simp only [hσj] at hr
        exact absurd halive (hr b)
      · simp only [hσj] at hr
        obtain ⟨_, hmax⟩ := hr
        have h1 := hmax b halive
        have h2 : betaQ k bid σ j = bid b'' j * psi k (slabOf k (spend bid σ b'' j)) := by
          simp [betaQ, hσj]
        rw [h2]
        refine le_trans ?_ h1
        exact mul_le_mul_of_nonneg_left (psi_anti hk (slab_mono k hle)) (hb0 b j)
    have hsum := sum_le_sum hβ
    rw [← sum_mul, ← hX] at hsum
    nlinarith [mul_le_mul_of_nonneg_right hkey hm0, mul_le_mul_of_nonneg_left hm1 hG0,
      mul_le_mul_of_nonneg_left hmX hψ0]
  · have hF : spend bid σ b M = 1 := le_antisymm hF1 (not_lt.mp hlt)
    have hψ : psi k (slabOf k (spend bid σ b M)) = 0 := by
      rw [hF, slab_one hk, psi_eq hk, Nat.sub_self, pow_zero, sub_self]
    rw [hψ, add_zero] at hkey
    nlinarith [mul_le_mul_of_nonneg_right hkey hm0, mul_le_mul_of_nonneg_left hm1 hG0]

lemma main_bound {k : ℕ} (hk : 1 ≤ k) {η : ℝ} (hη : 0 ≤ η) {bid : Fin N → Fin M → ℝ}
    (hbid : ∀ b t, 0 ≤ bid b t ∧ bid b t ≤ η) {σ : Fin M → Option (Fin N)}
    (hrun : IsRun (psi k) k bid σ) (τ : Fin M → Option (Fin N)) :
    (1 - R k ^ k - 1 / k) * revenue bid τ ≤ (1 + ((k:ℝ) + 1) * η) * revenue bid σ := by
  have hb0 : ∀ b t, 0 ≤ bid b t := fun b t => (hbid b t).1
  have hup : ∀ b, G k (spend bid σ b M)
      + ∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < M ∧ σ j = some b),
        bid b j * psi k (slabOf k (spend bid σ b j))
      ≤ (1 + ((k:ℝ) + 1) * η) * spend bid σ b M := by
    intro b
    obtain ⟨I1, I2⟩ := inv_run hk hη hbid hrun b M le_rfl
    have hsum : (∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < M ∧ σ j = some b),
          bid b j * R k ^ (k - slabOf k (spend bid σ b j)))
        + (∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < M ∧ σ j = some b),
          bid b j * psi k (slabOf k (spend bid σ b j))) = assignedBefore bid σ b M := by
      rw [← sum_add_distrib]
      unfold assignedBefore
      apply sum_congr rfl
      intro j _
      rw [psi_eq hk]
      ring
    have herr := err_bound hk (spend_nonneg hb0 σ b M)
    have herr' := mul_le_mul_of_nonneg_left herr hη
    have hA0 := assigned_nonneg hb0 σ b M
    have hF : assignedBefore bid σ b M ≤ (1 + η) * spend bid σ b M := by
      unfold spend
      rcases le_total (assignedBefore bid σ b M) 1 with h | h
      · rw [min_eq_right h]; nlinarith
      · rw [min_eq_left h]; linarith
    have hF0 := spend_nonneg hb0 σ b M
    nlinarith
  have hβsum : ∑ b, ∑ j ∈ univ.filter (fun j : Fin M => (j:ℕ) < M ∧ σ j = some b),
      bid b j * psi k (slabOf k (spend bid σ b j)) = ∑ j, betaQ k bid σ j := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    unfold betaQ
    apply sum_congr rfl
    intro b _
    simp [j.isLt]
  have h8 : ∑ b, ∑ j ∈ univ.filter (fun j : Fin M => τ j = some b), betaQ k bid σ j
      ≤ ∑ j, betaQ k bid σ j := by
    simp_rw [sum_filter]
    rw [sum_comm]
    apply sum_le_sum
    intro j _
    rcases hτ : τ j with _ | b0
    · simp [betaQ_nonneg hk hb0 j]
    · simp
  have hrevσ : revenue bid σ = ∑ b, spend bid σ b M := by
    unfold revenue spend
    apply sum_congr rfl
    intro b _
    congr 1
    unfold assignedBefore
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext j
    simp [j.isLt]
  have hrevτ : revenue bid τ
      = ∑ b, min 1 (∑ j ∈ univ.filter (fun j : Fin M => τ j = some b), bid b j) := rfl
  rw [hrevτ, hrevσ, mul_sum, mul_sum]
  have hA := sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin N))) => lower_b hk hb0 hrun τ b)
  rw [sum_add_distrib] at hA
  have hB := sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin N))) => hup b)
  rw [sum_add_distrib, hβsum] at hB
  linarith

end bidder

end AdWordsMSVV.Tradeoff.T8Aux

open AdWordsMSVV.Tradeoff in
theorem solution :
    ∀ δ : ℝ, 0 < δ → ∃ k₀ : ℕ, ∀ k ≥ k₀, ∃ η : ℝ, 0 < η ∧
      ∀ (N M : ℕ) (bid : Fin N → Fin M → ℝ), (∀ b t, 0 ≤ bid b t ∧ bid b t ≤ η) →
      ∀ σ : Fin M → Option (Fin N), IsRun (psi k) k bid σ →
      ∀ τ : Fin M → Option (Fin N),
        (1 - Real.exp (-1) - δ) * revenue bid τ ≤ revenue bid σ := by
  intro δ hδ
  refine ⟨⌈2 / δ⌉₊ + 2, ?_⟩
  intro k hk
  have hk1 : 1 ≤ k := by omega
  have hkpos : (0:ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk2 : 2 / δ ≤ (k:ℝ) := by
    have h1 := Nat.le_ceil (2 / δ)
    have h2 : ((⌈2 / δ⌉₊ + 2 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
    push_cast at h2
    linarith
  have hinv : 1 / (k:ℝ) ≤ δ / 2 := by
    rw [div_le_iff₀ hkpos]
    rw [div_le_iff₀ hδ] at hk2
    linarith
  refine ⟨δ / (2 * ((k:ℝ) + 1)), by positivity, ?_⟩
  intro N M bid hbid σ hrun τ
  have hη0 : (0:ℝ) ≤ δ / (2 * ((k:ℝ) + 1)) := by positivity
  have hmain := AdWordsMSVV.Tradeoff.T8Aux.main_bound hk1 hη0 hbid hrun τ
  have hx : ((k:ℝ) + 1) * (δ / (2 * ((k:ℝ) + 1))) = δ / 2 := by
    field_simp
  rw [hx] at hmain
  have hRk : AdWordsMSVV.Tradeoff.T8Aux.R k ^ k ≤ Real.exp (-1) := by
    unfold AdWordsMSVV.Tradeoff.T8Aux.R
    exact Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hk1)
  have hτ0 : 0 ≤ revenue bid τ := by
    unfold revenue
    exact Finset.sum_nonneg (fun b _ => le_min zero_le_one
      (Finset.sum_nonneg (fun j _ => (hbid b j).1)))
  have ha1 : 1 - Real.exp (-1) - δ ≤ 1 := by
    have := Real.exp_pos (-1); linarith
  have h1 : (1 - Real.exp (-1) - δ) * (1 + δ / 2)
      ≤ 1 - AdWordsMSVV.Tradeoff.T8Aux.R k ^ k - 1 / k := by
    nlinarith [mul_le_mul_of_nonneg_right ha1 (show (0:ℝ) ≤ δ / 2 by positivity)]
  have h2 : (1 + δ / 2) * ((1 - Real.exp (-1) - δ) * revenue bid τ)
      ≤ (1 + δ / 2) * revenue bid σ := by
    have := le_trans (mul_le_mul_of_nonneg_right h1 hτ0) hmain
    linarith
  exact le_of_mul_le_mul_left h2 (by linarith)
