-- Prove2me | solution 1 for AssemblyCoord.Feedback.lemma_OA2_i
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T00:58:12.629925+00:00
-- url     : https://prove2.me/submissions/bc9c7190-de98-47f2-8325-a80aa01e87c6

import Mathlib
import Definitions.Def_AssemblyCoord_Feedback_Model

namespace AssemblyCoord.Feedback

theorem X_play_zero {M : ℕ} (σ : Profile M) (h : History M) : play σ h 0 = h := rfl

theorem X_play_succ {M : ℕ} (σ : Profile M) (h : History M) (k : ℕ) :
    play σ h (k+1) = play σ (h ++ [fun i => σ i h]) k := rfl

theorem X_play_succ_right {M : ℕ} (σ : Profile M) :
    ∀ (k : ℕ) (h : History M), play σ h (k+1) = play σ h k ++ [fun i => σ i (play σ h k)]
  | 0, h => rfl
  | k+1, h => by
      rw [X_play_succ σ h (k+1), X_play_succ_right σ k (h ++ [fun i => σ i h])]
      rfl

theorem X_play_length {M : ℕ} (σ : Profile M) :
    ∀ (k : ℕ) (h : History M), (play σ h k).length = h.length + k
  | 0, h => rfl
  | k+1, h => by
      rw [X_play_succ, X_play_length σ k]; simp; omega

theorem X_play_add {M : ℕ} (σ : Profile M) (h : History M) (a : ℕ) :
    ∀ b : ℕ, play σ (play σ h a) b = play σ h (a + b)
  | 0 => rfl
  | b+1 => by
      rw [← Nat.add_assoc, X_play_succ_right σ (a+b) h, X_play_succ_right σ b (play σ h a),
        X_play_add σ h a b]

theorem X_level_append {M : ℕ} (q0 : Fin M → ℝ) (h : History M) (a : Fin M → ℝ) (j : Fin M) :
    level q0 (h ++ [a]) j = level q0 h j + a j := by
  simp [level, List.map_append, List.sum_append, add_assoc]

theorem X_level_nil {M : ℕ} (q0 : Fin M → ℝ) (j : Fin M) : level q0 [] j = q0 j := by
  simp [level]

theorem X_final_step (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) (h : History P.M)
    (hlen : h.length < P.N) :
    P.final q0 σ h = P.final q0 σ (h ++ [fun i => σ i h]) := by
  unfold Params.final
  have : P.N - h.length = (P.N - (h ++ [fun i => σ i h]).length) + 1 := by simp; omega
  rw [this]; rfl

theorem X_final_end (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) (h : History P.M)
    (hlen : P.N ≤ h.length) : P.final q0 σ h = level q0 h := by
  unfold Params.final
  have : P.N - h.length = 0 := by omega
  rw [this]; rfl

theorem X_pathHist_zero {M : ℕ} (σ : Profile M) : pathHist σ 0 = [] := rfl

theorem X_pathHist_succ {M : ℕ} (σ : Profile M) (n : ℕ) :
    pathHist σ (n+1) = pathHist σ n ++ [fun i => σ i (pathHist σ n)] :=
  X_play_succ_right σ n []

theorem X_pathHist_length {M : ℕ} (σ : Profile M) (n : ℕ) : (pathHist σ n).length = n := by
  unfold pathHist; rw [X_play_length]; simp

theorem X_sum_ge {M : ℕ} (q0 : Fin M → ℝ) (lo : ℝ) :
    ∀ (h : History M), (∀ a ∈ h, ∀ j, lo ≤ a j) → ∀ j, q0 j + h.length * lo ≤ level q0 h j := by
  intro h
  induction h with
  | nil => intro _ j; simp [level]
  | cons a t ih =>
    intro hh j
    have h1 := hh a (by simp) j
    have h2 := ih (fun b hb => hh b (by simp [hb])) j
    simp only [level, List.map_cons, List.sum_cons, List.length_cons] at *
    push_cast
    nlinarith

theorem X_play_entries {M : ℕ} (σ : Profile M) (lo : ℝ) (hσ : ∀ i h, lo ≤ σ i h) :
    ∀ (k : ℕ) (h : History M), (∀ a ∈ h, ∀ j, lo ≤ a j) → ∀ a ∈ play σ h k, ∀ j, lo ≤ a j
  | 0, h => fun hh => hh
  | k+1, h => fun hh => by
      rw [X_play_succ]
      apply X_play_entries σ lo hσ k
      intro a ha j
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · exact hh a ha j
      · subst ha; exact hσ j h


open Classical

noncomputable def XR (P : Params) (h : History P.M) : ℝ := ((P.N - h.length : ℕ) : ℝ)
noncomputable def XZ (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (j : Fin P.M) : ℝ :=
  level q0 h j + XR P h * (P.qlo / P.N)
noncomputable def XC (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (j : Fin P.M) : ℝ :=
  level q0 h j + XR P h * (P.qhi / P.N)
noncomputable def XL (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) : ℝ :=
  min P.qstar (⨅ j, XC P q0 h j)

noncomputable def XTie (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) : Prop :=
  (P.N - h.length) + 1 ≤ (Finset.univ.filter (fun j : Fin P.M => ∀ k, XZ P q0 h j ≤ XZ P q0 h k)).card

def XReg (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) : Prop :=
  ∀ k, k ≤ h.length → XTie P q0 (h.take k)

noncomputable def XE (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (j : Fin P.M) : ℝ :=
  P.qlo / P.N + (max 0 (XL P q0 h - XZ P q0 h j)) / XR P h

noncomputable def XSig (P : Params) (q0 : Fin P.M → ℝ) : Profile P.M :=
  fun j h => if XReg P q0 h then P.qlo / P.N else XE P q0 h j

theorem X_R_append (P : Params) (h : History P.M) (a : Fin P.M → ℝ) (hl : h.length < P.N) :
    XR P (h ++ [a]) + 1 = XR P h := by
  unfold XR
  have : P.N - (h ++ [a]).length + 1 = P.N - h.length := by simp; omega
  exact_mod_cast this

theorem X_R_ge (P : Params) (h : History P.M) (hl : h.length < P.N) : 1 ≤ XR P h := by
  unfold XR
  have : 1 ≤ P.N - h.length := by omega
  exact_mod_cast this

theorem X_Z_append (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (a : Fin P.M → ℝ)
    (hl : h.length < P.N) (j : Fin P.M) :
    XZ P q0 (h ++ [a]) j = XZ P q0 h j + (a j - P.qlo / P.N) := by
  have := X_R_append P h a hl
  unfold XZ
  rw [X_level_append]
  have e : XR P (h ++ [a]) = XR P h - 1 := by linarith
  rw [e]; ring

theorem X_C_append (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (a : Fin P.M → ℝ)
    (hl : h.length < P.N) (j : Fin P.M) :
    XC P q0 (h ++ [a]) j = XC P q0 h j + (a j - P.qhi / P.N) := by
  have := X_R_append P h a hl
  unfold XC
  rw [X_level_append]
  have e : XR P (h ++ [a]) = XR P h - 1 := by linarith
  rw [e]; ring

theorem X_reg_prefix (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (a : Fin P.M → ℝ) :
    XReg P q0 (h ++ [a]) → XReg P q0 h := by
  intro hr k hk
  have := hr k (by simp; omega)
  rwa [List.take_append_of_le_length hk] at this

theorem X_reg_append (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (a : Fin P.M → ℝ)
    (hr : XReg P q0 h) (ht : XTie P q0 (h ++ [a])) : XReg P q0 (h ++ [a]) := by
  intro k hk
  simp only [List.length_append, List.length_singleton] at hk
  rcases Nat.lt_or_ge k (h.length + 1) with hk' | hk'
  · rw [List.take_append_of_le_length (by omega)]
    exact hr k (by omega)
  · have : k = h.length + 1 := by omega
    subst this
    rw [List.take_of_length_le (by simp)]
    exact ht

theorem X_reg_tie (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (hr : XReg P q0 h) :
    XTie P q0 h := by
  simpa using hr h.length le_rfl

theorem X_tie_append (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (a : Fin P.M → ℝ)
    (i : Fin P.M) (hl : h.length < P.N) (ht : XTie P q0 h)
    (ha : ∀ j, j ≠ i → a j = P.qlo / P.N) (hlo : ∀ j, P.qlo / P.N ≤ a j) :
    XTie P q0 (h ++ [a]) := by
  unfold XTie at *
  set T := Finset.univ.filter (fun j : Fin P.M => ∀ k, XZ P q0 h j ≤ XZ P q0 h k) with hT
  have hsub : T.erase i ⊆ Finset.univ.filter
      (fun j : Fin P.M => ∀ k, XZ P q0 (h ++ [a]) j ≤ XZ P q0 (h ++ [a]) k) := by
    intro j hj
    rw [Finset.mem_erase] at hj
    obtain ⟨hji, hjT⟩ := hj
    rw [hT, Finset.mem_filter] at hjT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    rw [X_Z_append P q0 h a hl, X_Z_append P q0 h a hl, ha j hji]
    have := hjT.2 k
    have := hlo k
    linarith
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.pred_card_le_card_erase (s := T) (a := i)
  have : (h ++ [a]).length = h.length + 1 := by simp
  rw [this]
  omega


theorem X_R_end (P : Params) (h : History P.M) (hl : P.N ≤ h.length) : XR P h = 0 := by
  unfold XR
  have : P.N - h.length = 0 := by omega
  rw [this]; simp

theorem X_lo_play (P : Params) (q0 : Fin P.M → ℝ) (Rg : History P.M → Prop)
    (D : Fin P.M → Prop) (ρ : Profile P.M)
    (hρ : ∀ h, Rg h → ∀ j, ¬ D j → ρ j h = P.qlo / P.N)
    (hlo : ∀ h j, P.qlo / P.N ≤ ρ j h)
    (hcl : ∀ h, Rg h → h.length < P.N → ∀ a : Fin P.M → ℝ,
      (∀ j, ¬ D j → a j = P.qlo / P.N) → (∀ j, P.qlo / P.N ≤ a j) → Rg (h ++ [a])) :
    ∀ (r : ℕ) (h : History P.M), h.length + r = P.N → Rg h → ∀ j,
      XZ P q0 h j ≤ P.final q0 ρ h j ∧ (¬ D j → P.final q0 ρ h j = XZ P q0 h j) := by
  intro r
  induction r with
  | zero =>
    intro h hl hR j
    have hl' : P.N ≤ h.length := by omega
    rw [X_final_end P q0 ρ h hl']
    have : XZ P q0 h j = level q0 h j := by unfold XZ; rw [X_R_end P h hl']; ring
    rw [this]; exact ⟨le_rfl, fun _ => rfl⟩
  | succ r ih =>
    intro h hl hR j
    have hl1 : h.length < P.N := by omega
    rw [X_final_step P q0 ρ h hl1]
    have hR' : Rg (h ++ [fun i => ρ i h]) :=
      hcl h hR hl1 _ (fun j hj => hρ h hR j hj) (fun j => hlo h j)
    have := ih (h ++ [fun i => ρ i h]) (by simp; omega) hR' j
    rw [X_Z_append P q0 h _ hl1] at this
    obtain ⟨h1, h2⟩ := this
    have h3 := hlo h j
    refine ⟨by linarith, fun hj => ?_⟩
    rw [h2 hj, hρ h hR j hj]; ring

/-- profit comparison, tie version -/
theorem X_profit_tie (P : Params) (hP : P.Standing) (x w : Fin P.M → ℝ) (i : Fin P.M)
    (hx : ∀ j, j ≠ i → x j = w j) (hxi : w i ≤ x i)
    (k : Fin P.M) (hk : k ≠ i) (hkm : ∀ l, w k ≤ w l) :
    P.profit x i ≤ P.profit w i := by
  obtain ⟨_, _, _, _, _, hp, hg, hc⟩ := hP
  have : Nonempty (Fin P.M) := ⟨k⟩
  have h1 : projectLevel x = projectLevel w := by
    unfold projectLevel
    have a1 : (⨅ j, w j) = w k := by
      apply le_antisymm (ciInf_le (Set.finite_range w).bddBelow k)
      exact le_ciInf hkm
    have a2 : (⨅ j, x j) = x k := by
      apply le_antisymm (ciInf_le (Set.finite_range x).bddBelow k)
      apply le_ciInf
      intro l
      by_cases hl : l = i
      · subst hl; rw [hx k hk]; exact le_trans (hkm l) hxi
      · rw [hx l hl, hx k hk]; exact hkm l
    rw [a1, a2, hx k hk]
  unfold Params.profit
  rw [h1]
  have := mul_pos hg hp
  nlinarith

theorem X_iInf_le_add {M : ℕ} [Nonempty (Fin M)] (x w : Fin M → ℝ) (i : Fin M)
    (hx : ∀ j, j ≠ i → x j = w j) (hxi : w i ≤ x i) :
    (⨅ j, w j) ≤ (⨅ j, x j) ∧ (⨅ j, x j) ≤ (⨅ j, w j) + (x i - w i) := by
  constructor
  · apply le_ciInf
    intro l
    refine le_trans (ciInf_le (Set.finite_range w).bddBelow l) ?_
    by_cases hl : l = i
    · subst hl; exact hxi
    · rw [hx l hl]
  · obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := w)
    rw [← hk]
    refine le_trans (ciInf_le (Set.finite_range x).bddBelow k) ?_
    by_cases hki : k = i
    · subst hki; linarith
    · rw [hx k hki]; linarith

/-- profit comparison, Lipschitz version -/
theorem X_profit_lip (P : Params) (hP : P.Standing) (hle : P.γ * P.p ≤ P.c)
    (x w : Fin P.M → ℝ) (i : Fin P.M)
    (hx : ∀ j, j ≠ i → x j = w j) (hxi : w i ≤ x i) :
    P.profit x i ≤ P.profit w i := by
  obtain ⟨hM, _, _, _, _, hp, hg, hc⟩ := hP
  have : Nonempty (Fin P.M) := ⟨i⟩
  obtain ⟨b1, b2⟩ := X_iInf_le_add x w i hx hxi
  unfold Params.profit projectLevel
  have e1 : min (⨅ j, x j) P.qstar ≤ min (⨅ j, w j) P.qstar + (x i - w i) := by
    rcases le_total (⨅ j, w j) P.qstar with h | h
    · rw [min_eq_left h]
      exact le_trans (min_le_left _ _) b2
    · rw [min_eq_right h]
      have : 0 ≤ x i - w i := by linarith
      exact le_trans (min_le_right _ _) (by linarith)
  nlinarith [mul_pos hg hp]


theorem X_lo_le_hi (P : Params) (hP : P.Standing) : P.qlo / P.N ≤ P.qhi / P.N := by
  obtain ⟨hM, hN, h0, h1, h2, _⟩ := hP
  have : (0:ℝ) < P.N := by exact_mod_cast hN
  exact div_le_div_of_nonneg_right (by linarith) this.le

theorem X_R_nonneg (P : Params) (h : History P.M) : 0 ≤ XR P h := by
  unfold XR; positivity

theorem X_XL_le_cap (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (j : Fin P.M) :
    XL P q0 h ≤ XC P q0 h j :=
  le_trans (min_le_right _ _) (ciInf_le (Set.finite_range _).bddBelow j)

theorem X_XL_le_q (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) :
    XL P q0 h ≤ P.qstar := min_le_left _ _

/-- the effort increment `u_j` -/
noncomputable def XU (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (j : Fin P.M) : ℝ :=
  (max 0 (XL P q0 h - XZ P q0 h j)) / XR P h

theorem X_U_facts (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (h : History P.M)
    (j : Fin P.M) :
    0 ≤ XU P q0 h j ∧ XU P q0 h j ≤ P.qhi / P.N - P.qlo / P.N := by
  have hR := X_R_nonneg P h
  have hcap : XC P q0 h j - XZ P q0 h j = XR P h * (P.qhi / P.N - P.qlo / P.N) := by
    unfold XC XZ; ring
  have hlh := X_lo_le_hi P hP
  refine ⟨div_nonneg (le_max_left _ _) hR, ?_⟩
  unfold XU
  rcases hR.eq_or_lt with h0 | h0
  · rw [← h0]; simp; linarith
  · rw [div_le_iff₀ h0]
    apply max_le
    · nlinarith
    · have := X_XL_le_cap P q0 h j
      nlinarith

theorem X_U_facts2 (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (hl : h.length < P.N)
    (j : Fin P.M) :
    XL P q0 h ≤ XZ P q0 h j + XR P h * XU P q0 h j ∧
    XZ P q0 h j + XU P q0 h j ≤ max (XZ P q0 h j) (XL P q0 h) := by
  have hR := X_R_ge P h hl
  have hR0 : 0 < XR P h := by linarith
  unfold XU
  rcases le_total (XL P q0 h) (XZ P q0 h j) with hle | hle
  · rw [max_eq_left (by linarith)]
    simp
    exact hle
  · rw [max_eq_right (by linarith)]
    have e : XR P h * ((XL P q0 h - XZ P q0 h j) / XR P h) = XL P q0 h - XZ P q0 h j := by
      field_simp
    have e2 : (XL P q0 h - XZ P q0 h j) / XR P h ≤ XL P q0 h - XZ P q0 h j := by
      rw [div_le_iff₀ hR0]; nlinarith [sub_nonneg.2 hle]
    refine ⟨by linarith, ?_⟩
    rw [max_eq_right hle]; linarith

theorem X_XE_eq (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (j : Fin P.M) :
    XE P q0 h j = P.qlo / P.N + XU P q0 h j := rfl

theorem X_XE_feas (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (h : History P.M)
    (j : Fin P.M) : P.qlo / P.N ≤ XE P q0 h j ∧ XE P q0 h j ≤ P.qhi / P.N := by
  obtain ⟨a, b⟩ := X_U_facts P hP q0 h j
  rw [X_XE_eq]; constructor <;> linarith

theorem X_sig_feas (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (j : Fin P.M) :
    P.FeasibleStrategy (XSig P q0 j) := by
  intro h
  unfold XSig
  split_ifs
  · exact ⟨le_rfl, X_lo_le_hi P hP⟩
  · exact X_XE_feas P hP q0 h j

/-- one-step: target does not increase under unilateral deviation -/
theorem X_L_dev (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (h : History P.M)
    (hl : h.length < P.N) (a : Fin P.M → ℝ) (i : Fin P.M)
    (ha : ∀ j, j ≠ i → a j = XE P q0 h j) (hai : a i ≤ P.qhi / P.N) :
    XL P q0 (h ++ [a]) ≤ XL P q0 h := by
  have hR := X_R_ge P h hl
  have hR0 : 0 < XR P h := by linarith
  haveI : Nonempty (Fin P.M) := ⟨⟨0, by obtain ⟨hM, _⟩ := hP; omega⟩⟩
  unfold XL
  apply le_min (min_le_left _ _)
  by_cases hq : P.qstar ≤ ⨅ j, XC P q0 h j
  · exact le_trans (min_le_left _ _) hq
  · rw [not_le] at hq
    obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := fun j => XC P q0 h j)
    have hLk : XL P q0 h = XC P q0 h k := by
      unfold XL; rw [min_eq_right hq.le]; exact hk.symm
    have hk' : XC P q0 (h ++ [a]) k ≤ XC P q0 h k := by
      rw [X_C_append P q0 h a hl]
      by_cases hki : k = i
      · subst hki; linarith
      · rw [ha k hki, X_XE_eq]
        have hu : XU P q0 h k = P.qhi / P.N - P.qlo / P.N := by
          unfold XU
          rw [hLk]
          have hcap : XC P q0 h k - XZ P q0 h k = XR P h * (P.qhi / P.N - P.qlo / P.N) := by
            unfold XC XZ; ring
          have hpos : 0 ≤ XR P h * (P.qhi / P.N - P.qlo / P.N) :=
            mul_nonneg hR0.le (sub_nonneg.2 (X_lo_le_hi P hP))
          rw [hcap, max_eq_right hpos]
          field_simp
        rw [hu]; linarith
    refine le_trans (min_le_right _ _) ?_
    calc ⨅ j, XC P q0 (h ++ [a]) j ≤ XC P q0 (h ++ [a]) k :=
          ciInf_le (Set.finite_range _).bddBelow k
      _ ≤ XC P q0 h k := hk'
      _ = ⨅ j, XC P q0 h j := hk


theorem X_L_follow (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (h : History P.M)
    (hl : h.length < P.N) (a : Fin P.M → ℝ) (ha : ∀ j, a j = XE P q0 h j) :
    XL P q0 (h ++ [a]) = XL P q0 h := by
  have hR := X_R_ge P h hl
  have i0 : Fin P.M := ⟨0, by obtain ⟨hM, _⟩ := hP; omega⟩
  have : Nonempty (Fin P.M) := ⟨i0⟩
  apply le_antisymm
  · exact X_L_dev P hP q0 h hl a i0 (fun j _ => ha j) (by rw [ha]; exact (X_XE_feas P hP q0 h i0).2)
  · show XL P q0 h ≤ min P.qstar (⨅ j, XC P q0 (h ++ [a]) j)
    refine le_min (X_XL_le_q P q0 h) (le_ciInf fun j => ?_)
    rw [X_C_append P q0 h a hl, ha j, X_XE_eq]
    obtain ⟨u0, u1⟩ := X_U_facts P hP q0 h j
    obtain ⟨k1, _⟩ := X_U_facts2 P q0 h hl j
    have e : XC P q0 h j = XZ P q0 h j + XR P h * (P.qhi / P.N - P.qlo / P.N) := by
      unfold XC XZ; ring
    rw [e]
    nlinarith [mul_nonneg (sub_nonneg.2 hR) (sub_nonneg.2 u1)]

theorem X_max_follow (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (h : History P.M)
    (hl : h.length < P.N) (a : Fin P.M → ℝ) (ha : ∀ j, a j = XE P q0 h j) (j : Fin P.M) :
    max (XZ P q0 (h ++ [a]) j) (XL P q0 (h ++ [a])) = max (XZ P q0 h j) (XL P q0 h) := by
  rw [X_L_follow P hP q0 h hl a ha, X_Z_append P q0 h a hl, ha j, X_XE_eq]
  obtain ⟨u0, u1⟩ := X_U_facts P hP q0 h j
  obtain ⟨_, k3⟩ := X_U_facts2 P q0 h hl j
  apply le_antisymm
  · apply max_le _ (le_max_right _ _)
    linarith
  · apply max_le_max _ le_rfl
    linarith

noncomputable def XV (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (i : Fin P.M) : ℝ :=
  P.γ * (P.p * XL P q0 h) - P.c * max (XZ P q0 h i) (XL P q0 h)

theorem X_terminal (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) (h : History P.M)
    (hl : P.N ≤ h.length) (i : Fin P.M) :
    P.profit (P.final q0 σ h) i = XV P q0 h i := by
  rw [X_final_end P q0 σ h hl]
  have e1 : XC P q0 h = level q0 h := by
    funext j; unfold XC; rw [X_R_end P h hl]; ring
  have e2 : XZ P q0 h = level q0 h := by
    funext j; unfold XZ; rw [X_R_end P h hl]; ring
  unfold Params.profit projectLevel XV XL
  rw [e1, e2, min_comm]
  have : min P.qstar (⨅ j, level q0 h j) ≤ level q0 h i := by
    refine le_trans (min_le_right _ _) ?_
    exact ciInf_le (Set.finite_range _).bddBelow i
  rw [max_eq_left this]

theorem X_g_mono (P : Params) (hP : P.Standing) (hc : P.c ≤ P.γ * P.p) (z t s : ℝ) (hts : t ≤ s) :
    P.γ * (P.p * t) - P.c * max z t ≤ P.γ * (P.p * s) - P.c * max z s := by
  obtain ⟨_, _, _, _, _, hp, hg, hc0⟩ := hP
  have h1 : max z s - max z t ≤ s - t := by
    rcases le_total z t with h | h <;> rcases le_total z s with h' | h' <;>
      simp [*] <;> linarith
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hts), mul_le_mul_of_nonneg_left h1 hc0.le]

theorem X_E_main (P : Params) (hP : P.Standing) (hc : P.c ≤ P.γ * P.p) (q0 : Fin P.M → ℝ) :
    ∀ (r : ℕ) (h : History P.M), h.length + r = P.N → ¬ XReg P q0 h →
      (∀ i, P.profit (P.final q0 (XSig P q0) h) i = XV P q0 h i) ∧
      (∀ (i : Fin P.M) (τ : History P.M → ℝ), P.FeasibleStrategy τ →
        P.profit (P.final q0 (Function.update (XSig P q0) i τ) h) i ≤ XV P q0 h i) := by
  intro r
  induction r with
  | zero =>
    intro h hl hnr
    have hl' : P.N ≤ h.length := by omega
    exact ⟨fun i => X_terminal P q0 _ h hl' i, fun i τ _ => (X_terminal P q0 _ h hl' i).le⟩
  | succ r ih =>
    intro h hl hnr
    have hl1 : h.length < P.N := by omega
    have hlen : (h ++ [fun j => XE P q0 h j]).length + r = P.N := by simp; omega
    have sig_eq : ∀ j, XSig P q0 j h = XE P q0 h j := by
      intro j; simp [XSig, hnr]
    constructor
    · intro i
      have hs : (fun j => XSig P q0 j h) = fun j => XE P q0 h j := funext sig_eq
      rw [X_final_step P q0 _ h hl1, hs]
      have hnr' : ¬ XReg P q0 (h ++ [fun j => XE P q0 h j]) := fun hh => hnr (X_reg_prefix P q0 _ _ hh)
      have := (ih _ hlen hnr').1 i
      rw [this]
      unfold XV
      have hm := X_max_follow P hP q0 h hl1 (fun j => XE P q0 h j) (fun j => rfl) i
      rw [X_L_follow P hP q0 h hl1 (fun j => XE P q0 h j) (fun j => rfl)] at hm ⊢
      rw [hm]
    · intro i τ hτ
      set ρ := Function.update (XSig P q0) i τ with hρ
      have hs : ∀ j, j ≠ i → ρ j h = XE P q0 h j := by
        intro j hj; rw [hρ, Function.update_of_ne hj]; exact sig_eq j
      have hsi : ρ i h = τ h := by rw [hρ]; simp
      rw [X_final_step P q0 _ h hl1]
      set a : Fin P.M → ℝ := fun j => ρ j h with ha
      have hnr' : ¬ XReg P q0 (h ++ [a]) := fun hh => hnr (X_reg_prefix P q0 _ _ hh)
      have hlen' : (h ++ [a]).length + r = P.N := by simp; omega
      have := (ih _ hlen' hnr').2 i τ hτ
      refine le_trans this ?_
      have hai : a i = τ h := hsi
      have hL := X_L_dev P hP q0 h hl1 a i (fun j hj => hs j hj) (by rw [hai]; exact (hτ h).2)
      have hZ : XZ P q0 h i ≤ XZ P q0 (h ++ [a]) i := by
        rw [X_Z_append P q0 h a hl1, hai]
        have := (hτ h).1
        linarith
      unfold XV
      calc P.γ * (P.p * XL P q0 (h ++ [a])) - P.c * max (XZ P q0 (h ++ [a]) i) (XL P q0 (h ++ [a]))
          ≤ P.γ * (P.p * XL P q0 (h ++ [a])) - P.c * max (XZ P q0 h i) (XL P q0 (h ++ [a])) := by
            have := max_le_max_right (XL P q0 (h ++ [a])) hZ
            have hc0 := hP.2.2.2.2.2.2.2
            nlinarith
        _ ≤ _ := X_g_mono P hP hc _ _ _ hL


theorem X_lo_cmp (P : Params) (q0 : Fin P.M → ℝ) (Rg : History P.M → Prop) (σ : Profile P.M)
    (i : Fin P.M) (τ : History P.M → ℝ) (hτ : P.FeasibleStrategy τ)
    (hσlo : ∀ h, Rg h → ∀ j, σ j h = P.qlo / P.N)
    (hσfeas : ∀ j, P.FeasibleStrategy (σ j))
    (hcl : ∀ (i0 : Fin P.M) (h : History P.M), Rg h → h.length < P.N → ∀ a : Fin P.M → ℝ,
      (∀ j, j ≠ i0 → a j = P.qlo / P.N) → (∀ j, P.qlo / P.N ≤ a j) → Rg (h ++ [a]))
    (h : History P.M) (hh : h.length < P.N) (hR : Rg h) :
    (∀ j, j ≠ i → P.final q0 (Function.update σ i τ) h j = P.final q0 σ h j) ∧
      P.final q0 σ h i ≤ P.final q0 (Function.update σ i τ) h i := by
  have hr : h.length + (P.N - h.length) = P.N := by omega
  have A := X_lo_play P q0 Rg (fun j => j = i) (Function.update σ i τ)
    (fun h hR j hj => by rw [Function.update_of_ne hj]; exact hσlo h hR j)
    (fun h j => by
      by_cases hj : j = i
      · subst hj; simp; exact (hτ h).1
      · rw [Function.update_of_ne hj]; exact (hσfeas j h).1)
    (fun h hR hl a ha hb => hcl i h hR hl a ha hb) (P.N - h.length) h hr hR
  have B := X_lo_play P q0 Rg (fun _ => False) σ
    (fun h hR j _ => hσlo h hR j)
    (fun h j => (hσfeas j h).1)
    (fun h hR hl a ha hb => hcl i h hR hl a (fun j _ => ha j not_false) hb) (P.N - h.length) h hr hR
  constructor
  · intro j hj
    rw [(A j).2 hj, (B j).2 not_false]
  · have := (A i).1
    rw [(B i).2 not_false]; exact this

theorem X_tie_init (P : Params) (q0 : Fin P.M → ℝ) (S : Finset (Fin P.M))
    (hS : P.N + 1 ≤ S.card) (hmin : ∀ i ∈ S, ∀ j, q0 i ≤ q0 j) : XTie P q0 [] := by
  unfold XTie
  have hsub : S ⊆ Finset.univ.filter (fun j => ∀ k, XZ P q0 [] j ≤ XZ P q0 [] k) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k
    unfold XZ; rw [X_level_nil, X_level_nil]
    have := hmin j hj k
    linarith
  have := Finset.card_le_card hsub
  simp only [List.length_nil, Nat.sub_zero]
  omega

theorem X_reg_nil (P : Params) (q0 : Fin P.M → ℝ) (ht : XTie P q0 []) : XReg P q0 [] := by
  intro k hk
  simp at hk
  subst hk
  simpa using ht

theorem X_tie_other (P : Params) (q0 : Fin P.M → ℝ) (h : History P.M) (hl : h.length < P.N)
    (ht : XTie P q0 h) (i : Fin P.M) : ∃ k, k ≠ i ∧ ∀ l, XZ P q0 h k ≤ XZ P q0 h l := by
  unfold XTie at ht
  set T := Finset.univ.filter (fun j : Fin P.M => ∀ k, XZ P q0 h j ≤ XZ P q0 h k) with hT
  have h1 := Finset.pred_card_le_card_erase (s := T) (a := i)
  have h2 : 0 < (T.erase i).card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.1 h2
  rw [Finset.mem_erase, hT, Finset.mem_filter] at hk
  exact ⟨k, hk.1, hk.2.2⟩

theorem X_exists (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M) (q0 : Fin P.M → ℝ)
    (htie : ∃ S : Finset (Fin P.M), P.N + 1 ≤ S.card ∧ ∀ i ∈ S, ∀ j, q0 i ≤ q0 j) :
    ∃ σ : Profile P.M, P.IsSPE q0 σ ∧
      ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N := by
  obtain ⟨S, hS, hmin⟩ := htie
  have hlh := X_lo_le_hi P hP
  rcases le_total (P.γ * P.p) P.c with hle | hge
  · -- all-minimum profile
    refine ⟨fun _ _ => P.qlo / P.N, ⟨fun i h => ⟨le_rfl, hlh⟩, ?_⟩, fun n _ i => rfl⟩
    intro h hfh i τ hτ
    have hh := hfh.1
    obtain ⟨c1, c2⟩ := X_lo_cmp P q0 (fun _ => True) (fun _ _ => P.qlo / P.N) i τ hτ
      (fun _ _ _ => rfl) (fun j h => ⟨le_rfl, hlh⟩) (fun _ _ _ _ _ _ _ => trivial) h hh trivial
    exact X_profit_lip P hP hle _ _ i c1 c2
  · -- regime profile
    have hfeas := X_sig_feas P hP q0
    have hreg_nil := X_reg_nil P q0 (X_tie_init P q0 S hS hmin)
    have hsiglo : ∀ h, XReg P q0 h → ∀ j, XSig P q0 j h = P.qlo / P.N := by
      intro h hR j; simp [XSig, hR]
    have hcl : ∀ (i0 : Fin P.M) (h : History P.M), XReg P q0 h → h.length < P.N →
        ∀ a : Fin P.M → ℝ, (∀ j, j ≠ i0 → a j = P.qlo / P.N) → (∀ j, P.qlo / P.N ≤ a j) →
          XReg P q0 (h ++ [a]) := by
      intro i0 h hR hl a ha hb
      exact X_reg_append P q0 h a hR (X_tie_append P q0 h a i0 hl (X_reg_tie P q0 h hR) ha hb)
    refine ⟨XSig P q0, ⟨hfeas, ?_⟩, ?_⟩
    · intro h hfh i τ hτ
      have hh := hfh.1
      by_cases hR : XReg P q0 h
      · obtain ⟨c1, c2⟩ := X_lo_cmp P q0 (XReg P q0) (XSig P q0) i τ hτ hsiglo hfeas hcl h hh hR
        obtain ⟨k, hki, hk⟩ := X_tie_other P q0 h hh (X_reg_tie P q0 h hR) i
        -- final σ h = XZ h
        have hr : h.length + (P.N - h.length) = P.N := by omega
        have B := X_lo_play P q0 (XReg P q0) (fun _ => False) (XSig P q0)
          (fun h hR j _ => hsiglo h hR j) (fun h j => (hfeas j h).1)
          (fun h hR hl a ha hb => hcl i h hR hl a (fun j _ => ha j not_false) hb)
          (P.N - h.length) h hr hR
        have hw : ∀ l, P.final q0 (XSig P q0) h l = XZ P q0 h l := fun l => (B l).2 not_false
        exact X_profit_tie P hP _ _ i c1 c2 k hki (fun l => by rw [hw k, hw l]; exact hk l)
      · have hr : h.length + (P.N - h.length) = P.N := by omega
        obtain ⟨e1, e2⟩ := X_E_main P hP hge q0 (P.N - h.length) h hr hR
        have := e2 i τ hτ
        rw [e1 i]; exact this
    · -- on-path values
      have hpath : ∀ n, n ≤ P.N → XReg P q0 (pathHist (XSig P q0) n) := by
        intro n
        induction n with
        | zero => intro _; exact hreg_nil
        | succ n ih =>
          intro hn
          have hR := ih (by omega)
          have hl : (pathHist (XSig P q0) n).length < P.N := by rw [X_pathHist_length]; omega
          rw [X_pathHist_succ]
          apply hcl ⟨0, by obtain ⟨hM, _⟩ := hP; omega⟩ _ hR hl
          · intro j _; exact hsiglo _ hR j
          · intro j; rw [hsiglo _ hR j]
      intro n hn i
      exact hsiglo _ (hpath n hn.le) i

end AssemblyCoord.Feedback

open AssemblyCoord.Feedback

theorem solution (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M)
    (q0 : Fin P.M → ℝ)
    (htie : ∃ S : Finset (Fin P.M), P.N + 1 ≤ S.card ∧ ∀ i ∈ S, ∀ j, q0 i ≤ q0 j) :
    ∃ σ : Profile P.M, P.IsSPE q0 σ ∧
      ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N :=
  X_exists P hP hN q0 htie
