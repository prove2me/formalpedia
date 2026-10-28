-- Prove2me | solution 1 for AssemblyCoord.Feedback.proposition_2_i
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T01:04:16.652418+00:00
-- url     : https://prove2.me/submissions/355a2a21-d786-4d80-a408-2457cba1d3ac

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


theorem X_path_level {M : ℕ} (q0 : Fin M → ℝ) (σ : Profile M) (i : Fin M) (n : ℕ) :
    level q0 (pathHist σ n) i = q0 i + ∑ m ∈ Finset.range n, σ i (pathHist σ m) := by
  induction n with
  | zero => simp [X_pathHist_zero, X_level_nil]
  | succ n ih => rw [X_pathHist_succ, X_level_append, ih, Finset.sum_range_succ]; ring

theorem X_path_entries {M : ℕ} (σ : Profile M) (lo : ℝ) (N : ℕ)
    (hpath : ∀ m, m < N → ∀ j, σ j (pathHist σ m) = lo) :
    ∀ n, n ≤ N → ∀ a ∈ pathHist σ n, ∀ j, a j = lo := by
  intro n
  induction n with
  | zero => intro _ a ha; simp [X_pathHist_zero] at ha
  | succ n ih =>
    intro hn a ha j
    rw [X_pathHist_succ] at ha
    simp only [List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | ha
    · exact ih (by omega) a ha j
    · subst ha; exact hpath n (by omega) j

theorem X_N_mul (P : Params) (hN : 1 ≤ P.N) : (P.N : ℝ) * (P.qlo / P.N) = P.qlo := by
  have : (P.N : ℝ) ≠ 0 := by positivity
  field_simp

theorem X_path_final (P : Params) (hN : 1 ≤ P.N) (q0 : Fin P.M → ℝ) (σ : Profile P.M)
    (hpath : ∀ n, n < P.N → ∀ j, σ j (pathHist σ n) = P.qlo / P.N)
    (n : ℕ) (hn : n ≤ P.N) (j : Fin P.M) :
    P.final q0 σ (pathHist σ n) j = q0 j + P.qlo := by
  unfold Params.final
  rw [X_pathHist_length]
  have e : pathHist σ n = play σ [] n := rfl
  rw [e, X_play_add]
  have e2 : n + (P.N - n) = P.N := by omega
  rw [e2]
  have e3 : play σ [] P.N = pathHist σ P.N := rfl
  rw [e3]
  rw [X_path_level q0 σ j P.N]
  rw [Finset.sum_congr rfl (fun m hm => hpath m (Finset.mem_range.1 hm) j)]
  simp [X_N_mul P hN]

theorem X_final_ge (P : Params) (hN : 1 ≤ P.N) (q0 : Fin P.M → ℝ) (σ : Profile P.M)
    (hσ : ∀ j h, P.qlo / P.N ≤ σ j h) (h : History P.M) (hh : h.length ≤ P.N)
    (hent : ∀ a ∈ h, ∀ j, P.qlo / P.N ≤ a j) (j : Fin P.M) :
    q0 j + P.qlo ≤ P.final q0 σ h j := by
  unfold Params.final
  have e : h.length + (P.N - h.length) = P.N := by omega
  have h2 : ((P.N : ℕ) : ℝ) * (P.qlo / P.N) = P.qlo := X_N_mul P hN
  have h3 := X_sum_ge q0 (P.qlo / P.N) (play σ h (P.N - h.length))
    (X_play_entries σ _ hσ _ h hent) j
  rw [X_play_length, e] at h3
  linarith

theorem X_sum_const {M : ℕ} (q0 : Fin M → ℝ) (i : Fin M) (c : ℝ) :
    ∀ (l : History M), (∀ a ∈ l, a i = c) → level q0 l i = q0 i + l.length * c := by
  intro l
  induction l with
  | nil => intro _; simp [level]
  | cons a t ih =>
    intro hh
    have h1 := hh a (by simp)
    have h2 := ih (fun b hb => hh b (by simp [hb]))
    simp only [level, List.map_cons, List.sum_cons, List.length_cons] at *
    push_cast
    rw [h1]
    linarith

theorem X_play_comp {M : ℕ} (σ : Profile M) (i : Fin M) (c : ℝ) (hσ : ∀ h, σ i h = c) :
    ∀ (k : ℕ) (h : History M), (∀ a ∈ h, a i = c) → ∀ a ∈ play σ h k, a i = c
  | 0, h => fun hh => hh
  | k+1, h => fun hh => by
      rw [X_play_succ]
      apply X_play_comp σ i c hσ k
      intro a ha
      simp only [List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | ha
      · exact hh a ha
      · subst ha; exact hσ h

theorem X_final_dev_i (P : Params) (hN : 1 ≤ P.N) (q0 : Fin P.M → ℝ) (σ : Profile P.M)
    (i : Fin P.M) (h : History P.M) (hh : h.length ≤ P.N)
    (hent : ∀ a ∈ h, a i = P.qlo / P.N) :
    P.final q0 (Function.update σ i (fun _ => P.qlo / P.N)) h i = q0 i + P.qlo := by
  unfold Params.final
  have hc := X_play_comp (Function.update σ i (fun _ => P.qlo / P.N)) i (P.qlo / P.N)
    (fun h => by simp) (P.N - h.length) h hent
  rw [X_sum_const q0 i _ _ hc, X_play_length]
  have e : h.length + (P.N - h.length) = P.N := by omega
  rw [e]
  have h2 : ((P.N : ℕ) : ℝ) * (P.qlo / P.N) = P.qlo := X_N_mul P hN
  rw [h2]

theorem X_feas_update (P : Params) (σ : Profile P.M) (hσ : ∀ j, P.FeasibleStrategy (σ j))
    (i : Fin P.M) (τ : History P.M → ℝ) (hτ : P.FeasibleStrategy τ) (j : Fin P.M) :
    P.FeasibleStrategy (Function.update σ i τ j) := by
  by_cases hj : j = i
  · subst hj; simpa using hτ
  · rw [Function.update_of_ne hj]; exact hσ j

theorem X_proj_eq {M : ℕ} (x : Fin M → ℝ) (c : ℝ) (hx : ∀ j, c ≤ x j) (i : Fin M) (hi : x i = c) :
    projectLevel x = c := by
  unfold projectLevel
  apply le_antisymm
  · rw [← hi]; exact ciInf_le (Set.finite_range _).bddBelow i
  · haveI : Nonempty (Fin M) := ⟨i⟩
    exact le_ciInf hx

theorem X_path_sum_lo (P : Params) (σ : Profile P.M) (i : Fin P.M)
    (hf : ∀ m, P.qlo / P.N ≤ σ i (pathHist σ m)) (hsum : ∑ m ∈ Finset.range P.N, σ i (pathHist σ m) = P.qlo) :
    ∀ n, n < P.N → σ i (pathHist σ n) = P.qlo / P.N := by
  intro n hn
  have hN : 1 ≤ P.N := by omega
  have hsum' : ∑ m ∈ Finset.range P.N, (P.qlo / (P.N:ℝ)) = ∑ m ∈ Finset.range P.N, σ i (pathHist σ m) := by
    rw [hsum]
    simp [X_N_mul P hN]
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.range P.N) (f := fun _ => P.qlo / (P.N:ℝ))
    (g := fun m => σ i (pathHist σ m)) (fun m _ => hf m)).1 hsum' n (Finset.mem_range.2 hn)
  exact this.symm


theorem X_final_root (P : Params) (q0 : Fin P.M → ℝ) (σ : Profile P.M) (i : Fin P.M) :
    P.final q0 σ [] i = q0 i + ∑ m ∈ Finset.range P.N, σ i (pathHist σ m) := by
  unfold Params.final
  simp only [List.length_nil, Nat.sub_zero]
  exact X_path_level q0 σ i P.N

theorem X_profit_lo (P : Params) (hP : P.Standing) (x : Fin P.M → ℝ) (i : Fin P.M)
    (hx : ∀ j, P.qlo ≤ x j) (hi : x i = P.qlo) :
    P.profit x i = P.γ * (P.p * P.qlo) - P.c * P.qlo := by
  obtain ⟨_, _, _, h1, _⟩ := hP
  unfold Params.profit
  rw [X_proj_eq x P.qlo hx i hi, min_eq_left h1.le, hi]

theorem X_zero_apply (P : Params) (j : Fin P.M) : (0 : Fin P.M → ℝ) j = 0 := rfl

theorem X_min_profit (P : Params) (hP : P.Standing) (σ : Profile P.M)
    (hpath : ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) :
    ∀ n, n < P.N → ∀ σ' : Profile P.M, P.IsSPE 0 σ' → ∀ i : Fin P.M,
      P.profit (P.final 0 σ (pathHist σ n)) i ≤ P.profit (P.final 0 σ' (pathHist σ n)) i := by
  intro n hn σ' hσ' i
  have hN : 1 ≤ P.N := hP.2.1
  have hlh := X_lo_le_hi P hP
  have hent := X_path_entries σ (P.qlo / P.N) P.N hpath n hn.le
  have hfh : P.FeasibleHistory (pathHist σ n) :=
    ⟨by rw [X_pathHist_length]; exact hn,
     fun a ha j => by rw [hent a ha j]; exact ⟨le_rfl, hlh⟩⟩
  have hτ : P.FeasibleStrategy (fun _ => P.qlo / P.N) := fun h => ⟨le_rfl, hlh⟩
  have hdev := hσ'.2 _ hfh i (fun _ => P.qlo / P.N) hτ
  have hρf := X_feas_update P σ' hσ'.1 i _ hτ
  have hlen : (pathHist σ n).length ≤ P.N := by rw [X_pathHist_length]; exact hn.le
  have low : ∀ j, P.qlo ≤ P.final 0 (Function.update σ' i (fun _ => P.qlo / P.N)) (pathHist σ n) j := by
    intro j
    have := X_final_ge P hN 0 _ (fun j h => (hρf j h).1) _ hlen (fun a ha j => (hent a ha j).ge) j
    simpa [X_zero_apply] using this
  have ldev : P.final 0 (Function.update σ' i (fun _ => P.qlo / P.N)) (pathHist σ n) i = P.qlo := by
    have := X_final_dev_i P hN 0 σ' i _ hlen (fun a ha => hent a ha i)
    simpa [X_zero_apply] using this
  have e1 := X_profit_lo P hP _ i low ldev
  have e2 := X_profit_lo P hP (P.final 0 σ (pathHist σ n)) i
    (fun j => by rw [X_path_final P hN 0 σ hpath n hn.le j]; simp [X_zero_apply])
    (by rw [X_path_final P hN 0 σ hpath n hn.le i]; simp [X_zero_apply])
  rw [e2, ← e1]; exact hdev

theorem X_best_response (P : Params) (hP : P.Standing) (σ : Profile P.M) (hσ : P.IsSPE 0 σ)
    (j : Fin P.M) (hj : ∀ n, n < P.N → σ j (pathHist σ n) = P.qlo / P.N) :
    ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N := by
  have hN : 1 ≤ P.N := hP.2.1
  have hlh := X_lo_le_hi P hP
  have hc := hP.2.2.2.2.2.2.2
  have hσf : ∀ i h, P.qlo / P.N ≤ σ i h := fun i h => (hσ.1 i h).1
  have xj : P.final 0 σ [] j = P.qlo := by
    rw [X_final_root, Finset.sum_congr rfl (fun m hm => hj m (Finset.mem_range.1 hm))]
    simp [X_N_mul P hN, X_zero_apply]
  have xge : ∀ l, P.qlo ≤ P.final 0 σ [] l := by
    intro l
    have := X_final_ge P hN 0 σ hσf [] (by simp) (by simp) l
    simpa [X_zero_apply] using this
  have proj : projectLevel (P.final 0 σ []) = P.qlo := X_proj_eq _ _ xge j xj
  have hfh : P.FeasibleHistory ([] : History P.M) := ⟨by simp; omega, by simp⟩
  have hτ : P.FeasibleStrategy (fun _ => P.qlo / P.N) := fun h => ⟨le_rfl, hlh⟩
  intro n hn i
  have hdev := hσ.2 _ hfh i (fun _ => P.qlo / P.N) hτ
  have hρf := X_feas_update P σ hσ.1 i _ hτ
  have low : ∀ l, P.qlo ≤ P.final 0 (Function.update σ i (fun _ => P.qlo / P.N)) [] l := by
    intro l
    have := X_final_ge P hN 0 _ (fun j h => (hρf j h).1) [] (by simp) (by simp) l
    simpa [X_zero_apply] using this
  have ldev : P.final 0 (Function.update σ i (fun _ => P.qlo / P.N)) [] i = P.qlo := by
    have := X_final_dev_i P hN 0 σ i [] (by simp) (by simp)
    simpa [X_zero_apply] using this
  have e1 := X_profit_lo P hP _ i low ldev
  have hxi : P.final 0 σ [] i = P.qlo := by
    have hprof : P.profit (P.final 0 σ []) i = P.γ * (P.p * P.qlo) - P.c * P.final 0 σ [] i := by
      unfold Params.profit
      rw [proj, min_eq_left hP.2.2.2.1.le]
    rw [hprof, e1] at hdev
    have := xge i
    exact le_antisymm (by nlinarith) this
  rw [X_final_root] at hxi
  apply X_path_sum_lo P σ i (fun m => hσf i _)
  simpa [X_zero_apply] using hxi
  exact hn


theorem X_profit_update_ge (P : Params) (hP : P.Standing) (x : Fin P.M → ℝ)
    (hx : ∀ j, P.qlo ≤ x j) (i : Fin P.M) (y : ℝ) (hy : P.qlo ≤ y) :
    P.γ * (P.p * P.qlo) - P.c * y ≤ P.profit (Function.update x i y) i := by
  obtain ⟨_, _, _, h1, _, hp, hg, hc⟩ := hP
  haveI : Nonempty (Fin P.M) := ⟨i⟩
  unfold Params.profit projectLevel
  have e1 : P.qlo ≤ ⨅ j, Function.update x i y j := by
    apply le_ciInf
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hy
    · rw [Function.update_of_ne hj]; exact hx j
  have e2 : P.qlo ≤ min (⨅ j, Function.update x i y j) P.qstar := le_min e1 h1.le
  have := mul_pos hg hp
  simp only [Function.update_self]
  nlinarith

theorem X_sv_ge (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (h : History P.M)
    (i : Fin P.M) (y : ℝ)
    (hΩ : ∀ x ∈ P.SPEOutcomes q0 h, ∀ j, P.qlo ≤ x j)
    (hne : (P.SPEOutcomes q0 h).Nonempty) (hy : P.qlo ≤ y) :
    P.γ * (P.p * P.qlo) - P.c * y ≤ P.secureValue q0 h i y := by
  unfold Params.secureValue
  apply le_csInf (hne.image _)
  rintro _ ⟨x, hx, rfl⟩
  exact X_profit_update_ge P hP x (hΩ x hx) i y hy

theorem X_sv_le (P : Params) (hP : P.Standing) (q0 : Fin P.M → ℝ) (h : History P.M)
    (i : Fin P.M) (y : ℝ)
    (hΩ : ∀ x ∈ P.SPEOutcomes q0 h, ∀ j, P.qlo ≤ x j)
    (hmem : (fun _ => P.qlo) ∈ P.SPEOutcomes q0 h) (hy : P.qlo ≤ y)
    (j0 : Fin P.M) (hj0 : j0 ≠ i) :
    P.secureValue q0 h i y ≤ P.γ * (P.p * P.qlo) - P.c * y := by
  unfold Params.secureValue
  have hbdd : BddBelow ((fun x => P.profit (Function.update x i y) i) '' P.SPEOutcomes q0 h) := by
    refine ⟨P.γ * (P.p * P.qlo) - P.c * y, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact X_profit_update_ge P hP x (hΩ x hx) i y hy
  refine le_trans (csInf_le hbdd (Set.mem_image_of_mem _ hmem)) (le_of_eq ?_)
  obtain ⟨_, _, _, h1, _⟩ := hP
  have hproj : projectLevel (Function.update (fun _ : Fin P.M => P.qlo) i y) = P.qlo := by
    apply X_proj_eq _ _ _ j0
    · rw [Function.update_of_ne hj0]
    · intro j
      by_cases hj : j = i
      · subst hj; simpa using hy
      · rw [Function.update_of_ne hj]
  unfold Params.profit
  rw [hproj, min_eq_left h1.le]
  simp

theorem X_outcome_ge (P : Params) (hP : P.Standing) (h : History P.M) (hh : h.length ≤ P.N)
    (hent : ∀ a ∈ h, ∀ j, P.qlo / P.N ≤ a j) :
    ∀ x ∈ P.SPEOutcomes 0 h, ∀ j, P.qlo ≤ x j := by
  rintro x ⟨σ', hσ', rfl⟩ j
  have := X_final_ge P hP.2.1 0 σ' (fun j h => (hσ'.1 j h).1) h hh hent j
  simpa [X_zero_apply] using this

theorem X_goal (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M) :
    (∃ σ : Profile P.M, P.IsSPSE 0 σ ∧
        ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
    (∀ σ : Profile P.M, P.IsSPSE 0 σ →
        (∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
        projectLevel (P.final 0 σ []) = P.qlo) := by
  have hN1 : 1 ≤ P.N := hP.2.1
  have hc := hP.2.2.2.2.2.2.2
  have hq := hP.2.2.2.1
  have : Nontrivial (Fin P.M) := Fin.nontrivial_iff_two_le.2 (by omega)
  obtain ⟨σ0, hσ0, hpath0⟩ := X_exists P hP hN 0
    ⟨Finset.univ, by simp; omega, fun i _ j => le_rfl⟩
  have fin0 : ∀ n, n ≤ P.N → ∀ j, P.final 0 σ0 (pathHist σ0 n) j = P.qlo := by
    intro n hn j
    have := X_path_final P hN1 0 σ0 hpath0 n hn j
    simpa [X_zero_apply] using this
  have ent0 : ∀ n, n ≤ P.N → ∀ a ∈ pathHist σ0 n, ∀ j, P.qlo / P.N ≤ a j := by
    intro n hn a ha j
    exact (X_path_entries σ0 (P.qlo / P.N) P.N hpath0 n hn a ha j).ge
  have mem0 : ∀ n, n ≤ P.N → (fun _ => P.qlo) ∈ P.SPEOutcomes 0 (pathHist σ0 n) := by
    intro n hn
    exact ⟨σ0, hσ0, funext (fin0 n hn)⟩
  constructor
  · refine ⟨σ0, ⟨hσ0, ?_⟩, hpath0⟩
    intro n hn i y hy
    have hΩ := X_outcome_ge P hP (pathHist σ0 n) (by rw [X_pathHist_length]; omega) (ent0 n hn.le)
    have hne : (P.SPEOutcomes 0 (pathHist σ0 n)).Nonempty := ⟨_, mem0 n hn.le⟩
    obtain ⟨x, hx, rfl⟩ := hy
    have hxy := hΩ x hx i
    obtain ⟨j0, hj0⟩ := exists_ne i
    have A := X_sv_le P hP 0 (pathHist σ0 n) i (x i) hΩ (mem0 n hn.le) hxy j0 hj0
    rw [fin0 n hn.le i]
    have B := X_sv_ge P hP 0 (pathHist σ0 n) i P.qlo hΩ hne le_rfl
    nlinarith
  · intro σ hσ
    have hσf : ∀ i h, P.qlo / P.N ≤ σ i h := fun i h => (hσ.1.1 i h).1
    have hΩ := X_outcome_ge P hP [] (by simp) (by simp)
    have hne : (P.SPEOutcomes 0 ([] : History P.M)).Nonempty := ⟨_, mem0 0 (Nat.zero_le _)⟩
    have hxi : ∀ i, P.final 0 σ [] i = P.qlo := by
      intro i
      have hs := hσ.2 0 (by omega) i P.qlo ⟨fun _ => P.qlo, mem0 0 (Nat.zero_le _), rfl⟩
      have xge : P.qlo ≤ P.final 0 σ [] i := by
        have := X_final_ge P hN1 0 σ hσf [] (by simp) (by simp) i
        simpa [X_zero_apply] using this
      obtain ⟨j0, hj0⟩ := exists_ne i
      have A := X_sv_le P hP 0 (pathHist σ 0) i (P.final 0 σ (pathHist σ 0) i) hΩ
        (mem0 0 (Nat.zero_le _)) xge j0 hj0
      have B := X_sv_ge P hP 0 (pathHist σ 0) i P.qlo hΩ hne le_rfl
      have : P.final 0 σ [] i ≤ P.qlo := by
        have hh : P.γ * (P.p * P.qlo) - P.c * P.qlo ≤ P.γ * (P.p * P.qlo) - P.c * P.final 0 σ [] i :=
          le_trans B (le_trans hs A)
        nlinarith
      exact le_antisymm this xge
    constructor
    · intro n hn i
      have h1 := hxi i
      rw [X_final_root] at h1
      apply X_path_sum_lo P σ i (fun m => hσf i _) _ n hn
      simpa [X_zero_apply] using h1
    · exact X_proj_eq _ _ (fun j => (hxi j).ge) ⟨0, by omega⟩ (hxi _)

end AssemblyCoord.Feedback

open AssemblyCoord.Feedback

theorem solution (P : Params) (hP : P.Standing) (hN : P.N + 1 ≤ P.M) :
    (∃ σ : Profile P.M, P.IsSPSE 0 σ ∧
        ∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
    (∀ σ : Profile P.M, P.IsSPSE 0 σ →
        (∀ n, n < P.N → ∀ i : Fin P.M, σ i (pathHist σ n) = P.qlo / P.N) ∧
        projectLevel (P.final 0 σ []) = P.qlo) :=
  X_goal P hP hN
