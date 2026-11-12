-- Prove2me | solution 1 for ABKUFinite.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T12:04:08.3456+00:00
-- url     : https://prove2.me/submissions/bb958395-4b08-4c9e-bd3c-0bf5ce99f143

import Mathlib
import Definitions.Def_ABKUFinite_Model

set_option autoImplicit false

namespace ABKULow
open ABKUFinite

/-! ## Layer 1: deterministic process lemmas -/

/-- the bin chosen by `step` -/
def sel {n d : ℕ} (loads : Fin (n + 1) → ℕ) (choices : Fin (d + 2) → Fin (n + 1)) : Fin (n + 1) :=
  (List.ofFn choices).foldl
    (fun best candidate => if loads candidate < loads best then candidate else best) (choices 0)

theorem step_eq {n d : ℕ} (loads : Fin (n + 1) → ℕ) (choices : Fin (d + 2) → Fin (n + 1)) :
    step loads choices = Function.update loads (sel loads choices) (loads (sel loads choices) + 1) :=
  rfl

theorem foldl_min_spec {α : Type} (g : α → ℕ) (l : List α) (b : α) :
    g (l.foldl (fun best c => if g c < g best then c else best) b) ≤ g b ∧
    (∀ x ∈ l, g (l.foldl (fun best c => if g c < g best then c else best) b) ≤ g x) ∧
    (l.foldl (fun best c => if g c < g best then c else best) b = b ∨
      l.foldl (fun best c => if g c < g best then c else best) b ∈ l) := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons]
    by_cases h : g a < g b
    · rw [if_pos h]
      obtain ⟨h1, h2, h3⟩ := ih a
      refine ⟨by omega, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1
        · exact h2 x hx
      · right
        rcases h3 with h3 | h3
        · rw [h3]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ h3
    · rw [if_neg h]
      obtain ⟨h1, h2, h3⟩ := ih b
      refine ⟨h1, ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · omega
        · exact h2 x hx
      · rcases h3 with h3 | h3
        · left; exact h3
        · right; exact List.mem_cons_of_mem _ h3

theorem sel_le {n d : ℕ} (loads : Fin (n + 1) → ℕ) (choices : Fin (d + 2) → Fin (n + 1))
    (j : Fin (d + 2)) : loads (sel loads choices) ≤ loads (choices j) :=
  (foldl_min_spec loads (List.ofFn choices) (choices 0)).2.1 _ (List.mem_ofFn' _ _ |>.mpr ⟨j, rfl⟩)

theorem sel_mem {n d : ℕ} (loads : Fin (n + 1) → ℕ) (choices : Fin (d + 2) → Fin (n + 1)) :
    ∃ j, sel loads choices = choices j := by
  rcases (foldl_min_spec loads (List.ofFn choices) (choices 0)).2.2 with h | h
  · exact ⟨0, h⟩
  · obtain ⟨j, hj⟩ := (List.mem_ofFn' _ _).1 h
    exact ⟨j, hj.symm⟩

/-- loads after the first `t` balls -/
def loadsAt {n d : ℕ} (w : Trace n d) (t : ℕ) : Fin (n + 1) → ℕ :=
  ((List.ofFn w).take t).foldl step (fun _ => 0)

theorem loadsAt_zero {n d : ℕ} (w : Trace n d) : loadsAt w 0 = fun _ => 0 := by
  simp [loadsAt]

theorem loadsAt_succ {n d : ℕ} (w : Trace n d) (t : ℕ) (ht : t < n + 1) :
    loadsAt w (t + 1) = step (loadsAt w t) (w ⟨t, ht⟩) := by
  unfold loadsAt
  rw [List.take_add_one, List.foldl_append]
  have : (List.ofFn w)[t]? = some (w ⟨t, ht⟩) := by
    first
      | (rw [List.getElem?_ofFn]; simp [ht])
      | simp [List.getElem?_eq_getElem, ht]
  rw [this]
  rfl

theorem loadsAt_final {n d : ℕ} (w : Trace n d) : loadsAt w (n + 1) = finalLoads n d w := by
  unfold loadsAt finalLoads
  rw [List.take_of_length_le (by simp)]

theorem step_mono {n d : ℕ} (loads : Fin (n + 1) → ℕ) (choices : Fin (d + 2) → Fin (n + 1))
    (b : Fin (n + 1)) : loads b ≤ step loads choices b := by
  rw [step_eq]
  by_cases h : b = sel loads choices
  · subst h; simp
  · simp [Function.update_of_ne h]

theorem loadsAt_mono {n d : ℕ} (w : Trace n d) {s t : ℕ} (hst : s ≤ t) (ht : t ≤ n + 1)
    (b : Fin (n + 1)) : loadsAt w s b ≤ loadsAt w t b := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih =>
    rw [loadsAt_succ w t (by omega)]
    exact (ih (by omega)).trans (step_mono _ _ _)

/-- `Φ j L` = number of balls at height `> j` = Σ_b (L b - j) -/
def Phi {n : ℕ} (j : ℕ) (L : Fin (n + 1) → ℕ) : ℕ := ∑ b, (L b - j)

theorem Phi_step {n d : ℕ} (j : ℕ) (L : Fin (n + 1) → ℕ) (c : Fin (d + 2) → Fin (n + 1)) :
    Phi j (step L c) = Phi j L + (if j ≤ L (sel L c) then 1 else 0) := by
  unfold Phi
  rw [step_eq]
  set s := sel L c
  have h1 := Finset.sum_update_of_mem (Finset.mem_univ s) (fun b => L b - j)
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), ← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
  have h2 : ∑ x ∈ Finset.univ.erase s, (Function.update L s (L s + 1) x - j) =
      ∑ x ∈ Finset.univ.erase s, (L x - j) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [h2]
  simp only [Function.update_self]
  split_ifs with h <;> omega

theorem Phi_split {n : ℕ} (j : ℕ) (L : Fin (n + 1) → ℕ) :
    Phi j L = (Finset.univ.filter (fun b => j + 1 ≤ L b)).card + Phi (j + 1) L := by
  unfold Phi
  rw [Finset.card_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> omega

/-- every unit of `Φ (j+1)` at time `t` comes from a ball whose choices all lie in
the level-`(j+1)` set at time `t` -/
theorem Phi_le_allin {n d : ℕ} (w : Trace n d) (j t : ℕ) (ht : t ≤ n + 1) :
    Phi (j + 1) (loadsAt w t) ≤
      (Finset.univ.filter (fun s : Fin (n + 1) =>
        s.val < t ∧ ∀ k, j + 1 ≤ loadsAt w t (w s k))).card := by
  induction t with
  | zero => simp [loadsAt_zero, Phi]
  | succ t ih =>
    rw [loadsAt_succ w t (by omega), Phi_step]
    have ih' := ih (by omega)
    rw [← loadsAt_succ w t (by omega)]
    -- the old set (at time t) maps into the new set
    have hsub : (Finset.univ.filter (fun s : Fin (n + 1) =>
        s.val < t ∧ ∀ k, j + 1 ≤ loadsAt w t (w s k))) ⊆
        (Finset.univ.filter (fun s : Fin (n + 1) =>
        s.val < t + 1 ∧ ∀ k, j + 1 ≤ loadsAt w (t + 1) (w s k))) := by
      intro s hs
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
      exact ⟨by omega, fun k => (hs.2 k).trans (loadsAt_mono w (Nat.le_succ t) (by omega) _)⟩
    split_ifs with h
    · -- the new ball itself is in the new set but not in the old one
      have hnew : (⟨t, by omega⟩ : Fin (n + 1)) ∉ (Finset.univ.filter (fun s : Fin (n + 1) =>
          s.val < t ∧ ∀ k, j + 1 ≤ loadsAt w t (w s k))) := by simp
      have hin : (⟨t, by omega⟩ : Fin (n + 1)) ∈ (Finset.univ.filter (fun s : Fin (n + 1) =>
          s.val < t + 1 ∧ ∀ k, j + 1 ≤ loadsAt w (t + 1) (w s k))) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨by simp, fun k => ?_⟩
        have := sel_le (loadsAt w t) (w ⟨t, by omega⟩) k
        exact (h.trans this).trans (loadsAt_mono w (Nat.le_succ t) (by omega) _)
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun he => hnew (he ▸ hin)⟩)
      omega
    · have := Finset.card_le_card hsub
      omega

theorem Phi_ge_window {n d : ℕ} (w : Trace n d) (j t1 t2 : ℕ) (h12 : t1 ≤ t2) (ht : t2 ≤ n + 1) :
    (Finset.univ.filter (fun s : Fin (n + 1) =>
        t1 ≤ s.val ∧ s.val < t2 ∧ ∀ k, j ≤ loadsAt w t1 (w s k))).card ≤ Phi j (loadsAt w t2) := by
  induction t2, h12 using Nat.le_induction with
  | base =>
    have : (Finset.univ.filter (fun s : Fin (n + 1) =>
        t1 ≤ s.val ∧ s.val < t1 ∧ ∀ k, j ≤ loadsAt w t1 (w s k))) = ∅ := by
      ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]; omega
    rw [this]; simp
  | succ t hst ih =>
    rw [loadsAt_succ w t (by omega), Phi_step]
    have ih' := ih (by omega)
    split_ifs with h
    · have hsplit : (Finset.univ.filter (fun s : Fin (n + 1) =>
          t1 ≤ s.val ∧ s.val < t + 1 ∧ ∀ k, j ≤ loadsAt w t1 (w s k))) ⊆
          insert ⟨t, by omega⟩ (Finset.univ.filter (fun s : Fin (n + 1) =>
          t1 ≤ s.val ∧ s.val < t ∧ ∀ k, j ≤ loadsAt w t1 (w s k))) := by
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hs ⊢
        by_cases hst' : s.val = t
        · left; exact Fin.ext hst'
        · right; exact ⟨hs.1, by omega, hs.2.2⟩
      have := (Finset.card_le_card hsplit).trans (Finset.card_insert_le _ _)
      omega
    · have hsub : (Finset.univ.filter (fun s : Fin (n + 1) =>
          t1 ≤ s.val ∧ s.val < t + 1 ∧ ∀ k, j ≤ loadsAt w t1 (w s k))) ⊆
          (Finset.univ.filter (fun s : Fin (n + 1) =>
          t1 ≤ s.val ∧ s.val < t ∧ ∀ k, j ≤ loadsAt w t1 (w s k))) := by
        intro s hs
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
        refine ⟨hs.1, ?_, hs.2.2⟩
        by_contra hc
        have hval : s.val = t := by omega
        have hs_eq : s = ⟨t, Nat.lt_of_succ_le ht⟩ := Fin.ext hval
        rw [hs_eq] at hs
        obtain ⟨k, hk⟩ := sel_mem (loadsAt w t) (w ⟨t, Nat.lt_of_succ_le ht⟩)
        apply h
        rw [hk]
        exact (hs.2.2 k).trans (loadsAt_mono w hst (by omega) _)
      have := Finset.card_le_card hsub
      omega

/-- static good event: no small set of bins catches many balls with all choices inside it -/
def Good {n d : ℕ} (w : Trace n d) (M : ℕ) : Prop :=
  ∀ S : Finset (Fin (n + 1)), S.card ≤ M →
    (Finset.univ.filter (fun s : Fin (n + 1) => ∀ k, w s k ∈ S)).card ≤ 2 * S.card

/-- one phase of the layered induction (deterministic, on the good event) -/
theorem level_step {n d : ℕ} (w : Trace n d) (M j t1 t2 : ℕ) (hG : Good w M)
    (h12 : t1 ≤ t2) (ht : t2 ≤ n + 1) :
    M < (Finset.univ.filter (fun b => j + 1 ≤ loadsAt w t2 b)).card ∨
    (Finset.univ.filter (fun s : Fin (n + 1) =>
        t1 ≤ s.val ∧ s.val < t2 ∧ ∀ k, j ≤ loadsAt w t1 (w s k))).card ≤
      3 * (Finset.univ.filter (fun b => j + 1 ≤ loadsAt w t2 b)).card := by
  by_cases hM : M < (Finset.univ.filter (fun b => j + 1 ≤ loadsAt w t2 b)).card
  · exact Or.inl hM
  right
  have h1 := Phi_ge_window w j t1 t2 h12 ht
  have h2 := Phi_split j (loadsAt w t2)
  have h3 := Phi_le_allin w j t2 ht
  have h4 := hG _ (not_lt.1 hM)
  have h5 : (Finset.univ.filter (fun s : Fin (n + 1) =>
        s.val < t2 ∧ ∀ k, j + 1 ≤ loadsAt w t2 (w s k))).card ≤
      (Finset.univ.filter (fun s : Fin (n + 1) =>
        ∀ k, w s k ∈ Finset.univ.filter (fun b => j + 1 ≤ loadsAt w t2 b))).card := by
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
    exact hs.2
  omega

theorem maxLoad_ge {n d : ℕ} (w : Trace n d) (i : ℕ) (b : Fin (n + 1))
    (h : i ≤ loadsAt w (n + 1) b) : i ≤ maxLoad n d w := by
  rw [loadsAt_final] at h
  exact h.trans (Finset.le_sup (f := finalLoads n d w) (Finset.mem_univ b))

/-! ## Layer 2/3 counting -/

theorem card_allin {n d : ℕ} (T A : Finset (Fin (n + 1)))
    [DecidablePred (fun w : Trace n d => ∀ s ∈ T, ∀ k, w s k ∈ A)] :
    (Finset.univ.filter (fun w : Trace n d => ∀ s ∈ T, ∀ k, w s k ∈ A)).card =
      A.card ^ ((d + 2) * T.card) * (n + 1) ^ ((d + 2) * (n + 1 - T.card)) := by
  classical
  have h : (Finset.univ.filter (fun w : Trace n d => ∀ s ∈ T, ∀ k, w s k ∈ A)) =
      Fintype.piFinset (fun s => if s ∈ T then Fintype.piFinset (fun _ : Fin (d + 2) => A)
        else Finset.univ) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h s
      split_ifs with hs
      · exact Fintype.mem_piFinset.2 (h s hs)
      · exact Finset.mem_univ _
    · intro h s hs k
      have := h s
      rw [if_pos hs] at this
      exact Fintype.mem_piFinset.1 this k
  rw [h, Fintype.card_piFinset]
  have hc : ∀ s : Fin (n + 1), (if s ∈ T then Fintype.piFinset (fun _ : Fin (d + 2) => A)
        else (Finset.univ : Finset (Fin (d + 2) → Fin (n + 1)))).card =
      if s ∈ T then A.card ^ (d + 2) else (n + 1) ^ (d + 2) := by
    intro s; split_ifs <;> simp
  simp_rw [hc]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter (fun s : Fin (n + 1) => s ∈ T)).card = T.card := by
    congr 1; ext; simp
  have h2 : (Finset.univ.filter (fun s : Fin (n + 1) => ¬ s ∈ T)).card = n + 1 - T.card := by
    have : Finset.univ.filter (fun s : Fin (n + 1) => ¬ s ∈ T) = Tᶜ := by ext; simp
    rw [this, Finset.card_compl, Fintype.card_fin]
  rw [h1, h2, ← pow_mul, ← pow_mul]

theorem card_trace (n d : ℕ) : Fintype.card (Trace n d) = (n + 1) ^ ((d + 2) * (n + 1)) := by
  simp [Trace, ← pow_mul]

theorem prob_allin {n d : ℕ} (T A : Finset (Fin (n + 1))) :
    probability n d (fun w => ∀ s ∈ T, ∀ k, w s k ∈ A) =
      ((A.card : ℝ) / (n + 1)) ^ ((d + 2) * T.card) := by
  unfold probability
  simp only [Fintype.card_subtype]
  rw [card_allin, card_trace]
  have hT : T.card ≤ n + 1 := by simpa using T.card_le_univ
  have he : (d + 2) * (n + 1) = (d + 2) * T.card + (d + 2) * (n + 1 - T.card) := by
    rw [← mul_add]; congr 1; omega
  rw [he, pow_add]
  push_cast
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [div_pow]
  field_simp

theorem card_pred_eq {n d : ℕ} (P : Trace n d → Prop) [DecidablePred P] :
    ((Finset.univ.filter P).card : ℝ) = probability n d P * (Fintype.card (Trace n d) : ℝ) := by
  unfold probability
  simp only [Fintype.card_subtype]
  have hQ : (0 : ℝ) < Fintype.card (Trace n d) := by exact_mod_cast Fintype.card_pos
  rw [div_mul_cancel₀ _ hQ.ne']

theorem card_one {n d : ℕ} (A : Finset (Fin (n + 1))) (s : Fin (n + 1)) :
    ((Finset.univ.filter (fun w : Trace n d => ∀ k, w s k ∈ A)).card : ℝ) =
      ((A.card : ℝ) / (n + 1)) ^ (d + 2) * (Fintype.card (Trace n d) : ℝ) := by
  rw [card_pred_eq]
  have := prob_allin (d := d) {s} A
  simp only [Finset.mem_singleton, forall_eq, Finset.card_singleton, mul_one] at this
  rw [this]

theorem card_two {n d : ℕ} (A : Finset (Fin (n + 1))) (s s' : Fin (n + 1)) (h : s ≠ s') :
    ((Finset.univ.filter (fun w : Trace n d => (∀ k, w s k ∈ A) ∧ ∀ k, w s' k ∈ A)).card : ℝ) =
      (((A.card : ℝ) / (n + 1)) ^ (d + 2)) ^ 2 * (Fintype.card (Trace n d) : ℝ) := by
  rw [card_pred_eq]
  have := prob_allin (d := d) {s, s'} A
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    Finset.card_pair h] at this
  rw [this, ← pow_mul]

def ind {n d : ℕ} (A : Finset (Fin (n + 1))) (w : Trace n d) (s : Fin (n + 1)) : ℝ :=
  if ∀ k, w s k ∈ A then 1 else 0

/-- second-moment (Chebyshev) lower tail for the number of window balls landing all-in `A` -/
theorem cheb {n d : ℕ} (W A : Finset (Fin (n + 1)))
    (hμ : 0 < (W.card : ℝ) * ((A.card : ℝ) / (n + 1)) ^ (d + 2)) :
    probability n d (fun w => ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) <
        (W.card : ℝ) * ((A.card : ℝ) / (n + 1)) ^ (d + 2) / 2) ≤
      4 / ((W.card : ℝ) * ((A.card : ℝ) / (n + 1)) ^ (d + 2)) := by
  classical
  set p := ((A.card : ℝ) / (n + 1)) ^ (d + 2) with hp
  set μ := (W.card : ℝ) * p with hμdef
  set Q := (Fintype.card (Trace n d) : ℝ) with hQ
  have hQpos : 0 < Q := by rw [hQ]; exact_mod_cast Fintype.card_pos
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hX : ∀ w : Trace n d,
      ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) = ∑ s ∈ W, ind A w s := by
    intro w; rw [Finset.card_filter]; push_cast; rfl
  have hs1 : ∀ s, ∑ w : Trace n d, ind A w s = p * Q := by
    intro s
    simp only [ind]
    rw [Finset.sum_boole, card_one]
  have hsum1 : ∑ w : Trace n d, ∑ s ∈ W, ind A w s = μ * Q := by
    rw [Finset.sum_comm, Finset.sum_congr rfl (fun s _ => hs1 s), Finset.sum_const, nsmul_eq_mul]
    ring
  have hsum2 : ∑ w : Trace n d, (∑ s ∈ W, ind A w s) ^ 2 ≤ (μ + μ ^ 2) * Q := by
    have e : ∀ w : Trace n d, (∑ s ∈ W, ind A w s) ^ 2 = ∑ s ∈ W, ∑ s' ∈ W, ind A w s * ind A w s' := by
      intro w; rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl (fun w _ => e w), Finset.sum_comm]
    have h2 : ∀ s ∈ W, ∑ w : Trace n d, ∑ s' ∈ W, ind A w s * ind A w s' ≤
        p * Q + W.card * (p ^ 2 * Q) := by
      intro s hs
      rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ hs]
      have e1 : ∑ w : Trace n d, ind A w s * ind A w s = p * Q := by
        rw [← hs1 s]
        apply Finset.sum_congr rfl
        intro w _
        simp only [ind]; split_ifs <;> norm_num
      have e2 : ∀ s' ∈ W.erase s, ∑ w : Trace n d, ind A w s * ind A w s' = p ^ 2 * Q := by
        intro s' hs'
        have hne : s ≠ s' := fun h => (Finset.ne_of_mem_erase hs') h.symm
        simp only [ind, ite_zero_mul_ite_zero, mul_one]
        rw [Finset.sum_boole, card_two A s s' hne]
      rw [e1, Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul]
      have h3 : ((W.erase s).card : ℝ) ≤ W.card := by
        exact_mod_cast Finset.card_le_card (Finset.erase_subset _ _)
      have h4 : 0 ≤ p ^ 2 * Q := by positivity
      nlinarith
    calc _ ≤ ∑ s ∈ W, (p * Q + W.card * (p ^ 2 * Q)) := Finset.sum_le_sum h2
      _ = (μ + μ ^ 2) * Q := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  have hvar : ∑ w : Trace n d, ((∑ s ∈ W, ind A w s) - μ) ^ 2 ≤ μ * Q := by
    have e : ∀ w : Trace n d, ((∑ s ∈ W, ind A w s) - μ) ^ 2 =
        (∑ s ∈ W, ind A w s) ^ 2 + (-(2 * μ) * (∑ s ∈ W, ind A w s) + μ ^ 2) := fun w => by ring
    rw [Finset.sum_congr rfl (fun w _ => e w), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum1, ← hQ]
    nlinarith [hsum2]
  have hbad : ((Finset.univ.filter (fun w : Trace n d =>
      ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) < μ / 2)).card : ℝ) * (μ / 2) ^ 2 ≤ μ * Q := by
    calc _ = ∑ w ∈ Finset.univ.filter (fun w : Trace n d =>
          ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) < μ / 2), (μ / 2) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ w ∈ Finset.univ.filter (fun w : Trace n d =>
          ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) < μ / 2),
            ((∑ s ∈ W, ind A w s) - μ) ^ 2 := by
          apply Finset.sum_le_sum
          intro w hw
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
          rw [hX] at hw
          have h0 : 0 ≤ ∑ s ∈ W, ind A w s := by
            rw [← hX]; positivity
          nlinarith
      _ ≤ ∑ w : Trace n d, ((∑ s ∈ W, ind A w s) - μ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => sq_nonneg _)
      _ ≤ μ * Q := hvar
  have hc := card_pred_eq (fun w : Trace n d =>
      ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) < μ / 2)
  rw [← hQ] at hc
  have hpr : probability n d (fun w : Trace n d =>
      ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) < μ / 2) =
      ((Finset.univ.filter (fun w : Trace n d =>
      ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) < μ / 2)).card : ℝ) / Q := by
    rw [hc, mul_div_cancel_right₀ _ hQpos.ne']
  rw [hpr, div_le_div_iff₀ hQpos hμ]
  nlinarith

/-! ## Layer 4: independence of disjoint coordinate blocks -/

theorem indep_card {ι X : Type} [Fintype ι] [DecidableEq ι] [Fintype X] [DecidableEq X]
    (S : ι → Prop) [DecidablePred S] (P Q : (ι → X) → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ w w', (∀ i, S i → w i = w' i) → P w → P w')
    (hQ : ∀ w w', (∀ i, ¬ S i → w i = w' i) → Q w → Q w') :
    Fintype.card {w // P w ∧ Q w} * Fintype.card (ι → X) =
      Fintype.card {w // P w} * Fintype.card {w // Q w} := by
  classical
  let e := Equiv.piEquivPiSubtypeProd S (fun _ => X)
  let P' : ((i : {i // S i}) → X) → Prop := fun u => ∃ w, (e w).1 = u ∧ P w
  let Q' : ((i : {i // ¬ S i}) → X) → Prop := fun v => ∃ w, (e w).2 = v ∧ Q w
  have hP' : ∀ w, P w ↔ P' (e w).1 := by
    intro w; constructor
    · intro h; exact ⟨w, rfl, h⟩
    · rintro ⟨w', hw', h⟩
      apply hP w' w _ h
      intro i hi
      have := congrFun hw' ⟨i, hi⟩
      simpa [e, Equiv.piEquivPiSubtypeProd] using this
  have hQ' : ∀ w, Q w ↔ Q' (e w).2 := by
    intro w; constructor
    · intro h; exact ⟨w, rfl, h⟩
    · rintro ⟨w', hw', h⟩
      apply hQ w' w _ h
      intro i hi
      have := congrFun hw' ⟨i, hi⟩
      simpa [e, Equiv.piEquivPiSubtypeProd] using this
  have c1 : Fintype.card {w // P w ∧ Q w} =
      Fintype.card {a // P' a} * Fintype.card {b // Q' b} := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr ((e.subtypeEquiv (fun w => and_congr (hP' w) (hQ' w))).trans
      Equiv.subtypeProdEquivProd)
  have c2 : Fintype.card {w // P w} =
      Fintype.card {a // P' a} * Fintype.card ((i : {i // ¬ S i}) → X) := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr ((e.subtypeEquiv (q := fun c => P' c.1 ∧ True) (fun w => (hP' w).trans ⟨fun h => ⟨h, trivial⟩, fun h => h.1⟩)).trans
      (Equiv.subtypeProdEquivProd.trans
        (Equiv.prodCongr (Equiv.refl _) (Equiv.subtypeUnivEquiv (fun _ => trivial)))))
  have c3 : Fintype.card {w // Q w} =
      Fintype.card ((i : {i // S i}) → X) * Fintype.card {b // Q' b} := by
    rw [← Fintype.card_prod]
    exact Fintype.card_congr ((e.subtypeEquiv (q := fun c => True ∧ Q' c.2) (fun w => (hQ' w).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩)).trans
      (Equiv.subtypeProdEquivProd.trans
        (Equiv.prodCongr (Equiv.subtypeUnivEquiv (fun _ => trivial)) (Equiv.refl _))))
  have c4 : Fintype.card (ι → X) =
      Fintype.card ((i : {i // S i}) → X) * Fintype.card ((i : {i // ¬ S i}) → X) := by
    rw [← Fintype.card_prod]; exact Fintype.card_congr e
  rw [c1, c2, c3, c4]; ring

/-! ## Layer 4: conditioning on the past -/

theorem loadsAt_local {n d : ℕ} (w w' : Trace n d) (t : ℕ)
    (h : ∀ s : Fin (n + 1), s.val < t → w s = w' s) : loadsAt w t = loadsAt w' t := by
  by_cases ht : t ≤ n + 1
  · induction t with
    | zero => rw [loadsAt_zero, loadsAt_zero]
    | succ t ih =>
      rw [loadsAt_succ w t (by omega), loadsAt_succ w' t (by omega),
        ih (fun s hs => h s (by omega)) (by omega), h ⟨t, by omega⟩ (by simp)]
  · have : w = w' := funext fun s => h s (by omega)
    rw [this]

theorem prob_mono {n d : ℕ} {P Q : Trace n d → Prop} (h : ∀ w, P w → Q w) :
    probability n d P ≤ probability n d Q := by
  classical
  unfold probability
  have hQ : (0 : ℝ) ≤ Fintype.card (Trace n d) := by positivity
  have hc : (Fintype.card {w // P w} : ℝ) ≤ Fintype.card {w // Q w} := by
    exact_mod_cast Fintype.card_subtype_mono P Q (fun w hw => h w hw)
  exact div_le_div_of_nonneg_right hc hQ

theorem prob_eq_zero {n d : ℕ} {P : Trace n d → Prop} (h : ∀ w, ¬ P w) :
    probability n d P = 0 := by
  classical
  unfold probability
  rw [Fintype.card_eq_zero_iff.2 ⟨fun x => h x.1 x.2⟩]
  simp

theorem prob_nonneg {n d : ℕ} (P : Trace n d → Prop) : 0 ≤ probability n d P := by
  unfold probability; positivity

theorem cond_bound {n d : ℕ} (f : Trace n d → Finset (Fin (n + 1)))
    (S : Fin (n + 1) → Prop) [DecidablePred S]
    (hf : ∀ w w' : Trace n d, (∀ i, S i → w i = w' i) → f w = f w')
    (R : Finset (Fin (n + 1)) → Trace n d → Prop)
    (hR : ∀ A (w w' : Trace n d), (∀ i, ¬ S i → w i = w' i) → R A w → R A w')
    (c : ℝ) (hc : ∀ A, probability n d (R A) ≤ c) :
    probability n d (fun w => R (f w) w) ≤ c := by
  classical
  set Q := (Fintype.card (Trace n d) : ℝ) with hQ
  have hQpos : 0 < Q := by rw [hQ]; exact_mod_cast Fintype.card_pos
  have key : ∀ A, ((Finset.univ.filter (fun w : Trace n d => f w = A ∧ R A w)).card : ℝ) ≤
      c * (Finset.univ.filter (fun w : Trace n d => f w = A)).card := by
    intro A
    have h1 := indep_card S (fun w : Trace n d => f w = A) (R A)
      (fun w w' h hw => (hf w w' h).symm.trans hw) (hR A)
    simp only [Fintype.card_subtype] at h1
    have h2 := card_pred_eq (R A)
    have h3 := hc A
    have h1' : ((Finset.univ.filter (fun w : Trace n d => f w = A ∧ R A w)).card : ℝ) * Q =
        (Finset.univ.filter (fun w : Trace n d => f w = A)).card *
        (Finset.univ.filter (R A)).card := by rw [hQ]; exact_mod_cast h1
    rw [h2, ← hQ] at h1'
    have : ((Finset.univ.filter (fun w : Trace n d => f w = A ∧ R A w)).card : ℝ) * Q ≤
        c * (Finset.univ.filter (fun w : Trace n d => f w = A)).card * Q := by
      rw [h1']
      calc _ = ((Finset.univ.filter (fun w : Trace n d => f w = A)).card : ℝ) *
            probability n d (R A) * Q := by ring
        _ ≤ ((Finset.univ.filter (fun w : Trace n d => f w = A)).card : ℝ) * c * Q := by gcongr
        _ = _ := by ring
    exact le_of_mul_le_mul_right this hQpos
  have hsplit : (Finset.univ.filter (fun w : Trace n d => R (f w) w)).card =
      ∑ A : Finset (Fin (n + 1)),
        (Finset.univ.filter (fun w : Trace n d => f w = A ∧ R A w)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
    apply Finset.sum_congr rfl
    intro A _
    congr 1; ext w; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, rfl⟩; exact ⟨rfl, h⟩
    · rintro ⟨rfl, h⟩; exact ⟨h, rfl⟩
  have htot : ∑ A : Finset (Fin (n + 1)),
      ((Finset.univ.filter (fun w : Trace n d => f w = A)).card : ℝ) = Q := by
    rw [hQ]; norm_cast
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  have hE := card_pred_eq (fun w => R (f w) w)
  rw [← hQ] at hE
  have : probability n d (fun w => R (f w) w) * Q ≤ c * Q := by
    rw [← hE, hsplit]; push_cast
    calc _ ≤ ∑ A : Finset (Fin (n + 1)),
          c * ((Finset.univ.filter (fun w : Trace n d => f w = A)).card : ℝ) :=
          Finset.sum_le_sum (fun A _ => key A)
      _ = c * Q := by rw [← Finset.mul_sum, htot]
  exact le_of_mul_le_mul_right this hQpos

/-- level set `B_j(t)` -/
def Bset {n d : ℕ} (w : Trace n d) (j t : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun b => j ≤ loadsAt w t b)

/-- one phase fails with probability `≤ 4/μ` -/
theorem phase_whp {n d : ℕ} (j t1 β : ℕ) (W : Finset (Fin (n + 1)))
    (hW : ∀ s ∈ W, t1 ≤ s.val) (κ : ℝ)
    (hμ : 0 < (W.card : ℝ) * ((β : ℝ) / (n + 1)) ^ (d + 2))
    (hκ : κ ≤ (W.card : ℝ) * ((β : ℝ) / (n + 1)) ^ (d + 2) / 2) :
    probability n d (fun w => β ≤ (Bset w j t1).card ∧
      ((W.filter (fun s => ∀ k, w s k ∈ Bset w j t1)).card : ℝ) < κ) ≤
      4 / ((W.card : ℝ) * ((β : ℝ) / (n + 1)) ^ (d + 2)) := by
  classical
  apply cond_bound (fun w => Bset w j t1) (fun i : Fin (n + 1) => i.val < t1)
    (fun w w' h => by
      show Bset w j t1 = Bset w' j t1
      unfold Bset; rw [loadsAt_local w w' t1 h])
    (fun A w => β ≤ A.card ∧ ((W.filter (fun s => ∀ k, w s k ∈ A)).card : ℝ) < κ)
  · intro A w w' h hw
    have : W.filter (fun s => ∀ k, w s k ∈ A) = W.filter (fun s => ∀ k, w' s k ∈ A) := by
      apply Finset.filter_congr
      intro s hs
      rw [h s (by have := hW s hs; omega)]
    beta_reduce at hw ⊢
    rw [← this]; exact hw
  · intro A
    by_cases hA : β ≤ A.card
    · obtain ⟨A', hA'A, hA'c⟩ := Finset.exists_subset_card_eq hA
      have hμ' : 0 < (W.card : ℝ) * ((A'.card : ℝ) / (n + 1)) ^ (d + 2) := by
        rw [hA'c]; exact hμ
      have hch := cheb (d := d) W A' hμ'
      rw [hA'c] at hch
      refine le_trans (prob_mono ?_) hch
      intro w hw
      beta_reduce at hw
      have hsub : ((W.filter (fun s => ∀ k, w s k ∈ A')).card : ℝ) ≤
          (W.filter (fun s => ∀ k, w s k ∈ A)).card := by
        exact_mod_cast Finset.card_le_card (fun s hs => by
          simp only [Finset.mem_filter] at hs ⊢
          exact ⟨hs.1, fun k => hA'A (hs.2 k)⟩)
      linarith [hw.2]
    · rw [prob_eq_zero (fun w hw => hA hw.1)]; positivity

/-! ## Layer 2: the static good event holds w.h.p. -/

theorem prob_union {n d : ℕ} {ι : Type} (I : Finset ι) (P : ι → Trace n d → Prop) :
    probability n d (fun w => ∃ i ∈ I, P i w) ≤ ∑ i ∈ I, probability n d (P i) := by
  classical
  have hQpos : (0 : ℝ) < Fintype.card (Trace n d) := by exact_mod_cast Fintype.card_pos
  have hsub : Finset.univ.filter (fun w => ∃ i ∈ I, P i w) ⊆
      I.biUnion (fun i => Finset.univ.filter (P i)) := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion] at hw ⊢
    exact hw
  have hc : ((Finset.univ.filter (fun w => ∃ i ∈ I, P i w)).card : ℝ) ≤
      ∑ i ∈ I, ((Finset.univ.filter (P i)).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  rw [card_pred_eq] at hc
  rw [Finset.sum_congr rfl (fun i _ => card_pred_eq (P i)), ← Finset.sum_mul] at hc
  exact le_of_mul_le_mul_right hc hQpos

theorem not_good_cover {n d : ℕ} (w : Trace n d) (M : ℕ) (h : ¬ Good w M) :
    ∃ s ∈ Finset.Icc 1 M, ∃ S ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard s,
      ∃ T ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard (2 * s + 1),
        ∀ t ∈ T, ∀ k, w t k ∈ S := by
  classical
  unfold Good at h
  push_neg at h
  obtain ⟨S, hS, hc⟩ := h
  have hs1 : 1 ≤ S.card := by
    rcases Nat.eq_zero_or_pos S.card with h0 | h0
    · rw [Finset.card_eq_zero] at h0
      subst h0
      have : (Finset.univ.filter (fun s : Fin (n + 1) => ∀ k, w s k ∈ (∅ : Finset (Fin (n + 1))))) = ∅ := by
        ext s; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false, not_forall]
        exact ⟨0, id⟩
      rw [this] at hc; simp at hc
    · exact h0
  obtain ⟨T, hT, hTc⟩ := Finset.exists_subset_card_eq
    (show 2 * S.card + 1 ≤ (Finset.univ.filter (fun s : Fin (n + 1) => ∀ k, w s k ∈ S)).card by omega)
  refine ⟨S.card, Finset.mem_Icc.2 ⟨hs1, hS⟩, S, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, rfl⟩,
    T, Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, hTc⟩, fun t ht => ?_⟩
  exact (Finset.mem_filter.1 (hT ht)).2

theorem term_bound (n d s : ℕ) (hs : 1 ≤ s) (hsN : (s : ℝ) ≤ ((n : ℝ) + 1) / 96) :
    ((n + 1).choose s : ℝ) * ((n + 1).choose (2 * s + 1) : ℝ) *
      ((s : ℝ) / (n + 1)) ^ ((d + 2) * (2 * s + 1)) ≤ 3 * (1 / 2 : ℝ) ^ s / ((n : ℝ) + 1) := by
  set N : ℝ := (n : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  set x : ℝ := (s : ℝ) / N with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 96 := by rw [hx, div_le_iff₀ hNpos]; linarith
  have hNx : N * x = s := by rw [hx]; field_simp
  have c1 : ((n + 1).choose s : ℝ) ≤ N ^ s / (s.factorial : ℝ) := by
    have := Nat.choose_le_pow_div (α := ℝ) s (n + 1); push_cast at this; exact this
  have c2 : ((n + 1).choose (2 * s + 1) : ℝ) ≤ N ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ) := by
    have := Nat.choose_le_pow_div (α := ℝ) (2 * s + 1) (n + 1); push_cast at this; exact this
  have p1 : x ^ ((d + 2) * (2 * s + 1)) ≤ x ^ (4 * s + 2) :=
    pow_le_pow_of_le_one hx0 (by linarith)
      (by calc 4 * s + 2 = 2 * (2 * s + 1) := by ring
            _ ≤ (d + 2) * (2 * s + 1) := Nat.mul_le_mul_right _ (by omega))
  have f1 : (s : ℝ) ^ s / (s.factorial : ℝ) ≤ Real.exp 1 ^ s := by
    rw [← Real.exp_nat_mul, mul_one]; exact Real.pow_div_factorial_le_exp _ (by positivity) s
  have f2 : (s : ℝ) ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ) ≤ Real.exp 1 ^ (2 * s + 1) := by
    calc (s : ℝ) ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ)
        ≤ ((2 * s + 1 : ℕ) : ℝ) ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ) := by
          gcongr; push_cast; linarith
      _ ≤ Real.exp ((2 * s + 1 : ℕ) : ℝ) := Real.pow_div_factorial_le_exp _ (by positivity) _
      _ = Real.exp 1 ^ (2 * s + 1) := by rw [← Real.exp_nat_mul, mul_one]
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
  have he24 : Real.exp 1 ^ 3 ≤ 24 := by
    calc Real.exp 1 ^ 3 ≤ (2.7182818286 : ℝ) ^ 3 := by gcongr; exact Real.exp_one_lt_d9.le
      _ ≤ 24 := by norm_num
  have he3 : Real.exp 1 ^ 3 * x ≤ 1 / 4 := by
    have := mul_le_mul he24 hx1 hx0 (by norm_num : (0 : ℝ) ≤ 24)
    linarith
  have hs2 : (s : ℝ) * (1 / 2 : ℝ) ^ s ≤ 1 := by
    have h2s : (s : ℝ) ≤ 2 ^ s := by
      have : s < 2 ^ s := Nat.lt_two_pow_self
      exact_mod_cast this.le
    calc (s : ℝ) * (1 / 2 : ℝ) ^ s ≤ 2 ^ s * (1 / 2 : ℝ) ^ s := by gcongr
      _ = 1 := by rw [← mul_pow]; norm_num
  have q : (1 / 4 : ℝ) ^ s = (1 / 2 : ℝ) ^ s * (1 / 2 : ℝ) ^ s := by rw [← mul_pow]; norm_num
  calc ((n + 1).choose s : ℝ) * ((n + 1).choose (2 * s + 1) : ℝ) * x ^ ((d + 2) * (2 * s + 1))
      ≤ (N ^ s / (s.factorial : ℝ)) * (N ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ)) *
          x ^ (4 * s + 2) := by gcongr
    _ = ((N * x) ^ s / (s.factorial : ℝ)) * ((N * x) ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ)) *
          x ^ (s + 1) := by ring
    _ = ((s : ℝ) ^ s / (s.factorial : ℝ)) * ((s : ℝ) ^ (2 * s + 1) / ((2 * s + 1).factorial : ℝ)) *
          x ^ (s + 1) := by rw [hNx]
    _ ≤ Real.exp 1 ^ s * Real.exp 1 ^ (2 * s + 1) * x ^ (s + 1) := by gcongr
    _ = Real.exp 1 * x * (Real.exp 1 ^ 3 * x) ^ s := by ring
    _ ≤ Real.exp 1 * x * (1 / 4) ^ s := by gcongr
    _ = Real.exp 1 / N * ((s : ℝ) * (1 / 2 : ℝ) ^ s) * (1 / 2 : ℝ) ^ s := by rw [q, hx]; ring
    _ ≤ 3 / N * 1 * (1 / 2 : ℝ) ^ s := by gcongr
    _ = 3 * (1 / 2 : ℝ) ^ s / N := by ring

theorem good_whp (n d M : ℕ) (hM : (M : ℝ) ≤ ((n : ℝ) + 1) / 96) :
    probability n d (fun w => ¬ Good w M) ≤ 6 / ((n : ℝ) + 1) := by
  classical
  have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  calc probability n d (fun w => ¬ Good w M)
      ≤ probability n d (fun w => ∃ s ∈ Finset.Icc 1 M,
          ∃ S ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard s,
          ∃ T ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard (2 * s + 1),
            ∀ t ∈ T, ∀ k, w t k ∈ S) :=
        prob_mono (fun w hw => not_good_cover w M hw)
    _ ≤ ∑ s ∈ Finset.Icc 1 M, probability n d (fun w =>
          ∃ S ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard s,
          ∃ T ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard (2 * s + 1),
            ∀ t ∈ T, ∀ k, w t k ∈ S) := prob_union _ _
    _ ≤ ∑ s ∈ Finset.Icc 1 M, ((n + 1).choose s : ℝ) * ((n + 1).choose (2 * s + 1) : ℝ) *
          ((s : ℝ) / (n + 1)) ^ ((d + 2) * (2 * s + 1)) := by
        apply Finset.sum_le_sum
        intro s _
        refine (prob_union _ _).trans ?_
        have hS1 : ∀ S ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard s,
            probability n d (fun w => ∃ T ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard (2 * s + 1),
              ∀ t ∈ T, ∀ k, w t k ∈ S)
              ≤ ((n + 1).choose (2 * s + 1) : ℝ) * ((s : ℝ) / (n + 1)) ^ ((d + 2) * (2 * s + 1)) := by
          intro S hS
          rw [Finset.mem_powersetCard] at hS
          refine (prob_union _ _).trans (le_of_eq ?_)
          have hterm : ∀ T ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard (2 * s + 1),
              probability n d (fun w => ∀ t ∈ T, ∀ k, w t k ∈ S) =
                ((s : ℝ) / (n + 1)) ^ ((d + 2) * (2 * s + 1)) := by
            intro T hT
            rw [prob_allin, hS.2, (Finset.mem_powersetCard.1 hT).2]
          rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_powersetCard,
            Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        refine (Finset.sum_le_sum hS1).trans (le_of_eq ?_)
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
    _ ≤ ∑ s ∈ Finset.Icc 1 M, 3 * (1 / 2 : ℝ) ^ s / ((n : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro s hs
        rw [Finset.mem_Icc] at hs
        apply term_bound n d s hs.1
        have : (s : ℝ) ≤ M := by exact_mod_cast hs.2
        linarith
    _ ≤ 6 / ((n : ℝ) + 1) := by
        rw [← Finset.sum_div, ← Finset.mul_sum]
        apply div_le_div_of_nonneg_right _ hNpos.le
        have h1 : ∑ s ∈ Finset.Icc 1 M, (1 / 2 : ℝ) ^ s ≤ ∑ s ∈ Finset.range (M + 1), (1 / 2 : ℝ) ^ s :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by intro s hs; simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢; omega)
            (fun _ _ _ => by positivity)
        have h2 := sum_geometric_two_le (M + 1)
        linarith

/-! ## Layer 5: phases, sizes and assembly -/

/-- start of phase `i` -/
def T (n i : ℕ) : ℕ := (n + 1) - (n + 1) / 2 ^ i

theorem T_le (n i : ℕ) : T n i ≤ n + 1 := Nat.sub_le _ _

theorem T_mono (n i : ℕ) : T n i ≤ T n (i + 1) := by
  unfold T
  have : (n + 1) / 2 ^ (i + 1) ≤ (n + 1) / 2 ^ i :=
    Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
  omega

def Win (n i : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun s : Fin (n + 1) => T n i ≤ s.val ∧ s.val < T n (i + 1))

theorem card_window (n a b : ℕ) (hb : b ≤ n + 1) :
    (Finset.univ.filter (fun s : Fin (n + 1) => a ≤ s.val ∧ s.val < b)).card = b - a := by
  rw [← Nat.card_Ico, ← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
  congr 1
  ext x
  simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk, Finset.mem_Ico]
  constructor
  · rintro ⟨s, hs, rfl⟩; exact hs
  · intro hx; exact ⟨⟨x, by omega⟩, hx, rfl⟩

theorem card_win_ge (n i : ℕ) (h : (2 : ℝ) ^ (i + 2) ≤ (n : ℝ) + 1) :
    ((n : ℝ) + 1) / 2 ^ (i + 2) ≤ ((Win n i).card : ℝ) := by
  have hc : (Win n i).card = T n (i + 1) - T n i := card_window n _ _ (T_le n (i + 1))
  set q := (n + 1) / 2 ^ (i + 1) with hq
  have h1 : (n + 1) / 2 ^ (i + 1) = (n + 1) / 2 ^ i / 2 := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have h2 : (n + 1) / 2 ^ i / 2 * 2 ≤ (n + 1) / 2 ^ i := Nat.div_mul_le_self _ _
  have h3 : (n + 1) / 2 ^ i ≤ n + 1 := Nat.div_le_self _ _
  have hge : q ≤ (Win n i).card := by
    rw [hc]; unfold T; omega
  have hlt : n + 1 < q * 2 ^ (i + 1) + 2 ^ (i + 1) := Nat.lt_div_mul_add (by positivity)
  have hlt' : (n : ℝ) + 1 < ((q : ℝ) + 1) * 2 ^ (i + 1) := by
    have : ((n + 1 : ℕ) : ℝ) < ((q * 2 ^ (i + 1) + 2 ^ (i + 1) : ℕ) : ℝ) := by exact_mod_cast hlt
    push_cast at this; linarith
  have hp : (0 : ℝ) < 2 ^ (i + 1) := by positivity
  have hq' : ((n : ℝ) + 1) / 2 ^ (i + 1) - 1 < q := by
    rw [sub_lt_iff_lt_add, div_lt_iff₀ hp]; linarith
  have h4 : ((n : ℝ) + 1) / 2 ^ (i + 2) ≤ ((n : ℝ) + 1) / 2 ^ (i + 1) - 1 := by
    have e : (2 : ℝ) ^ (i + 2) = 2 ^ (i + 1) * 2 := by rw [pow_succ]
    have h5 : 1 ≤ ((n : ℝ) + 1) / 2 ^ (i + 2) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [e] at h5 ⊢
    have : ((n : ℝ) + 1) / 2 ^ (i + 1) = 2 * (((n : ℝ) + 1) / (2 ^ (i + 1) * 2)) := by
      field_simp
    linarith
  have : (q : ℝ) ≤ (Win n i).card := by exact_mod_cast hge
  linarith

/-- level-density lower bounds -/
noncomputable def xs (d : ℕ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => min (1 / 96) (xs d i ^ (d + 2) / (24 * 2 ^ i))

theorem xs_succ (d i : ℕ) : xs d (i + 1) = min (1 / 96) (xs d i ^ (d + 2) / (24 * 2 ^ i)) := rfl

theorem xs_pos (d i : ℕ) : 0 < xs d i := by
  induction i with
  | zero => show (0 : ℝ) < 1; norm_num
  | succ i ih => rw [xs_succ]; exact lt_min (by norm_num) (by positivity)

/-- exponent `g i = 11 D^i - i - 5` -/
noncomputable def g (d i : ℕ) : ℝ := 11 * ((d : ℝ) + 2) ^ i - i - 5

theorem Dpow_ge (d i : ℕ) : (i : ℝ) + 1 ≤ ((d : ℝ) + 2) ^ i := by
  have := one_add_mul_le_pow (show (-2 : ℝ) ≤ (d : ℝ) + 1 by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]) i
  have h0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have e : (1 : ℝ) + ((d : ℝ) + 1) = (d : ℝ) + 2 := by ring
  rw [e] at this
  nlinarith

theorem exp_g_step (d i : ℕ) (x : ℝ) (hx : Real.exp (-g d i) ≤ x) :
    Real.exp (-g d (i + 1)) ≤ x ^ (d + 2) / (24 * 2 ^ i) := by
  have hD : (2 : ℝ) ≤ (d : ℝ) + 2 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hpow : Real.exp (-g d i) ^ (d + 2) ≤ x ^ (d + 2) := by gcongr
  rw [← Real.exp_nat_mul] at hpow
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have h24 : (24 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ)
    have h2 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h2]
    calc (24 : ℝ) ≤ 2.7 ^ 4 := by norm_num
      _ ≤ Real.exp 1 ^ 4 := by
        gcongr
        have := Real.exp_one_gt_d9; linarith
  have h2i : (2 : ℝ) ^ i ≤ Real.exp i := by
    rw [← Real.exp_one_pow]; gcongr
  have hden : (24 : ℝ) * 2 ^ i ≤ Real.exp (4 + i) := by
    rw [Real.exp_add]; gcongr
  have hgi : ((d + 2 : ℕ) : ℝ) * (-g d i) - (4 + i) ≥ -g d (i + 1) := by
    unfold g; push_cast
    have h1 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    have e : ((d : ℝ) + 2) ^ (i + 1) = ((d : ℝ) + 2) * ((d : ℝ) + 2) ^ i := by ring
    rw [e]; nlinarith
  calc Real.exp (-g d (i + 1)) ≤ Real.exp (((d + 2 : ℕ) : ℝ) * (-g d i) - (4 + i)) :=
        Real.exp_le_exp.2 hgi
    _ = Real.exp (((d + 2 : ℕ) : ℝ) * (-g d i)) / Real.exp (4 + i) := by rw [Real.exp_sub]
    _ ≤ x ^ (d + 2) / (24 * 2 ^ i) := by
        gcongr
        exact le_trans (by positivity) hpow

theorem xs_ge (d i : ℕ) : Real.exp (-g d i) ≤ xs d i := by
  induction i with
  | zero =>
    show Real.exp (-g d 0) ≤ 1
    rw [Real.exp_le_one_iff]; unfold g; norm_num
  | succ i ih =>
    rw [xs_succ]
    refine le_min ?_ (exp_g_step d i _ ih)
    have h5 : (5 : ℝ) ≤ g d (i + 1) := by
      unfold g
      have := Dpow_ge d (i + 1)
      push_cast at this ⊢
      have h1 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
      linarith
    have he5 : (96 : ℝ) ≤ Real.exp 5 := by
      have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h2]
      calc (96 : ℝ) ≤ 2.7 ^ 5 := by norm_num
        _ ≤ Real.exp 1 ^ 5 := by
          gcongr
          have := Real.exp_one_gt_d9; linarith
    calc Real.exp (-g d (i + 1)) ≤ Real.exp (-5) := Real.exp_le_exp.2 (by linarith)
      _ = 1 / Real.exp 5 := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / 96 := by gcongr

noncomputable def kap (n d i : ℕ) : ℝ := ((n : ℝ) + 1) / 2 ^ (i + 2) * xs d i ^ (d + 2) / 2

def Fail (n d i : ℕ) (w : Trace n d) : Prop :=
  ⌈xs d i * ((n : ℝ) + 1)⌉₊ ≤ (Bset w i (T n i)).card ∧
    (((Win n i).filter (fun s => ∀ k, w s k ∈ Bset w i (T n i))).card : ℝ) < kap n d i

theorem levels {n d : ℕ} (w : Trace n d) (L : ℕ) (hG : Good w ⌊((n : ℝ) + 1) / 96⌋₊)
    (hF : ∀ i < L, ¬ Fail n d i w) :
    ∀ i ≤ L, xs d i * ((n : ℝ) + 1) ≤ (Bset w i (T n i)).card := by
  intro i hi
  induction i with
  | zero =>
    have : Bset w 0 (T n 0) = Finset.univ := by
      unfold Bset; ext b; simp
    rw [this, Finset.card_univ, Fintype.card_fin]
    show (1 : ℝ) * ((n : ℝ) + 1) ≤ ((n + 1 : ℕ) : ℝ)
    push_cast; linarith
  | succ i ih =>
    have ih := ih (by omega)
    have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hβ : ⌈xs d i * ((n : ℝ) + 1)⌉₊ ≤ (Bset w i (T n i)).card := Nat.ceil_le.2 ih
    have hX : kap n d i ≤ (((Win n i).filter (fun s => ∀ k, w s k ∈ Bset w i (T n i))).card : ℝ) := by
      by_contra hc
      push_neg at hc
      exact hF i (by omega) ⟨hβ, hc⟩
    have hB : Bset w (i + 1) (T n (i + 1)) =
        Finset.univ.filter (fun b => i + 1 ≤ loadsAt w (T n (i + 1)) b) := rfl
    rcases level_step w _ i (T n i) (T n (i + 1)) hG (T_mono n i) (T_le n (i + 1)) with h | h
    · rw [← hB] at h
      have h1 : ((n : ℝ) + 1) / 96 < (Bset w (i + 1) (T n (i + 1))).card := by
        have h0 := Nat.lt_floor_add_one (((n : ℝ) + 1) / 96)
        have h' : ((⌊((n : ℝ) + 1) / 96⌋₊ : ℕ) : ℝ) + 1 ≤ (Bset w (i + 1) (T n (i + 1))).card := by
          exact_mod_cast h
        linarith
      have : xs d (i + 1) ≤ 1 / 96 := by rw [xs_succ]; exact min_le_left _ _
      calc xs d (i + 1) * ((n : ℝ) + 1) ≤ 1 / 96 * ((n : ℝ) + 1) := by gcongr
        _ ≤ _ := by linarith
    · rw [← hB] at h
      have hwin : (Finset.univ.filter (fun s : Fin (n + 1) =>
          T n i ≤ s.val ∧ s.val < T n (i + 1) ∧ ∀ k, i ≤ loadsAt w (T n i) (w s k))) =
          (Win n i).filter (fun s => ∀ k, w s k ∈ Bset w i (T n i)) := by
        ext s; simp [Win, Bset, and_assoc]
      rw [hwin] at h
      have h' : (((Win n i).filter (fun s => ∀ k, w s k ∈ Bset w i (T n i))).card : ℝ) ≤
          3 * (Bset w (i + 1) (T n (i + 1))).card := by exact_mod_cast h
      have hx : xs d (i + 1) ≤ xs d i ^ (d + 2) / (24 * 2 ^ i) := by
        rw [xs_succ]; exact min_le_right _ _
      have hk : kap n d i = ((n : ℝ) + 1) * (xs d i ^ (d + 2) / (24 * 2 ^ i)) * 3 := by
        unfold kap; rw [pow_add]; field_simp; ring
      calc xs d (i + 1) * ((n : ℝ) + 1) ≤ xs d i ^ (d + 2) / (24 * 2 ^ i) * ((n : ℝ) + 1) := by
            gcongr
        _ ≤ _ := by nlinarith

/-- number of levels -/
noncomputable def Lv (n d : ℕ) : ℕ := Nat.log (d + 2) ⌊Real.log ((n : ℝ) + 1) / 22⌋₊

theorem center_le (n d : ℕ) : center n d - 6 ≤ (Lv n d : ℝ) := by
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hD2 : (2 : ℝ) ≤ (d : ℝ) + 2 := by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hDl : 0 < Real.log ((d : ℝ) + 2) := Real.log_pos (by linarith)
  have hl2 : Real.log 2 ≤ Real.log ((d : ℝ) + 2) := Real.log_le_log (by norm_num) hD2
  have h22 : Real.log 22 ≤ 5 * Real.log 2 := by
    have : Real.log ((2 : ℝ) ^ 5) = 5 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]; exact Real.log_le_log (by norm_num) (by norm_num)
  set F := ⌊Real.log ((n : ℝ) + 1) / 22⌋₊ with hF
  have hlt : (F : ℝ) + 1 ≤ ((d : ℝ) + 2) ^ (Lv n d + 1) := by
    have := Nat.lt_pow_succ_log_self (show 1 < d + 2 by omega) F
    have h' : F + 1 ≤ (d + 2) ^ (Lv n d + 1) := this
    exact_mod_cast h'
  have hF1 : Real.log ((n : ℝ) + 1) / 22 < (F : ℝ) + 1 := Nat.lt_floor_add_one _
  unfold center
  push_cast
  rw [sub_le_iff_le_add, div_le_iff₀ hDl]
  rcases (Real.log_nonneg hN).eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    have : (0 : ℝ) ≤ Lv n d := Nat.cast_nonneg _
    nlinarith
  · have hpos : 0 < Real.log ((n : ℝ) + 1) / 22 := by positivity
    have h1 : Real.log (Real.log ((n : ℝ) + 1) / 22) < Real.log (((d : ℝ) + 2) ^ (Lv n d + 1)) :=
      Real.log_lt_log hpos (by linarith)
    rw [Real.log_pow, Real.log_div h0.ne' (by norm_num)] at h1
    push_cast at h1
    nlinarith

theorem Lv_le (n d : ℕ) : (Lv n d : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
  have hN : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hl0 := Real.log_nonneg hN
  by_cases hF : ⌊Real.log ((n : ℝ) + 1) / 22⌋₊ = 0
  · unfold Lv; rw [hF, Nat.log_zero_right]; simpa using hl0
  · have h1 : Lv n d < 2 ^ Lv n d := Nat.lt_two_pow_self
    have h2 : 2 ^ Lv n d ≤ (d + 2) ^ Lv n d := Nat.pow_le_pow_left (by omega) _
    have h3 : (d + 2) ^ Lv n d ≤ ⌊Real.log ((n : ℝ) + 1) / 22⌋₊ := Nat.pow_log_le_self _ hF
    have h4 : (Lv n d : ℝ) ≤ (⌊Real.log ((n : ℝ) + 1) / 22⌋₊ : ℝ) := by exact_mod_cast (h1.le.trans (h2.trans h3))
    have h5 := Nat.floor_le (show 0 ≤ Real.log ((n : ℝ) + 1) / 22 by positivity)
    linarith

theorem Dpow_le_log (n d i : ℕ) (hi : i < Lv n d) :
    ((d : ℝ) + 2) ^ (i + 1) ≤ Real.log ((n : ℝ) + 1) / 22 := by
  have hF : ⌊Real.log ((n : ℝ) + 1) / 22⌋₊ ≠ 0 := by
    intro h; unfold Lv at hi; rw [h, Nat.log_zero_right] at hi; omega
  have h2 : (d + 2) ^ (i + 1) ≤ (d + 2) ^ Lv n d := Nat.pow_le_pow_right (by omega) hi
  have h3 : (d + 2) ^ Lv n d ≤ ⌊Real.log ((n : ℝ) + 1) / 22⌋₊ := Nat.pow_log_le_self _ hF
  have h4 : (((d + 2) ^ (i + 1) : ℕ) : ℝ) ≤ (⌊Real.log ((n : ℝ) + 1) / 22⌋₊ : ℝ) := by
    exact_mod_cast h2.trans h3
  have h5 := Nat.floor_le (show 0 ≤ Real.log ((n : ℝ) + 1) / 22 by
    have := Real.log_nonneg (show (1 : ℝ) ≤ (n : ℝ) + 1 by
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    positivity)
  push_cast at h4
  linarith

theorem fail_bound (n d i : ℕ) (hi : i < Lv n d) :
    probability n d (Fail n d i) ≤ 4 / Real.sqrt ((n : ℝ) + 1) := by
  set N : ℝ := (n : ℝ) + 1 with hN
  have hNpos : 0 < N := by positivity
  have hD := Dpow_le_log n d i hi
  have hlogN : Real.log N ≤ N := by
    have := Real.log_le_sub_one_of_pos hNpos; linarith
  have h2D : (2 : ℝ) ^ (i + 1) ≤ ((d : ℝ) + 2) ^ (i + 1) := by
    gcongr; linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have h2N : (2 : ℝ) ^ (i + 2) ≤ N := by
    rw [pow_succ]; nlinarith
  have hm := card_win_ge n i h2N
  set β := ⌈xs d i * N⌉₊ with hβ
  have hx := xs_pos d i
  have hβN : xs d i ≤ (β : ℝ) / N := by
    rw [le_div_iff₀ hNpos]; exact Nat.le_ceil _
  set μ0 := N / 2 ^ (i + 2) * xs d i ^ (d + 2) with hμ0
  have hμ0pos : 0 < μ0 := by positivity
  have hμ : μ0 ≤ ((Win n i).card : ℝ) * ((β : ℝ) / N) ^ (d + 2) := by
    rw [hμ0]; gcongr
  -- μ0 ≥ √N
  have hstep := exp_g_step d i (xs d i) (xs_ge d i)
  have hg : g d (i + 1) ≤ Real.log N / 2 := by
    unfold g
    have h1 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    push_cast
    linarith
  have hsq : Real.sqrt N = Real.exp (Real.log N / 2) := by
    have : Real.exp (Real.log N / 2) ^ 2 = N := by
      rw [sq, ← Real.exp_add, add_halves, Real.exp_log hNpos]
    rw [← this, Real.sqrt_sq (Real.exp_pos _).le, this]
  have hsqrt : Real.sqrt N ≤ μ0 := by
    have e1 : Real.exp (-(Real.log N / 2)) ≤ xs d i ^ (d + 2) / (24 * 2 ^ i) :=
      le_trans (Real.exp_le_exp.2 (by linarith)) hstep
    have e2 : N * Real.exp (-(Real.log N / 2)) = Real.exp (Real.log N / 2) := by
      have h := Real.exp_log hNpos
      calc N * Real.exp (-(Real.log N / 2)) =
          Real.exp (Real.log N) * Real.exp (-(Real.log N / 2)) := by rw [h]
        _ = Real.exp (Real.log N / 2) := by rw [← Real.exp_add]; congr 1; ring
    have e3 : N * (xs d i ^ (d + 2) / (24 * 2 ^ i)) ≤ μ0 := by
      rw [hμ0, show (2 : ℝ) ^ (i + 2) = 4 * 2 ^ i by rw [pow_add]; ring]
      have : (0 : ℝ) ≤ N * xs d i ^ (d + 2) := by positivity
      rw [show N / (4 * 2 ^ i) * xs d i ^ (d + 2) = N * xs d i ^ (d + 2) / (4 * 2 ^ i) by ring,
        show N * (xs d i ^ (d + 2) / (24 * 2 ^ i)) = N * xs d i ^ (d + 2) / (24 * 2 ^ i) by ring]
      gcongr <;> norm_num
    rw [hsq, ← e2]
    calc N * Real.exp (-(Real.log N / 2)) ≤ N * (xs d i ^ (d + 2) / (24 * 2 ^ i)) := by gcongr
      _ ≤ μ0 := e3
  have hW : ∀ s ∈ Win n i, T n i ≤ s.val := by
    intro s hs; simp only [Win, Finset.mem_filter] at hs; exact hs.2.1
  have hph := phase_whp (d := d) i (T n i) β (Win n i) hW (kap n d i)
    (lt_of_lt_of_le hμ0pos hμ) (by unfold kap; rw [← hμ0]; linarith)
  refine le_trans hph ?_
  gcongr
  exact hsqrt.trans hμ

theorem prob_or {n d : ℕ} (P Q : Trace n d → Prop) :
    probability n d (fun w => P w ∨ Q w) ≤ probability n d P + probability n d Q := by
  classical
  have hQpos : (0 : ℝ) < Fintype.card (Trace n d) := by exact_mod_cast Fintype.card_pos
  have hsub : Finset.univ.filter (fun w => P w ∨ Q w) ⊆
      Finset.univ.filter P ∪ Finset.univ.filter Q := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hw ⊢
    exact hw
  have hc : ((Finset.univ.filter (fun w => P w ∨ Q w)).card : ℝ) ≤
      (Finset.univ.filter P).card + (Finset.univ.filter Q).card := by
    exact_mod_cast (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  rw [card_pred_eq (fun w => P w ∨ Q w), card_pred_eq P, card_pred_eq Q, ← add_mul] at hc
  exact le_of_mul_le_mul_right hc hQpos

theorem prob_compl {n d : ℕ} (P : Trace n d → Prop) :
    probability n d (fun w => ¬ P w) = 1 - probability n d P := by
  classical
  unfold probability
  have hQ : (Fintype.card (Trace n d) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (Trace n d) := Fintype.card_pos
    positivity
  rw [Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le _), sub_div, div_self hQ]

theorem main_bound (n d : ℕ) :
    1 - 6 / ((n : ℝ) + 1) - (Lv n d : ℝ) * (4 / Real.sqrt ((n : ℝ) + 1)) ≤
      probability n d (fun w => center n d - 6 ≤ (maxLoad n d w : ℝ)) := by
  classical
  set M := ⌊((n : ℝ) + 1) / 96⌋₊ with hM
  have hsucc : ∀ w : Trace n d, (Good w M ∧ ∀ i < Lv n d, ¬ Fail n d i w) →
      center n d - 6 ≤ (maxLoad n d w : ℝ) := by
    rintro w ⟨hG, hF⟩
    have h := levels w (Lv n d) hG hF (Lv n d) le_rfl
    have hpos : 0 < (Bset w (Lv n d) (T n (Lv n d))).card := by
      have : 0 < xs d (Lv n d) * ((n : ℝ) + 1) := by have := xs_pos d (Lv n d); positivity
      exact_mod_cast lt_of_lt_of_le this h
    obtain ⟨b, hb⟩ := Finset.card_pos.1 hpos
    have hb' : Lv n d ≤ loadsAt w (T n (Lv n d)) b := (Finset.mem_filter.1 hb).2
    have hm := maxLoad_ge w (Lv n d) b
      (hb'.trans (loadsAt_mono w (T_le n (Lv n d)) le_rfl b))
    have hc := center_le n d
    have : ((Lv n d : ℕ) : ℝ) ≤ (maxLoad n d w : ℝ) := by exact_mod_cast hm
    linarith
  have h1 := prob_mono (n := n) (d := d) hsucc
  have h2 : probability n d (fun w => ¬ (Good w M ∧ ∀ i < Lv n d, ¬ Fail n d i w)) ≤
      6 / ((n : ℝ) + 1) + (Lv n d : ℝ) * (4 / Real.sqrt ((n : ℝ) + 1)) := by
    refine le_trans (prob_mono (Q := fun w => (¬ Good w M) ∨
      ∃ i ∈ Finset.range (Lv n d), Fail n d i w) ?_) ?_
    · intro w hw
      by_cases hg : Good w M
      · right
        by_contra hc
        push_neg at hc
        exact hw ⟨hg, fun i hi => hc i (Finset.mem_range.2 hi)⟩
      · left; exact hg
    refine le_trans (prob_or _ _) (add_le_add ?_ ?_)
    · exact good_whp n d M (Nat.floor_le (by positivity))
    · refine le_trans (prob_union _ _) ?_
      calc ∑ i ∈ Finset.range (Lv n d), probability n d (Fail n d i)
          ≤ ∑ i ∈ Finset.range (Lv n d), 4 / Real.sqrt ((n : ℝ) + 1) :=
            Finset.sum_le_sum (fun i hi => fail_bound n d i (Finset.mem_range.1 hi))
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h3 := prob_compl (n := n) (d := d) (fun w => Good w M ∧ ∀ i < Lv n d, ¬ Fail n d i w)
  linarith

end ABKULow

open ABKUFinite in
theorem solution (d : ℕ) : Lower d := by
  refine ⟨6, by norm_num, fun ε hε => ?_⟩
  refine ⟨⌈(40 / ε) ^ 4⌉₊, fun n hn => ?_⟩
  have hb := ABKULow.main_bound n d
  have hL := ABKULow.Lv_le n d
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hNpos : 0 < N := by linarith
  set s := Real.sqrt N with hs
  set u := Real.sqrt s with hu
  have hs2 : s ^ 2 = N := Real.sq_sqrt hNpos.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = s := Real.sq_sqrt hs0
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hs1 : 1 ≤ s := by rw [hs]; rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
  have hu1 : 1 ≤ u := by rw [hu]; rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hs1
  have hupos : 0 < u := by linarith
  -- N ≥ (40/ε)^4 gives u ≥ 40/ε
  have hNε : (40 / ε) ^ 4 ≤ N := by
    have h1 := Nat.le_ceil ((40 / ε) ^ 4)
    have h2 : ((⌈(40 / ε) ^ 4⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hsε : (40 / ε) ^ 2 ≤ s := by
    have := Real.sqrt_le_sqrt hNε
    rwa [show (40 / ε) ^ 4 = ((40 / ε) ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)] at this
  have huε : 40 / ε ≤ u := by
    have := Real.sqrt_le_sqrt hsε
    rwa [Real.sqrt_sq (by positivity)] at this
  -- log N ≤ 4 u
  have hlog : Real.log N ≤ 4 * u := by
    have e : N = u ^ 4 := by rw [← hs2, ← hu2]; ring
    rw [e, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hupos
    push_cast; linarith
  have hεu : 22 / u ≤ ε := by
    rw [div_le_iff₀ hupos]
    have := (div_le_iff₀ hε).1 huε
    nlinarith
  have hterm1 : 6 / N ≤ 6 / u := by
    have : u ≤ N := by
      have e : N = u ^ 4 := by rw [← hs2, ← hu2]; ring
      rw [e]; nlinarith [pow_le_pow_right₀ hu1 (show 1 ≤ 4 by norm_num)]
    gcongr
  have hterm2 : (ABKULow.Lv n d : ℝ) * (4 / s) ≤ 16 / u := by
    have hL0 : (0 : ℝ) ≤ ABKULow.Lv n d := Nat.cast_nonneg _
    calc (ABKULow.Lv n d : ℝ) * (4 / s) ≤ (4 * u) * (4 / s) := by gcongr; linarith
      _ = 16 / u := by rw [← hu2]; field_simp; ring
  have hsum : 6 / u + 16 / u = 22 / u := by ring
  refine le_trans ?_ hb
  linarith
