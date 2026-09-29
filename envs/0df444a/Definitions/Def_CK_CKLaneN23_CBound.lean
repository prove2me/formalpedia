-- Prove2me | Definitions.Def_CK_CKLaneN23_CBound
-- name    : CK_CKLaneN23_CBound
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:59:15.692712+00:00
-- url     : https://prove2.me/theorems/dc09440b-3e82-49ff-b640-da1b9268d0c1
-- title:
--   Courtade–Kumar proof module `CKLaneN23.CBound` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `CKLaneN23.CBound` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `CKLaneN23.CBound` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module CKLaneN23.CBound (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/CKLaneN23/CBound.lean)

import Definitions.Def_CK_CKLaneN23_CPoly
import Mathlib.Analysis.Complex.ExponentialBounds

-- ===== source module CKLaneN23.CBound =====
section

/-!
# CKLaneN23.CBound — rigorous magnitude bounds for the corner Taylor-model checker

(Adapted from Lane A3's `CKLaneA3.Bound`; two parameters.)
`L ∈ [Llo, Lhi]` (Mathlib `Real.log_two_gt_d9`, `Real.log_two_lt_d9`), `|σ| ≤ 1/2`, `|τ| ≤ 1/2`,
`0 ≤ s ≤ Eps` (the corner radius).  All bound functions are kernel-evaluable.
-/

namespace CKLaneN23.CT

def Llo : ℚ := 6931471803 / 10000000000
def Lhi : ℚ := 6931471808 / 10000000000
/-- corner radius in the scale `s = (1/2 - b) + d` -/
def Eps : ℚ := 1 / 20

noncomputable def qpow (x : ℚ) (k : ℕ) : ℚ := Nat.rec (motive := fun _ => ℚ) 1 (fun _ ih => ih * x) k

theorem qpow_zero (x : ℚ) : qpow x 0 = 1 := rfl
theorem qpow_succ (x : ℚ) (k : ℕ) : qpow x (k + 1) = qpow x k * x := rfl

theorem qpow_eq (x : ℚ) (k : ℕ) : qpow x k = x ^ k := by
  induction k with
  | zero => simp [qpow_zero]
  | succ k ih => rw [qpow_succ, ih, pow_succ]

noncomputable def Lpow : ℤ → ℚ × ℚ
  | Int.ofNat k => (qpow Llo k, qpow Lhi k)
  | Int.negSucc k => (qpow (1 / Lhi) (k + 1), qpow (1 / Llo) (k + 1))

theorem Llo_pos : (0 : ℚ) < Llo := by norm_num [Llo]

theorem Lpow_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (c : ℤ) :
    ((Lpow c).1 : ℝ) ≤ L ^ c ∧ L ^ c ≤ ((Lpow c).2 : ℝ) := by
  have hlo : (0 : ℝ) < (Llo : ℝ) := by exact_mod_cast Llo_pos
  have hL : 0 < L := lt_of_lt_of_le hlo h1
  cases c with
  | ofNat k =>
    simp only [Lpow, qpow_eq, zpow_natCast, Int.ofNat_eq_natCast]
    push_cast
    exact ⟨pow_le_pow_left₀ hlo.le h1 k, pow_le_pow_left₀ hL.le h2 k⟩
  | negSucc k =>
    simp only [Lpow, qpow_eq, zpow_negSucc]
    push_cast
    constructor
    · rw [one_div, inv_pow]
      exact inv_anti₀ (pow_pos hL _) (pow_le_pow_left₀ hL.le h2 _)
    · rw [one_div, inv_pow]
      exact inv_anti₀ (pow_pos hlo _) (pow_le_pow_left₀ hlo.le h1 _)

noncomputable def termIntv (c : ℤ) (q : ℚ) : ℚ × ℚ :=
  if 0 ≤ q then (q * (Lpow c).1, q * (Lpow c).2) else (q * (Lpow c).2, q * (Lpow c).1)

theorem termIntv_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (c : ℤ) (q : ℚ) :
    ((termIntv c q).1 : ℝ) ≤ (q : ℝ) * L ^ c ∧ (q : ℝ) * L ^ c ≤ ((termIntv c q).2 : ℝ) := by
  obtain ⟨a, b⟩ := Lpow_spec h1 h2 c
  unfold termIntv
  split_ifs with hq
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    push_cast
    exact ⟨mul_le_mul_of_nonneg_left a hq', mul_le_mul_of_nonneg_left b hq'⟩
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hq))
    push_cast
    exact ⟨mul_le_mul_of_nonpos_left b hq', mul_le_mul_of_nonpos_left a hq'⟩

noncomputable def LPoly.intv (l : LPoly) : ℚ × ℚ :=
  @List.rec (ℤ × ℚ) (fun _ => ℚ × ℚ) (0, 0)
    (fun m _ ih => ((termIntv m.1 m.2).1 + ih.1, (termIntv m.1 m.2).2 + ih.2)) l

theorem LPoly.intv_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (l : LPoly) :
    ((LPoly.intv l).1 : ℝ) ≤ LPoly.eval L l ∧ LPoly.eval L l ≤ ((LPoly.intv l).2 : ℝ) := by
  induction l with
  | nil => simp [LPoly.intv, LPoly.eval_nil]
  | cons m t ih =>
    obtain ⟨a, b⟩ := termIntv_spec h1 h2 m.1 m.2
    show (((termIntv m.1 m.2).1 + (LPoly.intv t).1 : ℚ) : ℝ) ≤ _ ∧
      _ ≤ (((termIntv m.1 m.2).2 + (LPoly.intv t).2 : ℚ) : ℝ)
    rw [LPoly.eval_cons]; push_cast
    exact ⟨add_le_add a ih.1, add_le_add b ih.2⟩

noncomputable def LPoly.absB (l : LPoly) : ℚ := max (|(LPoly.intv l).1|) (|(LPoly.intv l).2|)

theorem LPoly.absB_spec {L : ℝ} (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (l : LPoly) :
    |LPoly.eval L l| ≤ (LPoly.absB l : ℝ) := by
  obtain ⟨a, b⟩ := LPoly.intv_spec h1 h2 l
  unfold LPoly.absB
  push_cast
  rw [abs_le]
  constructor
  · have : -((|((LPoly.intv l).1 : ℝ)|)) ≤ ((LPoly.intv l).1 : ℝ) := neg_abs_le _
    have hm : (|((LPoly.intv l).1 : ℝ)|) ≤ max (|((LPoly.intv l).1 : ℝ)|) (|((LPoly.intv l).2 : ℝ)|) :=
      le_max_left _ _
    linarith
  · have : ((LPoly.intv l).2 : ℝ) ≤ (|((LPoly.intv l).2 : ℝ)|) := le_abs_self _
    have hm : (|((LPoly.intv l).2 : ℝ)|) ≤ max (|((LPoly.intv l).1 : ℝ)|) (|((LPoly.intv l).2 : ℝ)|) :=
      le_max_right _ _
    linarith

/-- `|σ|, |τ| ≤ 1/2` bound for a `QPoly`. -/
noncomputable def QPoly.absB (s : QPoly) : ℚ :=
  @List.rec ((ℕ × ℕ) × LPoly) (fun _ => ℚ) 0
    (fun m _ ih => qpow (1 / 2) m.1.1 * qpow (1 / 2) m.1.2 * LPoly.absB m.2 + ih) s

theorem QPoly.absB_spec {σ τ L : ℝ} (hσ : |σ| ≤ 1 / 2) (hτ : |τ| ≤ 1 / 2)
    (h1 : (Llo : ℝ) ≤ L) (h2 : L ≤ (Lhi : ℝ)) (s : QPoly) :
    |QPoly.eval σ τ L s| ≤ (QPoly.absB s : ℝ) := by
  induction s with
  | nil => simp [QPoly.absB, QPoly.eval_nil]
  | cons m t ih =>
    show |QPoly.eval σ τ L (m :: t)| ≤
      ((qpow (1 / 2) m.1.1 * qpow (1 / 2) m.1.2 * LPoly.absB m.2 + QPoly.absB t : ℚ) : ℝ)
    rw [QPoly.eval_cons]
    push_cast
    rw [qpow_eq, qpow_eq]; push_cast
    have hl := LPoly.absB_spec h1 h2 m.2
    have hp : |σ ^ m.1.1| ≤ (1 / 2 : ℝ) ^ m.1.1 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hσ _
    have hq : |τ ^ m.1.2| ≤ (1 / 2 : ℝ) ^ m.1.2 := by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hτ _
    calc |σ ^ m.1.1 * τ ^ m.1.2 * LPoly.eval L m.2 + QPoly.eval σ τ L t|
        ≤ |σ ^ m.1.1 * τ ^ m.1.2 * LPoly.eval L m.2| + |QPoly.eval σ τ L t| := abs_add_le _ _
      _ = |σ ^ m.1.1| * |τ ^ m.1.2| * |LPoly.eval L m.2| + |QPoly.eval σ τ L t| := by
          rw [abs_mul, abs_mul]
      _ ≤ (1 / 2 : ℝ) ^ m.1.1 * (1 / 2 : ℝ) ^ m.1.2 * (LPoly.absB m.2 : ℝ) + (QPoly.absB t : ℝ) := by
          apply add_le_add _ ih
          apply mul_le_mul (mul_le_mul hp hq (abs_nonneg _) (by positivity)) hl (abs_nonneg _)
          positivity

theorem log2_lo : ((Llo : ℚ) : ℝ) ≤ Real.log 2 := by
  have := Real.log_two_gt_d9
  unfold Llo; push_cast; norm_num at this ⊢; linarith

theorem log2_hi : Real.log 2 ≤ ((Lhi : ℚ) : ℝ) := by
  have := Real.log_two_lt_d9
  unfold Lhi; push_cast; norm_num at this ⊢; linarith

/-! ## entry bounds for TPoly -/

def EntryBnd (P : TPoly) (β : List ℚ) : Prop :=
  List.Forall₂ (fun (s : QPoly) (b : ℚ) => ∀ σ τ : ℝ, |σ| ≤ 1 / 2 → |τ| ≤ 1 / 2 →
    |QPoly.eval σ τ (Real.log 2) s| ≤ (b : ℝ)) P β

noncomputable def entryCheck (P : TPoly) (β : List ℚ) : Bool :=
  @List.rec QPoly (fun _ => List ℚ → Bool) (fun β => β.isEmpty)
    (fun s _ ih => fun β => @List.rec ℚ (fun _ => Bool) false
      (fun b β' _ => decide (QPoly.absB s ≤ b) && ih β') β) P β

theorem entryBnd_of_check (P : TPoly) (β : List ℚ) (h : entryCheck P β = true) : EntryBnd P β := by
  induction P generalizing β with
  | nil =>
    cases β with
    | nil => exact List.Forall₂.nil
    | cons b β => simp [entryCheck] at h
  | cons s P ih =>
    cases β with
    | nil => simp [entryCheck] at h
    | cons b β =>
      have h' : decide (QPoly.absB s ≤ b) = true ∧ entryCheck P β = true := by
        have : entryCheck (s :: P) (b :: β) = (decide (QPoly.absB s ≤ b) && entryCheck P β) := rfl
        rw [this] at h; simpa using h
      refine List.Forall₂.cons ?_ (ih β h'.2)
      intro σ τ hσ hτ
      have hb : QPoly.absB s ≤ b := by simpa using h'.1
      have := QPoly.absB_spec hσ hτ log2_lo log2_hi s
      exact this.trans (by exact_mod_cast hb)

/-! ## sums of entry bounds -/

/-- `Σ β_i Eps^i` (Horner). -/
noncomputable def bsum (β : List ℚ) : ℚ := @List.rec ℚ (fun _ => ℚ) 0 (fun b _ ih => b + Eps * ih) β

noncomputable def ldrop (β : List ℚ) : ℕ → List ℚ :=
  @List.rec ℚ (fun _ => ℕ → List ℚ) (fun _ => [])
    (fun b β' ih => fun k => Nat.rec (motive := fun _ => List ℚ) (b :: β') (fun k' _ => ih k') k) β

theorem ldrop_zero (β : List ℚ) : ldrop β 0 = β := by cases β <;> rfl
theorem ldrop_nil (k : ℕ) : ldrop [] k = [] := rfl
theorem ldrop_cons_succ (b : ℚ) (β : List ℚ) (k : ℕ) : ldrop (b :: β) (k + 1) = ldrop β k := rfl

def Nonneg (β : List ℚ) : Prop := ∀ b ∈ β, 0 ≤ b

theorem Eps_pos : (0 : ℚ) < Eps := by norm_num [Eps]

theorem bsum_nonneg (β : List ℚ) (h : Nonneg β) : 0 ≤ bsum β := by
  induction β with
  | nil => simp [bsum]
  | cons b β ih =>
    show 0 ≤ b + Eps * bsum β
    have hb : 0 ≤ b := h b (List.mem_cons_self)
    have hr : 0 ≤ bsum β := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have : (0 : ℚ) ≤ Eps := Eps_pos.le
    positivity

theorem EntryBnd.nonneg {P : TPoly} {β : List ℚ} (h : EntryBnd P β) : Nonneg β := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons hsb _ ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb'
    · have := hsb 0 0 (by norm_num) (by norm_num)
      have h0 : (0 : ℝ) ≤ _ := (abs_nonneg _).trans this
      exact_mod_cast h0
    · exact ih b hb'

theorem ldrop_nonneg (β : List ℚ) (h : Nonneg β) (k : ℕ) : Nonneg (ldrop β k) := by
  induction β generalizing k with
  | nil => simp [ldrop_nil, Nonneg]
  | cons b β ih =>
    cases k with
    | zero => rw [ldrop_zero]; exact h
    | succ k =>
      rw [ldrop_cons_succ]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) k

theorem EntryBnd.eval_le {P : TPoly} {β : List ℚ} (h : EntryBnd P β) {x σ τ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ (Eps : ℝ)) (hσ : |σ| ≤ 1 / 2) (hτ : |τ| ≤ 1 / 2) :
    |TPoly.eval x σ τ (Real.log 2) P| ≤ (bsum β : ℝ) := by
  induction h with
  | nil => simp [TPoly.eval_nil, bsum]
  | @cons s b P' β' hsb _ ih =>
    rw [TPoly.eval_cons]
    show _ ≤ ((b + Eps * bsum β' : ℚ) : ℝ)
    push_cast
    have h1 := hsb σ τ hσ hτ
    have hnn : (0 : ℝ) ≤ bsum β' := (abs_nonneg _).trans ih
    have hE : (0 : ℝ) ≤ (Eps : ℝ) := by exact_mod_cast Eps_pos.le
    calc |QPoly.eval σ τ (Real.log 2) s + x * TPoly.eval x σ τ (Real.log 2) P'|
        ≤ |QPoly.eval σ τ (Real.log 2) s| + |x| * |TPoly.eval x σ τ (Real.log 2) P'| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ (b : ℝ) + (Eps : ℝ) * (bsum β' : ℝ) := by
          apply add_le_add h1
          rw [abs_of_nonneg hx0]
          exact mul_le_mul hx ih (abs_nonneg _) hE

theorem EntryBnd.drop {P : TPoly} {β : List ℚ} (h : EntryBnd P β) (k : ℕ) :
    EntryBnd (TPoly.drop P k) (ldrop β k) := by
  induction h generalizing k with
  | nil => exact List.Forall₂.nil
  | @cons s b P' β' hsb hrest ih =>
    cases k with
    | zero => rw [TPoly.drop_zero, ldrop_zero]; exact List.Forall₂.cons hsb hrest
    | succ k => rw [TPoly.drop_cons_succ, ldrop_cons_succ]; exact ih k

end CKLaneN23.CT

end


