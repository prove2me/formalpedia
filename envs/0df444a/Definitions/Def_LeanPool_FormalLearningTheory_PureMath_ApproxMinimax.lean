-- Prove2me | Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
-- name    : LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T05:31:40.098594+00:00
-- url     : https://prove2.me/theorems/5ea636d5-8475-41ef-b4f3-4cdbc030619c
-- title:
--   Approx Minimax
-- statement:
--   Definitions and structural lemmas for Approx Minimax, from Dhruv Gupta; LeanPool contributors's pinned Formal Learning Theory Kernel development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/PureMath/ApproxMinimax.lean

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset
noncomputable section
def normalizeToPMF {C : Type*} [Fintype C] [Nonempty C]
    (w : C → ℝ) (hw : ∀ c, 0 < w c) : FinitePMF C where
  prob c := w c / ∑ c' : C, w c'
  prob_nonneg c :=
    div_nonneg (le_of_lt (hw c))
      (Finset.sum_nonneg fun c' _ => le_of_lt (hw c'))
  prob_sum_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (Finset.sum_pos (fun c _ => hw c) univ_nonempty))
def pointMassPMF {C : Type*} [Fintype C] [DecidableEq C] (c₀ : C) :
    FinitePMF C where
  prob c := if c = c₀ then 1 else 0
  prob_nonneg c := by split_ifs <;> norm_num
  prob_sum_one := by simp [sum_ite_eq']
def uniformPMF (C : Type*) [Fintype C] [Nonempty C] : FinitePMF C :=
  normalizeToPMF (fun _ => (1 : ℝ)) fun _ => one_pos
def empiricalPMF {α : Type*} [Fintype α] [DecidableEq α]
    {T : ℕ} (hT : 0 < T) (rs : Fin T → α) : FinitePMF α where
  prob a := (univ.filter (fun t => rs t = a)).card / (T : ℝ)
  prob_nonneg a := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  prob_sum_one := by
    rw [← Finset.sum_div]
    suffices h : (∑ a : α, ((univ.filter (fun t : Fin T => rs t = a)).card : ℝ)) = T by
      rw [h]; exact div_self (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hT))
    -- Use card_eq_sum_card_fiberwise: #s = Σ_{b ∈ t} #{a ∈ s | f a = b}
    have hfib := Finset.card_eq_sum_card_fiberwise
      (f := rs) (s := univ) (t := univ)
      (fun t _ => mem_univ (rs t))
    simp_all
def boolGamePayoff {R C : Type*} [Fintype R]
    (M : R → C → Bool) (p : FinitePMF R) (c : C) : ℝ :=
  ∑ r : R, p.prob r * (if M r c then (1 : ℝ) else 0)
structure MWUConfig (C : Type*) [Fintype C] where
  /-- Current nonnegative weight for each expert/concept. -/
  weights : C → ℝ
  weights_pos : ∀ c, 0 < weights c
def MWUConfig.potential {C : Type*} [Fintype C] (cfg : MWUConfig C) : ℝ :=
  ∑ c : C, cfg.weights c
def mwuInit (C : Type*) [Fintype C] : MWUConfig C where
  weights := fun _ => 1
  weights_pos := fun _ => one_pos
def MWUConfig.toPMF {C : Type*} [Fintype C] [Nonempty C]
    (cfg : MWUConfig C) : FinitePMF C :=
  normalizeToPMF cfg.weights cfg.weights_pos
def mwuUpdateWeights {C : Type*} [Fintype C] {R : Type*}
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1)
    (cfg : MWUConfig C) (r : R) : MWUConfig C where
  weights c := cfg.weights c * (if M r c then (1 - η) else 1)
  weights_pos c := mul_pos (cfg.weights_pos c) (by split_ifs <;> linarith)
def mwuRun {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    (T : ℕ) → MWUConfig C × (Fin T → R)
  | 0 => (mwuInit C, Fin.elim0)
  | T + 1 =>
    let ⟨cfg, rows⟩ := mwuRun M η hη1 v hrow T
    let r := (hrow cfg.toPMF).choose
    (mwuUpdateWeights M η hη1 cfg r, Fin.snoc rows r)
abbrev mwuConfig {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) : MWUConfig C :=
  (mwuRun M η hη1 v hrow T).1
abbrev mwuRows {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0))
    (T : ℕ) : Fin T → R :=
  (mwuRun M η hη1 v hrow T).2
def mwuHitCount
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (η : ℝ) (hη1 : η < 1) (v : ℝ)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    (T : ℕ) → C → ℕ
  | 0, _ => 0
  | T + 1, c =>
      let cfg := mwuConfig M η hη1 v hrow T
      let r := (hrow cfg.toPMF).choose
      mwuHitCount M η hη1 v hrow T c + if M r c then 1 else 0
end


