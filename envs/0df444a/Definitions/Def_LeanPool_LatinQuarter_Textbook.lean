-- Prove2me | Definitions.Def_LeanPool_LatinQuarter_Textbook
-- name    : LeanPool_LatinQuarter_Textbook
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:22:56.758392+00:00
-- url     : https://prove2.me/theorems/6a2fbc6f-141e-4607-a637-a377acb03dcb
-- title:
--   Textbook
-- statement:
--   Definitions and structural lemmas for Textbook, from Richard Bean; LeanPool contributors's pinned Critical sets in Latin squares development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/LatinQuarter/Textbook.lean

module
public import Mathlib.SetTheory.Cardinal.Finite
public import Definitions.Def_LeanPool_LatinQuarter_Main
public import Definitions.Def_LeanPool_LatinQuarter_Parity
public import Theorems.Thm_LatinQuarter_allTagsExponent_apply
public import Theorems.Thm_LatinQuarter_allTagsExponent_support
public import Theorems.Thm_LatinQuarter_chosenSquare_clue
public import Theorems.Thm_LatinQuarter_chosenSquare_free
public import Theorems.Thm_LatinQuarter_chosenSquare_one
public import Theorems.Thm_LatinQuarter_mem_completions
public import Theorems.Thm_LatinQuarter_mem_cornerSet
public import Theorems.Thm_LatinQuarter_tag_sq
attribute [local simp] LatinQuarter.allTagsExponent_apply
attribute [local simp] LatinQuarter.allTagsExponent_support
attribute [local simp] LatinQuarter.chosenSquare_clue
attribute [local simp] LatinQuarter.chosenSquare_free
attribute [local simp] LatinQuarter.chosenSquare_one
attribute [local simp] LatinQuarter.mem_completions
attribute [local simp] LatinQuarter.mem_cornerSet
attribute [local simp] LatinQuarter.tag_sq


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace LatinQuarter.Textbook
def Latin {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ r s, ∃! c, L r c = s) ∧ (∀ c s, ∃! r, L r c = s)
def Completes {n : ℕ} (T : Finset (Fin n × Fin n × Fin n))
    (L : Fin n → Fin n → Fin n) : Prop :=
  Latin L ∧ ∀ t ∈ T, L t.1 t.2.1 = t.2.2
noncomputable def numCompletions {n : ℕ} (T : Finset (Fin n × Fin n × Fin n)) : ℕ :=
  Nat.card {L : Fin n → Fin n → Fin n // Completes T L}
def DefiningSet {n : ℕ} (L : Fin n → Fin n → Fin n)
    (T : Finset (Fin n × Fin n × Fin n)) : Prop :=
  Completes T L ∧ ∀ M, Completes T M → M = L
def CriticalSet {n : ℕ} (L : Fin n → Fin n → Fin n)
    (T : Finset (Fin n × Fin n × Fin n)) : Prop :=
  DefiningSet L T ∧ ∀ t ∈ T, 1 < numCompletions (T.erase t)
noncomputable def scsOf {n : ℕ} (L : Fin n → Fin n → Fin n) : ℕ :=
  sInf {m | ∃ T, CriticalSet L T ∧ T.card = m}
noncomputable def scs (n : ℕ) : ℕ :=
  sInf {m | ∃ L : Fin n → Fin n → Fin n, Latin L ∧ scsOf L = m}
def cyclicSquare (n : ℕ) : Fin n → Fin n → Fin n :=
  fun r c => ⟨(r.val + c.val) % n, Nat.mod_lt _ r.pos⟩
theorem latin_iff {n : ℕ} (L : Fin n → Fin n → Fin n) : Latin L ↔ IsLatin L := by
  simp only [Latin, IsLatin, Function.bijective_iff_existsUnique]
example : ¬ DefiningSet (cyclicSquare 2) ∅ := by
  rintro ⟨_, huniq⟩
  have hM : Completes (∅ : Finset (Fin 2 × Fin 2 × Fin 2)) (fun r c => r + c + 1) :=
    ⟨(latin_iff _).mpr (by unfold IsLatin; decide), by simp⟩
  have h := congrFun (congrFun (huniq _ hM) 0) 0
  revert h
  decide
end LatinQuarter.Textbook


