-- Prove2me | Definitions.Def_DegreeSeqLib_DegreeSequences
-- name    : DegreeSeqLib_DegreeSequences
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T14:28:52.172236+00:00
-- url     : https://prove2.me/theorems/dbc4160c-efea-59df-8967-62a0c7f1f2f1
-- title:
--   Degree Sequences
-- statement:
--   Definitions and structural lemmas for Degree Sequences, from Juan Pablo Traverso Gianini (jtraverso/degree-sequences; see pinned Apache-2.0 LICENSE and source headers)'s pinned Graphic sequences: the Erdos-Gallai and Havel-Hakimi theorems development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/degree-sequences/blob/b49808e0c0aade945472b777047148399a582858/DegreeSeqLib/DegreeSequences.lean

module
public import Mathlib
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace DegreeSequences
def IsGraphic {n : ℕ} (d : Fin n → ℕ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj), ∀ i, G.degree i = d i
def havelHakimi {m : ℕ} (d : Fin (m + 1) → ℕ) : Fin m → ℕ :=
  fun j => if j.val < d 0 then d j.succ - 1 else d j.succ
def editGraph {V : Type*} (G : SimpleGraph V) (R A : Finset (Sym2 V)) : SimpleGraph V where
  Adj x y := x ≠ y ∧ ((G.Adj x y ∧ s(x, y) ∉ R) ∨ s(x, y) ∈ A)
  symm := ⟨by
    intro x y h
    obtain ⟨h1, h2⟩ := h
    refine ⟨h1.symm, ?_⟩
    have hs : s(y, x) = s(x, y) := Sym2.eq_swap
    rw [hs]
    rcases h2 with ⟨h2, h3⟩ | h2
    · exact Or.inl ⟨h2.symm, h3⟩
    · exact Or.inr h2⟩
  loopless := ⟨fun x h => h.1 rfl⟩
def hhExtend {m : ℕ} (d : Fin (m + 1) → ℕ) (H : SimpleGraph (Fin m)) :
    SimpleGraph (Fin (m + 1)) :=
  SimpleGraph.fromRel fun v w =>
    (v = 0 ∧ ∃ j : Fin m, w = j.succ ∧ j.val < d 0) ∨
      (∃ j k : Fin m, v = j.succ ∧ w = k.succ ∧ H.Adj j k)
def hhSet {m : ℕ} (d : Fin (m + 1) → ℕ) : Finset (Fin (m + 1)) :=
  ({v : Fin (m + 1) | v.val < d 0 + 1} : Finset _).erase 0
def egReduce {n : ℕ} (d : Fin n → ℕ) (t p : Fin n) : Fin n → ℕ :=
  fun i => d i - (if i = t then 1 else 0) - (if i = p then 1 else 0)
end DegreeSequences


