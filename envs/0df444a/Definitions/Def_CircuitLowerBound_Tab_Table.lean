-- Prove2me | Definitions.Def_CircuitLowerBound_Tab_Table
-- name    : CircuitLowerBound_Tab_Table
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T17:57:15.790624+00:00
-- url     : https://prove2.me/theorems/fd7afa12-22a9-44fc-a9f3-6be87e569118
-- title:
--   Table
-- statement:
--   Definitions and structural lemmas for Table, from Anthropic’s pinned ETH development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Tab/Table.lean

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Tab_Frame
import Mathlib.Tactic
import Theorems.Thm_Groundwork_length_toWord
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.length_toWord
attribute [local simp] Groundwork.mem_words


set_option autoImplicit false
section
section
@[expose] section
namespace CircuitLowerBound.Tab
open ENP Turing
variable (N : TM2ComputableAux Bool Bool)
abbrev YLit : Type := Atom N × ℕ × ℕ × ℕ × Bool
abbrev YCl : Type := YLit N × YLit N × YLit N
variable {N}
def holdsY (α : Atom N → ℕ → ℕ → Bool) (b P t q : ℕ) (l : YLit N) : Prop := α l.1 (tval b t l.2.1) (qval P q l.2.2.1 + l.2.2.2.1) = l.2.2.2.2
def HoldsC (α : Atom N → ℕ → ℕ → Bool) (b Q P : ℕ) (c : YCl N) : Prop :=
  ∀ t < 2 ^ b, ∀ q < 2 ^ Q, holdsY α b P t q c.1 ∨ holdsY α b P t q c.2.1 ∨ holdsY α b P t q c.2.2
def c1 (l : YLit N) : YCl N := (l, l, l)
def c2 (l l' : YLit N) : YCl N := (l, l', l')
def taut : YCl N := ((.u, 0, 0, 0, false), (.u, 0, 0, 0, true), (.u, 0, 0, 0, true))
noncomputable def en (ι : Type) [Finite ι] : List ι := (@Finset.univ ι (Fintype.ofFinite ι)).toList
noncomputable def fam {ι : Type} [Finite ι] (f : ι → YCl N) : List (YCl N) := (en ι).map f
variable (N) [Finite (Case N)] [∀ k, Finite (N.tm.Γ k)]
open Classical in
/-- The table, with atoms as kinds. -/
noncomputable def table : List (YCl N) := List.flatten [
  [c1 (.pre (Fin.last _), 1, 0, 0, true)],
  [c1 (.pre 0, 1, 0, 0, false)],
  fam fun i : Fin (nc N) => ((.pre i.succ, 1, 0, 0, false), (.pre i.castSucc, 1, 0, 0, true), (.cs ((ec N).symm i), 1, 0, 0, true)),
  fam fun γ : Case N => c2 (.cs γ, 1, 0, 0, false) (.lab γ.1, 1, 0, 0, true),
  fam fun γ : Case N => c2 (.cs γ, 1, 0, 0, false) (.var γ.2.1, 1, 0, 0, true),
  fam fun p : Case N × N.tm.K × Fin (dep N) => c2 (.cs p.1, 1, 0, 0, false) (.cell p.2.1 (p.1.2.2 p.2.1 p.2.2), 1, 0, p.2.2, true),
  fam fun p : Case N × Option N.tm.Λ => c2 (.cs p.1, 1, 0, 0, false) (.lab p.2, 2, 0, 0, decide (p.2 = (nxt N p.1).l)),
  fam fun p : Case N × N.tm.σ => c2 (.cs p.1, 1, 0, 0, false) (.var p.2, 2, 0, 0, decide (p.2 = (nxt N p.1).var)),
  fam fun p : Case N × N.tm.K × Fin (2 * dep N + 1) =>
    c2 (.cs p.1, 1, 0, 0, false) (.len p.2.1 p.2.2, 1, 0, 0, decide ((p.2.2 : ℕ) = ((nxt N p.1).stk p.2.1).length)),
  fam fun p : Case N × (Σ k, Option (N.tm.Γ k)) × Fin (2 * dep N) =>
    if (p.2.2 : ℕ) < ((nxt N p.1).stk p.2.1.1).length then
      c2 (.cs p.1, 1, 0, 0, false) (.cell p.2.1.1 p.2.1.2, 2, 0, p.2.2, decide (p.2.1.2 = ((nxt N p.1).stk p.2.1.1)[(p.2.2 : ℕ)]?))
    else taut,
  fam fun p : (Σ k, Option (N.tm.Γ k)) × Fin (2 * dep N + 1) =>
    ((.len p.1.1 p.2, 1, 0, 0, false), (.cell p.1.1 p.1.2, 2, 1, p.2, false), (.cell p.1.1 p.1.2, 1, 1, dep N, true)),
  fam fun p : (Σ k, Option (N.tm.Γ k)) × Fin (2 * dep N + 1) =>
    ((.len p.1.1 p.2, 1, 0, 0, false), (.cell p.1.1 p.1.2, 2, 1, p.2, true), (.cell p.1.1 p.1.2, 1, 1, dep N, false)),
  fam fun x : Option N.tm.Λ => c1 (.lab x, 0, 0, 0, decide (x = some N.tm.main)),
  fam fun x : N.tm.σ => c1 (.var x, 0, 0, 0, decide (x = N.tm.initialState)),
  fam fun p : Σ k, Option (N.tm.Γ k) => if p.1 ≠ N.tm.k₀ then c1 (.cell p.1 p.2, 0, 1, 0, decide (p.2 = none)) else taut,
  [((.cell N.tm.k₀ none, 0, 1, 0, true), (.cell N.tm.k₀ (some (N.inputAlphabet.symm false)), 0, 1, 0, true), (.cell N.tm.k₀ (some (N.inputAlphabet.symm true)), 0, 1, 0, true))],
  fam fun p : Option (N.tm.Γ N.tm.k₀) × Option (N.tm.Γ N.tm.k₀) =>
    if p.1 ≠ p.2 then c2 (.cell N.tm.k₀ p.1, 0, 1, 0, false) (.cell N.tm.k₀ p.2, 0, 1, 0, false) else taut,
  [c2 (.cell N.tm.k₀ none, 0, 1, 0, false) (.cell N.tm.k₀ none, 0, 1, 1, true)],
  [c2 (.u, 0, 1, 1, false) (.u, 0, 1, 0, true)],
  [c1 (.u, 0, 2, 0, true)],
  [c1 (.u, 0, 2, 1, false)],
  [c2 (.u, 0, 1, 1, false) (.cell N.tm.k₀ (some (N.inputAlphabet.symm true)), 0, 1, 0, true)],
  [c1 (.cell N.tm.k₀ (some (N.inputAlphabet.symm false)), 0, 2, 0, true)],
  [c1 (.lab none, 3, 0, 0, true)],
  [c1 (.var N.tm.initialState, 3, 0, 0, true)],
  [c1 (.cell N.tm.k₁ (some (N.outputAlphabet.symm true)), 3, 0, 0, true)],
  [c1 (.cell N.tm.k₁ none, 3, 0, 1, true)],
  fam fun k : N.tm.K => if k ≠ N.tm.k₁ then c1 (.cell k none, 3, 0, 0, true) else taut]
variable {N}
instance : Finite (Atom N) := by
  let f : Atom N → Option N.tm.Λ ⊕ N.tm.σ ⊕ (N.tm.K × Fin (2 * dep N + 1)) ⊕ (Σ k, Option (N.tm.Γ k)) ⊕ Case N ⊕ Fin (nc N + 1) ⊕ Unit := fun a =>
    match a with
    | .lab l => .inl l
    | .var v => .inr (.inl v)
    | .len k n => .inr (.inr (.inl (k, n)))
    | .cell k x => .inr (.inr (.inr (.inl ⟨k, x⟩)))
    | .cs γ => .inr (.inr (.inr (.inr (.inl γ))))
    | .pre i => .inr (.inr (.inr (.inr (.inr (.inl i)))))
    | .u => .inr (.inr (.inr (.inr (.inr (.inr ())))))
  refine Finite.of_injective f fun a a' h => ?_
  cases a <;> cases a' <;> simp only [f, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq, Sigma.mk.injEq] at h
  · rw [h]
  · rw [h]
  · rw [h.1, h.2]
  · obtain ⟨rfl, h⟩ := h; rw [eq_of_heq h]
  · rw [h]
  · rw [h]
  · rfl
noncomputable def num (a : Atom N) : ℕ := (Finite.equivFin (Atom N) a : ℕ) + 1
noncomputable def nl (l : YLit N) : TLit := (num l.1, l.2)
variable (N) in
/-- The table with numbers as kinds. -/
noncomputable def codeTab : MCode := (Nat.size (Nat.card (Atom N) + 1), lamOf N, (table N).map fun c => (nl c.1, nl c.2.1, nl c.2.2))
end CircuitLowerBound.Tab
namespace CircuitLowerBound
open Tab Turing
end CircuitLowerBound


