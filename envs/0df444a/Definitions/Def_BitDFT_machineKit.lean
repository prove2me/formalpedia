-- Prove2me | Definitions.Def_BitDFT_machineKit
-- name    : BitDFT_machineKit
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T01:45:41.343251+00:00
-- url     : https://prove2.me/theorems/da3490ef-f217-4f0b-a3b3-cab3bd9c83f8
-- title:
--   Machine constructor with the multitape structural axioms discharged
-- statement:
--   A constructor for the platform's deterministic multitape Turing machines that takes only the data of a machine — a number of tapes, a finite state type with a start state, and a transition function — and produces a machine whose four structural obligations are already met: the start symbol is never overwritten and never stepped left from, the start symbol is never written on a cell that does not already hold it, the halting state is fixed, and the input tape is read-only.
--
--   Two guards make this uniform. The transition function is applied through `guardSpec`, which forces every tape that scans the start symbol to rewrite it and stay put, and forces tape 0 to keep its symbol; and the state set is `Option Q`, with `none` as the halting state and the fixed transition there. The alphabet is a fixed seven-symbol type containing the blank, the start symbol, both bits, the separator, and two markers.
--
--   With this constructor a machine is specified by its transition function alone, so a proof obligation about a concrete machine reduces to reasoning about that function rather than about the structure axioms.
-- source:
--   Internal: construction kit for the machine proofs of the Prove2me theorems BitDFT.unpacking_machine and BitDFT.packing_machine (https://prove2.me/theorems/3a9d0791-96d8-4079-919b-de51b895da98). Model from IntMul_MultitapeModel.

import Mathlib
import Definitions.Def_IntMul_MultitapeModel

set_option autoImplicit false
noncomputable section

/-! A machine constructor that discharges the four structural axioms of `IntMul.MultitapeTM`
once and for all, so that a machine is specified by its transition function alone. -/

namespace TMKit

open IntMul

/-- The seven tape symbols used by our machines. -/
inductive Sym
  | blank | start | zero | one | sep | mk | out
  deriving DecidableEq

instance : Fintype Sym where
  elems := {.blank, .start, .zero, .one, .sep, .mk, .out}
  complete := by intro x; cases x <;> simp

/-- A machine with `k` tapes whose transitions are written for the "heads rest on the top of a
stack" convention: `spec` is the raw transition and `guard` enforces the platform rules. -/
def guardSpec {k : ℕ} (a : Fin k → Sym) (spec : Fin k → Sym × Move) : Fin k → Sym × Move :=
  fun i => if a i = Sym.start then (Sym.start, Move.stay)
    else if (i : ℕ) = 0 then (a i, (spec i).2) else (spec i)

/-- The machine determined by a raw transition function `spec`.  State set `Option Q` (`none` halts).
`hwrite` must say that `spec` never writes `▷`. -/
def mkMachine (k : ℕ) (hk : 2 ≤ k) (Q : Type) [Fintype Q] (q0 : Q)
    (spec : Q → (Fin k → Sym) → Q × (Fin k → Sym × Move))
    (hwrite : ∀ q a i, ((spec q a).2 i).1 ≠ Sym.start) : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := Option Q
  qStart := some q0
  qHalt := none
  start_ne_halt := by simp
  k := k
  two_le_k := hk
  δ q a := match q with
    | none => (none, fun i => (a i, Move.stay))
    | some q => ((spec q a).1, guardSpec a (spec q a).2)
  start_preserved := by
    intro q a i hi
    rcases q with _ | q
    · dsimp only; exact ⟨hi, by simp⟩
    · dsimp only
      have hg : guardSpec a (spec q a).2 i = (Sym.start, Move.stay) := by
        simp only [guardSpec, hi, if_true]
      rw [hg]
      exact ⟨rfl, by simp⟩
  start_only_at_start := by
    intro q a i hi
    rcases q with _ | q
    · dsimp only; simpa using hi
    · dsimp only
      have hne : ¬ (a i = Sym.start) := hi
      simp only [guardSpec, if_neg hne]
      by_cases h0 : (i : ℕ) = 0
      · rw [if_pos h0]; simpa using hi
      · rw [if_neg h0]
        exact hwrite q a i
  halt_fixed := by intro a; rfl
  input_readonly := by
    intro q a
    rcases q with _ | q
    · rfl
    · dsimp only
      simp only [guardSpec]
      have hv : ((⟨0, by omega⟩ : Fin k) : ℕ) = 0 := rfl
      by_cases h : a ⟨0, by omega⟩ = Sym.start
      · simp [h]
      · simp [h, hv]


end TMKit


