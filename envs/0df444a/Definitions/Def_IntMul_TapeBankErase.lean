-- Prove2me | Definitions.Def_IntMul_TapeBankErase
-- name    : IntMul_TapeBankErase
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-10T11:10:55.343154+00:00
-- url     : https://prove2.me/theorems/337c6c1c-c7f6-4332-be37-476a2083b7ba
-- title:
--   Fixed four-state physical selected-work-bank eraser
-- statement:
--   For a fixed number m+2 of tapes and a fixed selected bank index at least one, this four-state machine seeks the selected real start marker, opens the bank, replaces each nonblank payload symbol by blank, turns on the final blank and seeks the marker again before halting. It freezes every other bank, including read-only input 0. Its finite table reads only state and scanned symbols. The caller frame records the selected payload and arbitrary initial head explicitly. Correctness and an exact actual transition clock are separate obligations.
-- source:
--   Original fixed-bank physical erasure machine for reusable streaming carry workspaces. Written by Codex.

import Definitions.Def_IntMul_TapeAdder

namespace IntMul.TapeBankErase
open TapeCopy (Sym)
open TapeAdder (safeStep)

inductive State
  | rewind | sweep | restore | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.rewind,.sweep,.restore,.halt}
  complete := by intro q;cases q <;> simp

def rawTransition (m : ℕ) (bank : Fin (m+2)) (q : State)
    (a : Fin (m+2) → Sym) : State × (Fin (m+2) → Sym × Move) :=
  match q with
  | .halt => (.halt,fun i => (a i,.stay))
  | .rewind =>
      if a bank=.start then
        (.sweep,fun i => (a i,if i=bank then .right else .stay))
      else (.rewind,fun i => (a i,if i=bank then .left else .stay))
  | .sweep =>
      if a bank=.blank then
        (.restore,fun i => (a i,if i=bank then .left else .stay))
      else (.sweep,fun i => (if i=bank then .blank else a i,
        if i=bank then .right else .stay))
  | .restore =>
      if a bank=.start then (.halt,fun i => (a i,.stay))
      else (.restore,fun i => (a i,if i=bank then .left else .stay))

def transition (m : ℕ) (bank : Fin (m+2)) (q : State) (a : Fin (m+2) → Sym) :
    State × (Fin (m+2) → Sym × Move) :=
  let r := rawTransition m bank q a
  (r.1,fun i => safeStep (a i) (r.2 i).1 (r.2 i).2)

private theorem raw_input (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (q : State) (a : Fin (m+2) → Sym) :
    ((rawTransition m bank q a).2 0).1=a 0 := by
  have hzero : (0 : Fin (m+2))≠bank := by
    intro h
    have hv : bank.val=0 := by simpa using (congrArg Fin.val h).symm
    omega
  cases q <;> simp only [rawTransition]
  all_goals try split_ifs
  all_goals simp_all

abbrev machine (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val) : MultitapeTM where
  Sym := Sym
  blank := .blank
  startSym := .start
  zero := .zero
  one := .one
  sep := .sep
  syms_distinct := by decide
  K := State
  qStart := .rewind
  qHalt := .halt
  start_ne_halt := by decide
  k := m+2
  two_le_k := by omega
  δ := transition m bank
  start_preserved := by
    intro q a i hi
    change (safeStep (a i) _ _).1=.start ∧ (safeStep (a i) _ _).2≠Move.left
    simp only [safeStep,hi,if_true]
    split <;> simp_all
  start_only_at_start := by
    intro q a i hi
    change (safeStep (a i) _ _).1≠.start
    simp only [safeStep,if_neg hi]
    split <;> simp_all
  halt_fixed := by intro a;simp [transition,rawTransition,TapeAdder.safe_stay]
  input_readonly := by
    intro q a
    change (safeStep (a 0) ((rawTransition m bank q a).2 0).1 _).1=a 0
    rw [raw_input m bank hb]
    by_cases h : a 0=Sym.start <;> simp [safeStep,h]

/-- The bank payload has no interior boundary or blank; in particular bits
and separators are allowed. The table itself does not inspect this predicate. -/
def ValidWord (w : List Sym) : Prop := ∀ s ∈ w, s≠Sym.start ∧ s≠Sym.blank

/-- Prepared selected bank, preserving every other physical caller bank and
head. The selected head may start at any h, including beyond the payload. -/
def initialFrame (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) (w : List Sym) (h : ℕ) : (machine m bank hb).Cfg where
  state := .rewind
  cells := Function.update base.cells bank ((machine m bank hb).tapeOf w)
  head := Function.update base.head bank h

/-- Exact erased marked bank and returned head, with all caller banks retained. -/
def finalFrame (m : ℕ) (bank : Fin (m+2)) (hb : 1 ≤ bank.val)
    (base : (machine m bank hb).Cfg) : (machine m bank hb).Cfg where
  state := .halt
  cells := Function.update base.cells bank ((machine m bank hb).tapeOf [])
  head := Function.update base.head bank 0

end IntMul.TapeBankErase


