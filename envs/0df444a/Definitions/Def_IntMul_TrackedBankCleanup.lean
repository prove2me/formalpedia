-- Prove2me | Definitions.Def_IntMul_TrackedBankCleanup
-- name    : IntMul_TrackedBankCleanup
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T22:11:09.354965+00:00
-- url     : https://prove2.me/theorems/a6c078e2-d5ad-427d-b078-7abee7c93971
-- title:
--   Physical parallel rewind, visited-workspace clearing and fresh-bank restoration
-- statement:
--   For each finite child machine M, one fixed M.k+2-tape four-state machine over Option(M.Sym×Bool) clears prepared tracked child banks. All work heads first rewind independently to tagged local start symbols, then move onto payloads. The machine physically erases each visited payload cell, stopping each bank separately at its first fresh flag. Once all sweeps finish, heads return independently to retained local markers. A final physical transition erases those markers and halts, leaving fresh blank suffixes at the same offsets. Root input and caller buffer are frozen; global markers are protected. Offsets, workspace extents, initial head distances and saved prefixes occur only in proof-side frames and are absent from the finite transition table. Unique-marker and blank-tail invariants are explicit proof preconditions. Output must already have been copied before clearing its bank.
-- source:
--   Original finite visited-workspace clearing construction for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedBankedSimulation

namespace IntMul.TrackedBankCleanup

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

inductive State
  | rewind | sweep | restore | halt
  deriving DecidableEq

instance : Fintype State where
  elems := {.rewind,.sweep,.restore,.halt}
  complete := by intro q; cases q <;> simp

def visited (M : MultitapeTM) : Sym M → Bool
  | none => false
  | some s => s.2

/-- A finite-symbol guard for the outer global marker. Local child markers
and visited flags remain ordinary writable symbols of the outer alphabet. -/
def protect (M : MultitapeTM) (old write : Sym M) (move : Move) : Sym M × Move :=
  match old with
  | none => (none,match move with | .left => .stay | other => other)
  | some s => (match write with | none => some s | some t => some t,move)

noncomputable def rawTransition (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    State × (Fin (M.k + 2) → Sym M × Move) := by
  classical
  exact match q with
  | .halt => (.halt,fun i => (a i,.stay))
  | .rewind =>
      if ∀ j : Fin M.k, a (workTape M j) = some (M.startSym,true) then
        (.sweep,fun i => (a i,if 2 ≤ i.val then .right else .stay))
      else (.rewind,fun i =>
        (a i,if 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) then .left else .stay))
  | .sweep =>
      if ∀ j : Fin M.k, visited M (a (workTape M j)) = false then
        (.restore,fun i => (a i,if 2 ≤ i.val then .left else .stay))
      else (.sweep,fun i =>
        (if 2 ≤ i.val ∧ visited M (a i) = true then some (M.blank,false) else a i,
          if 2 ≤ i.val ∧ visited M (a i) = true then .right else .stay))
  | .restore =>
      if ∀ j : Fin M.k, a (workTape M j) = some (M.startSym,true) then
        (.halt,fun i => (if 2 ≤ i.val then some (M.blank,false) else a i,.stay))
      else (.restore,fun i =>
        (a i,if 2 ≤ i.val ∧ a i ≠ some (M.startSym,true) then .left else .stay))

noncomputable def transition (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    State × (Fin (M.k + 2) → Sym M × Move) :=
  let r := rawTransition M q a
  (r.1,fun i => protect M (a i) (r.2 i).1 (r.2 i).2)

private theorem protect_self_stay (M : MultitapeTM) (a : Sym M) : protect M a a .stay = (a,.stay) := by
  cases a <;> rfl

private theorem protect_self_write (M : MultitapeTM) (a : Sym M) (d : Move) : (protect M a a d).1 = a := by
  cases a <;> rfl

private theorem raw_input_readonly (M : MultitapeTM) (q : State) (a : Fin (M.k + 2) → Sym M) :
    ((rawTransition M q a).2 ⟨0,by omega⟩).1 = a ⟨0,by omega⟩ := by
  classical
  cases q <;> simp only [rawTransition] <;> split_ifs <;> first | rfl | omega

/-- Physical clearing on the same fixed bank tapes and finite tracked
alphabet, preserving caller input/output and every earlier work-bank prefix. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Sym M
  blank := some (M.blank,false)
  startSym := none
  zero := some (M.zero,true)
  one := some (M.one,true)
  sep := some (M.sep,true)
  syms_distinct := (TrackedBankedSimulation.machine M).syms_distinct
  K := State
  qStart := .rewind
  qHalt := .halt
  start_ne_halt := by decide
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    change (protect M (a i) _ _).1 = none ∧ (protect M (a i) _ _).2 ≠ .left
    rw [hi]
    simp only [protect]
    split <;> simp_all
  start_only_at_start := by
    classical
    intro q a i hi
    change (protect M (a i) _ _).1 ≠ none
    cases hs : a i with
    | none => exact False.elim (hi hs)
    | some s => simp only [protect]; split <;> simp
  halt_fixed := by
    intro a
    simp [transition,rawTransition,protect_self_stay]
  input_readonly := by
    intro q a
    change (protect M (a ⟨0,by omega⟩) ((rawTransition M q a).2 ⟨0,by omega⟩).1 _).1 = _
    rw [raw_input_readonly]
    exact protect_self_write _ _ _

/-- Proof-only maximum of the finitely many physical bank-head distances. -/
def span (M : MultitapeTM) (f : Fin M.k → ℕ) : ℕ := Finset.univ.sup f

noncomputable def parentBase (M : MultitapeTM) (base : (machine M).Cfg) : (TrackedBankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := base.cells
  head := base.head

noncomputable def rewindFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (pos : Fin M.k → ℕ) : (machine M).Cfg where
  state := .rewind
  cells := (TrackedBankedSimulation.embed M (parentBase M base) offset extent c).cells
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) + pos (innerTape M i h) else base.head i

/-- Erase the visited payload prefix, retaining the local boundary until
all sweep heads have returned. The current sweep stops on the first fresh flag. -/
def sweepCells (M : MultitapeTM) (base : (machine M).Cfg) (offset extent cleared : Fin M.k → ℕ)
    (c : M.Cfg) (i : Fin (M.k + 2)) (p : ℕ) : Sym M :=
  if h : 2 ≤ i.val then
    let j := innerTape M i h
    if p < offset j then base.cells i p else
      let v := p - offset j
      if v = 0 then some (M.startSym,true)
      else if v ≤ cleared j then some (M.blank,false)
      else some (c.cells j v,decide (v ≤ extent j))
  else base.cells i p

noncomputable def sweepFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset extent cleared : Fin M.k → ℕ) (c : M.Cfg) : (machine M).Cfg where
  state := .sweep
  cells := sweepCells M base offset extent cleared c
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) + cleared (innerTape M i h) + 1 else base.head i

def markerTape (M : MultitapeTM) (base : ℕ → Sym M) (offset p : ℕ) : Sym M :=
  if p < offset then base p else if p = offset then some (M.startSym,true) else some (M.blank,false)

def freshTape (M : MultitapeTM) (base : ℕ → Sym M) (offset p : ℕ) : Sym M :=
  if p < offset then base p else some (M.blank,false)

noncomputable def restoreFrame (M : MultitapeTM) (base : (machine M).Cfg)
    (offset pos : Fin M.k → ℕ) : (machine M).Cfg where
  state := .restore
  cells := fun i => if h : 2 ≤ i.val then markerTape M (base.cells i) (offset (innerTape M i h)) else base.cells i
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) + pos (innerTape M i h) else base.head i

noncomputable def finalFrame (M : MultitapeTM) (base : (machine M).Cfg) (offset : Fin M.k → ℕ) : (machine M).Cfg where
  state := .halt
  cells := fun i => if h : 2 ≤ i.val then freshTape M (base.cells i) (offset (innerTape M i h)) else base.cells i
  head := fun i => if h : 2 ≤ i.val then offset (innerTape M i h) else base.head i

end IntMul.TrackedBankCleanup


