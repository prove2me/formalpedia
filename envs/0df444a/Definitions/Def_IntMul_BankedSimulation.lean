-- Prove2me | Definitions.Def_IntMul_BankedSimulation
-- name    : IntMul_BankedSimulation
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T20:39:54.682418+00:00
-- url     : https://prove2.me/theorems/1616497b-3420-499c-9520-bf1f22523d6a
-- title:
--   Literal one-step-per-step multitape simulation inside work-tape banks
-- statement:
--   For any finite deterministic multitape machine M, defines a finite simulator with M.k+2 physical tapes and a tagged finite alphabet. Two global input/output tapes are frozen. The other tapes simulate M using tagged symbols, including a tagged local start marker distinct from the outer global marker. An embedding describes arbitrary positive-offset prepared banks, retaining every prefix cell and placing heads at offset plus the child head. The transition table sees only finite state and scanned symbols; offsets are proof-side configuration data, never table arguments. Preparing banks and seeking or returning heads are separate charged obligations.
-- source:
--   Original literal compiler foundation for the integer-multiplication campaign's clocked recursive multiplier and fixed-tape routing. Written by Codex.

import Definitions.Def_IntMul_MultitapeModel

/-!
# Literal simulation in interior work-tape banks

The alphabet tags the simulated machine's symbols, including its local start
marker. The simulator's global start marker is a different symbol (`none`).
Two global input/output tapes remain frozen; the other tapes run the simulated
machine. Offsets are configuration data in the proof, never transition inputs.
-/

namespace IntMul.BankedSimulation

def workTape (M : MultitapeTM) (i : Fin M.k) : Fin (M.k + 2) :=
  ⟨i.val + 2,by omega⟩

def innerTape (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) : Fin M.k :=
  ⟨i.val - 2,by omega⟩

def decode (M : MultitapeTM) : Option M.Sym → M.Sym
  | none => M.startSym
  | some s => s

/-- At a global marker, preserve it and suppress a left move. A tagged local
marker remains an ordinary legal symbol of the outer machine's alphabet. -/
def protect (M : MultitapeTM) (old : Option M.Sym) (write : M.Sym) (move : Move) :
    Option M.Sym × Move :=
  match old with
  | none => (none,match move with | .left => .stay | other => other)
  | some _ => (some write,move)

def transition (M : MultitapeTM) (q : M.K) (a : Fin (M.k + 2) → Option M.Sym) :
    M.K × (Fin (M.k + 2) → Option M.Sym × Move) :=
  let r := M.δ q (fun i => decode M (a (workTape M i)))
  (r.1,fun i => if h : 2 ≤ i.val then
    protect M (a i) (r.2 (innerTape M i h)).1 (r.2 (innerTape M i h)).2
    else (a i,.stay))

/-- A fixed finite simulator with M.k+2 tapes and the tagged finite alphabet.
Its literal table has no access to offsets, positions, lengths, or tape tails. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Option M.Sym
  blank := some M.blank
  startSym := none
  zero := some M.zero
  one := some M.one
  sep := some M.sep
  syms_distinct := by
    classical
    have hd := M.syms_distinct
    simp only [List.nodup_cons,List.mem_cons,List.mem_singleton,not_or] at hd
    simp_all
  K := M.K
  qStart := M.qStart
  qHalt := M.qHalt
  start_ne_halt := M.start_ne_halt
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    intro q a i hi
    simp only [transition]
    split
    · rw [hi]
      simp only [protect]
      split <;> simp_all
    · simp [hi]
  start_only_at_start := by
    intro q a i hi
    simp only [transition]
    split
    · cases hs : a i with
      | none => exact False.elim (hi hs)
      | some s => simp [protect]
    · exact hi
  halt_fixed := by
    intro a
    simp only [transition,M.halt_fixed]
    congr 1
    funext i
    split
    · have hw : workTape M (innerTape M i (by assumption)) = i := by
        apply Fin.ext
        simp only [workTape,innerTape]
        omega
      simp only [hw]
      cases hs : a i <;> simp [decode,protect,hs]
    · rfl
  input_readonly := by
    intro q a
    simp [transition,MultitapeTM.inTape]

/-- Prepared banks retain every cell before their offset. Each offset is
positive, so the global cell-zero marker is outside the simulated bank.
Constructing these banks and moving heads into them is a separate charged task. -/
def embed (M : MultitapeTM) (base : (machine M).Cfg)
    (offset : Fin M.k → ℕ) (c : M.Cfg) : (machine M).Cfg where
  state := c.state
  cells := fun i p => if h : 2 ≤ i.val then
    let j := innerTape M i h
    if p < offset j then base.cells i p else some (c.cells j (p - offset j))
    else base.cells i p
  head := fun i => if h : 2 ≤ i.val then
    let j := innerTape M i h
    offset j + c.head j
    else base.head i

end IntMul.BankedSimulation


