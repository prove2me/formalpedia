-- Prove2me | Definitions.Def_IntMul_BankedCall
-- name    : IntMul_BankedCall
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-09T20:53:41.869125+00:00
-- url     : https://prove2.me/theorems/1010757e-a1f3-463e-bb54-a5a6dd77df66
-- title:
--   Literal banked caller with physical initialization, child execution, and output return
-- statement:
--   For a finite multitape child machine M, defines a fixed caller with M.k+2 tapes, tagged alphabet Option M.Sym, and a finite state sum of seven phases and M.K. Its table creates local bank markers, copies the global input x#y into the child input bank, rewinds that child input head, executes the child's literal table in banks, rewinds the child output head, copies the output to the global output tape, and globally halts. Full correctness and time bounds are separate proof obligations. All transitions use only finite control state and the scanned symbol tuple. The initialization, running, output-return, and final frames are proof-side descriptions, never transition inputs.
-- source:
--   Original literal compiler foundation for the integer-multiplication campaign's clocked recursive multiplier and fixed-tape routing. Written by Codex.

import Definitions.Def_IntMul_BankedSimulation

namespace IntMul.BankedCall

inductive Phase
  | start | mark | copyInput | rewindInput | rewindOutput | copyOutput | halt
  deriving DecidableEq

instance : Fintype Phase where
  elems := {.start,.mark,.copyInput,.rewindInput,.rewindOutput,.copyOutput,.halt}
  complete := by intro q; cases q <;> simp

abbrev State (M : MultitapeTM) := Sum Phase M.K

noncomputable def rawTransition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Option M.Sym) : State M × (Fin (M.k + 2) → Option M.Sym × Move) := by
  classical
  exact match q with
  | .inr q =>
      if q = M.qHalt then (.inl .rewindOutput,fun i => (a i,.stay))
      else let r := BankedSimulation.transition M q a
        (.inr r.1,r.2)
  | .inl .start => (.inl .mark,fun i => (a i,.right))
  | .inl .mark => (.inl .copyInput,fun i =>
      (if 2 ≤ i.val then some M.startSym else a i,if i.val = 2 then .right else .stay))
  | .inl .copyInput =>
      if a ⟨0,by omega⟩ = some M.zero ∨ a ⟨0,by omega⟩ = some M.one ∨ a ⟨0,by omega⟩ = some M.sep then
        (.inl .copyInput,fun i =>
          (if i.val = 2 then a ⟨0,by omega⟩ else a i,if i.val = 0 ∨ i.val = 2 then .right else .stay))
      else (.inl .rewindInput,fun i => (a i,if i.val = 2 then .left else .stay))
  | .inl .rewindInput =>
      if a ⟨2,by have := M.two_le_k; omega⟩ = some M.startSym then
        (.inr M.qStart,fun i => (a i,.stay))
      else (.inl .rewindInput,fun i => (a i,if i.val = 2 then .left else .stay))
  | .inl .rewindOutput =>
      if a ⟨3,by have := M.two_le_k; omega⟩ = some M.startSym then
        (.inl .copyOutput,fun i => (a i,if i.val = 3 then .right else .stay))
      else (.inl .rewindOutput,fun i => (a i,if i.val = 3 then .left else .stay))
  | .inl .copyOutput =>
      if a ⟨3,by have := M.two_le_k; omega⟩ = some M.zero ∨
          a ⟨3,by have := M.two_le_k; omega⟩ = some M.one then
        (.inl .copyOutput,fun i =>
          (if i.val = 1 then a ⟨3,by have := M.two_le_k; omega⟩ else a i,
            if i.val = 1 ∨ i.val = 3 then .right else .stay))
      else (.inl .halt,fun i => (a i,.stay))
  | .inl .halt => (.inl .halt,fun i => (a i,.stay))

noncomputable def transition (M : MultitapeTM) (q : State M)
    (a : Fin (M.k + 2) → Option M.Sym) : State M × (Fin (M.k + 2) → Option M.Sym × Move) :=
  match q with
  | .inr _ => rawTransition M q a
  | .inl _ =>
      let r := rawTransition M q a
      (r.1,fun i => BankedSimulation.protect M (a i) (BankedSimulation.decode M (r.2 i).1) (r.2 i).2)

private theorem protect_self_stay (M : MultitapeTM) (a : Option M.Sym) :
    BankedSimulation.protect M a (BankedSimulation.decode M a) .stay = (a,.stay) := by
  cases a <;> rfl

private theorem protect_self_write (M : MultitapeTM) (a : Option M.Sym) (d : Move) :
    (BankedSimulation.protect M a (BankedSimulation.decode M a) d).1 = a := by
  cases a <;> rfl

private theorem raw_input_readonly (M : MultitapeTM) (q : Phase)
    (a : Fin (M.k + 2) → Option M.Sym) :
    ((rawTransition M (.inl q) a).2 ⟨0,by omega⟩).1 = a ⟨0,by omega⟩ := by
  classical
  cases q <;> simp [rawTransition]
  all_goals repeat' first | rfl | split

/-- The complete banked subroutine caller has explicit setup, child execution,
and output-return phases. It never reads a head position or an input length. -/
noncomputable abbrev machine (M : MultitapeTM) : MultitapeTM where
  Sym := Option M.Sym
  blank := some M.blank
  startSym := none
  zero := some M.zero
  one := some M.one
  sep := some M.sep
  syms_distinct := (BankedSimulation.machine M).syms_distinct
  K := State M
  qStart := .inl .start
  qHalt := .inl .halt
  start_ne_halt := by simp
  k := M.k + 2
  two_le_k := by omega
  δ := transition M
  start_preserved := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        simp only [transition]
        rw [hi]
        simp only [BankedSimulation.protect]
        split <;> simp_all
    | inr q =>
        by_cases hq : q = M.qHalt
        · simp [transition,rawTransition,hq,hi]
        · simpa [transition,rawTransition,hq] using
            (BankedSimulation.machine M).start_preserved q a i hi
  start_only_at_start := by
    classical
    intro q a i hi
    cases q with
    | inl q =>
        simp only [transition]
        cases hs : a i with
        | none => exact False.elim (hi hs)
        | some s => simp [BankedSimulation.protect]
    | inr q =>
        by_cases hq : q = M.qHalt
        · simpa [transition,rawTransition,hq] using hi
        · simpa [transition,rawTransition,hq] using
            (BankedSimulation.machine M).start_only_at_start q a i hi
  halt_fixed := by
    classical
    intro a
    simp [transition,rawTransition,protect_self_stay]
  input_readonly := by
    classical
    intro q a
    cases q with
    | inl q =>
        change (BankedSimulation.protect M (a ⟨0,by omega⟩)
          (BankedSimulation.decode M ((rawTransition M (.inl q) a).2 ⟨0,by omega⟩).1) _).1 = _
        rw [raw_input_readonly]
        exact protect_self_write _ _ _
    | inr q =>
        by_cases hq : q = M.qHalt
        · simp [transition,rawTransition,hq]
        · simpa [transition,rawTransition,hq] using
            (BankedSimulation.machine M).input_readonly q a

def inputWord (M : MultitapeTM) (x y : List Bool) : List M.Sym :=
  x.map M.bitSym ++ M.sep :: y.map M.bitSym

/-- An interior bank beginning at cell one. Cell zero retains the global
marker; cell one holds the tagged child marker and its payload starts at two. -/
def bankTape (M : MultitapeTM) (w : List M.Sym) (p : ℕ) : Option M.Sym :=
  if p = 0 then none else some (M.tapeOf w (p - 1))

/-- The child has its complete initial configuration in banks at offset one;
the global source head is at its end blank and the global output is still empty. -/
noncomputable def readyFrame (M : MultitapeTM) (x y : List Bool) : (machine M).Cfg where
  state := .inr M.qStart
  cells := fun i =>
    if i.val = 0 then (machine M).tapeOf ((inputWord M x y).map some)
    else if i.val = 1 then (machine M).tapeOf []
    else if i.val = 2 then bankTape M (inputWord M x y)
    else bankTape M []
  head := fun i => if i.val = 0 then x.length + y.length + 2 else 1

/-- Saved global input/output and work-prefix data for a prepared child call. -/
noncomputable def bankBase (M : MultitapeTM) (x y : List Bool) :
    (BankedSimulation.machine M).Cfg where
  state := M.qStart
  cells := (readyFrame M x y).cells
  head := (readyFrame M x y).head

/-- The child configuration occupies offset-one banks during execution. -/
noncomputable def runningFrame (M : MultitapeTM) (x y : List Bool) (c : M.Cfg) : (machine M).Cfg where
  state := .inr c.state
  cells := (BankedSimulation.embed M (bankBase M x y) (fun _ => 1) c).cells
  head := (BankedSimulation.embed M (bankBase M x y) (fun _ => 1) c).head

/-- Return the child's output head physically toward its local start marker. -/
noncomputable def returnOutputFrame (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (pos : ℕ) : (machine M).Cfg where
  state := .inl .rewindOutput
  cells := (runningFrame M x y c).cells
  head := fun i => if i.val = 3 then pos else (runningFrame M x y c).head i

/-- A physical output-copy boundary: j output bits have been written, and the
child's output head is at its next bank payload cell. -/
noncomputable def copyOutputFrame (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) (j : ℕ) : (machine M).Cfg where
  state := .inl .copyOutput
  cells := fun i => if i.val = 1 then (machine M).tapeOf ((w.take j).map (machine M).bitSym)
    else (runningFrame M x y c).cells i
  head := fun i => if i.val = 1 then j + 1 else if i.val = 3 then j + 2
    else (runningFrame M x y c).head i

/-- Complete returned configuration after the copied output's terminating
blank has been observed and the global machine has halted. -/
noncomputable def finalFrame (M : MultitapeTM) (x y : List Bool) (c : M.Cfg)
    (w : List Bool) : (machine M).Cfg where
  state := .inl .halt
  cells := (copyOutputFrame M x y c w w.length).cells
  head := (copyOutputFrame M x y c w w.length).head

end IntMul.BankedCall


