-- Prove2me | Definitions.Def_BitDFT_RepeatUntilBlank
-- name    : BitDFT_RepeatUntilBlank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T03:14:23.870607+00:00
-- url     : https://prove2.me/theorems/cc01ff78-8f0d-4fd9-8e68-efa61d94c946
-- title:
--   A reusable finite-controller loop over a read-only stream
-- statement:
--   Let $P$ be a finite multitape controller with a read-only source tape. The wrapper re-enters $P$ whenever the source symbol at the body exit is nonblank, and halts when that symbol is blank. A finite trace records each body run, its first arrival at the exit state, and the blank test after the final run. The resulting machine executes exactly the sum of all body-run lengths plus one control transition per processed record. This gives a machine-level interface for repeating a scalar transformation across a self-delimiting stream.
-- source:
--   Reusable finite-state construction for the output stream in BitDFT.rescale_output_machine; based on the project machine model in Definitions.Def_IntMul_MultitapeModel and controller sequencing in Definitions.Def_BitDFT_MachineSequence.

import Definitions.Def_BitDFT_MachineSequence

set_option autoImplicit false

namespace BitDFT.MachineSequence
open IntMul

/-- Re-run a finite controller whenever its read-only source has not reached
blank. The body must advance the source head before reaching its exit state. -/
noncomputable def repeatUntilBlank {M : MultitapeTM} (P : Controller M) :
    Controller M := by
  classical
  exact {
    K := P.K ⊕ Unit
    entry := Sum.inl P.entry
    exit := Sum.inr ()
    distinct := by simp
    transition := fun q a => match q with
      | .inl p =>
        if hp : p = P.exit then
          if a M.inTape = M.blank then
            (.inr (), fun i => (a i, .stay))
          else
            (.inl P.entry, fun i => (a i, .stay))
        else
          let r := P.transition p a
          (.inl r.1, r.2)
      | .inr _ => (.inr (), fun i => (a i, .stay))
    marker := by
      intro q a i hi
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · by_cases hb : a M.inTape = M.blank <;> simp [hp, hb, hi]
        · simpa [hp] using P.marker p a i hi
      | inr u => simp [hi]
    noMarker := by
      intro q a i hi
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · by_cases hb : a M.inTape = M.blank <;> simp [hp, hb, hi]
        · simpa [hp] using P.noMarker p a i hi
      | inr u => simpa using hi
    frozen := by intro a; simp
    readonly := by
      intro q a
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · by_cases hb : a M.inTape = M.blank <;> simp [hp, hb]
        · simpa [hp] using P.readonly p a
      | inr u => rfl }

noncomputable abbrev repeatMachine {M : MultitapeTM} (P : Controller M) :=
  (repeatUntilBlank P).machine

def repeatBodyCfg {M : MultitapeTM} {P : Controller M}
    (c : P.machine.Cfg) : (repeatMachine P).Cfg :=
  ⟨Sum.inl c.state, c.cells, c.head⟩

def repeatBodyEntryCfg {M : MultitapeTM} (P : Controller M)
    (c : P.machine.Cfg) : P.machine.Cfg := ⟨P.entry, c.cells, c.head⟩

def repeatHaltCfg {M : MultitapeTM} (P : Controller M)
    (c : P.machine.Cfg) : (repeatMachine P).Cfg :=
  ⟨Sum.inr (), c.cells, c.head⟩

/-- A finite certificate for a run of the repeat controller. Each `next`
chunk is one body execution that advances the read-only source past a record;
the final `stop` chunk sees blank at the next record boundary. -/
inductive RepeatTrace {M : MultitapeTM} (P : Controller M) :
    ℕ → P.machine.Cfg → (repeatMachine P).Cfg → Prop where
  | stop {c : P.machine.Cfg} (hExit : c.state = P.exit)
      (hBlank : c.cells M.inTape (c.head M.inTape) = M.blank) :
      RepeatTrace P 1 c (repeatHaltCfg P c)
  | next {t m : ℕ} {c d : P.machine.Cfg} {final : (repeatMachine P).Cfg}
      (hEntry : c.state = P.entry)
      (hRun : P.machine.step^[t] c = d)
      (hFirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
      (hExit : d.state = P.exit)
      (hNonblank : d.cells M.inTape (d.head M.inTape) ≠ M.blank)
      (hTail : RepeatTrace P m (repeatBodyEntryCfg P d) final) :
      RepeatTrace P (t + 1 + m) c final

theorem repeatBody_step {M : MultitapeTM} (P : Controller M)
    (c : P.machine.Cfg) (hstate : c.state ≠ P.exit) :
    (repeatMachine P).step (repeatBodyCfg c) =
      repeatBodyCfg (P.machine.step c) := by
  cases c
  simp [repeatMachine, repeatUntilBlank, Controller.machine, MultitapeTM.step,
    repeatBodyCfg, hstate]

theorem repeatBody_exit_step {M : MultitapeTM} (P : Controller M)
    [DecidableEq M.Sym]
    (c : P.machine.Cfg) (hstate : c.state = P.exit) :
    (repeatMachine P).step (repeatBodyCfg c) =
      if c.cells M.inTape (c.head M.inTape) = M.blank then
        (⟨(Sum.inr () : (repeatUntilBlank P).K), c.cells, c.head⟩ : (repeatMachine P).Cfg)
      else (⟨(Sum.inl P.entry : (repeatUntilBlank P).K), c.cells, c.head⟩ : (repeatMachine P).Cfg) := by
  cases c with
  | mk state cells head =>
    change state = P.exit at hstate
    subst state
    by_cases hb : cells M.inTape (head M.inTape) = M.blank
    all_goals simp [repeatMachine, repeatUntilBlank, Controller.machine,
      MultitapeTM.step, repeatBodyCfg, hb]

end BitDFT.MachineSequence


