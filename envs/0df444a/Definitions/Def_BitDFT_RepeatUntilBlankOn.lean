-- Prove2me | Definitions.Def_BitDFT_RepeatUntilBlankOn
-- name    : BitDFT_RepeatUntilBlankOn
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T03:25:44.28665+00:00
-- url     : https://prove2.me/theorems/efcb8db9-9ad0-4dd0-b6a1-ef3d607a72eb
-- title:
--   Repeat a controller until a designated tape reaches blank
-- statement:
--   Given a finite-state controller and a designated tape, this construction reruns the controller after each completed record until the designated tape head sees blank. The designated tape may be a writable output or work tape, so the construction supports postprocessing output streams. The associated trace theorem gives an exact run length: each body execution plus one loop-control step, including the final blank test.
-- source:
--   Reusable controller construction for the integer-multiplication to finite-precision Fourier transfer formalization.

import Definitions.Def_BitDFT_MachineSequence

set_option autoImplicit false

namespace BitDFT.MachineSequence
open IntMul

/-- Re-run a finite controller whenever the designated source tape has not
reached blank. Unlike the machine input tape, this source may be writable by
the body controller. The body must advance its head before reaching exit. -/
noncomputable def repeatUntilBlankOn {M : MultitapeTM} (source : Fin M.k) (P : Controller M) :
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
          if a source = M.blank then
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
        · by_cases hb : a source = M.blank <;> simp [hp, hb, hi]
        · simpa [hp] using P.marker p a i hi
      | inr u => simp [hi]
    noMarker := by
      intro q a i hi
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · by_cases hb : a source = M.blank <;> simp [hp, hb, hi]
        · simpa [hp] using P.noMarker p a i hi
      | inr u => simpa using hi
    frozen := by intro a; simp
    readonly := by
      intro q a
      cases q with
      | inl p =>
        by_cases hp : p = P.exit
        · by_cases hb : a source = M.blank <;> simp [hp, hb]
        · simpa [hp] using P.readonly p a
      | inr u => rfl }

noncomputable abbrev repeatMachineOn {M : MultitapeTM} (source : Fin M.k) (P : Controller M) :=
  (repeatUntilBlankOn source P).machine

def repeatBodyCfgOn {M : MultitapeTM} (source : Fin M.k) {P : Controller M}
    (c : P.machine.Cfg) : (repeatMachineOn source P).Cfg :=
  ⟨Sum.inl c.state, c.cells, c.head⟩

def repeatBodyEntryCfgOn {M : MultitapeTM} (source : Fin M.k) (P : Controller M)
    (c : P.machine.Cfg) : P.machine.Cfg := ⟨P.entry, c.cells, c.head⟩

def repeatHaltCfgOn {M : MultitapeTM} (source : Fin M.k) (P : Controller M)
    (c : P.machine.Cfg) : (repeatMachineOn source P).Cfg :=
  ⟨Sum.inr (), c.cells, c.head⟩

/-- A finite certificate for a run of the repeat controller. Each `next`
chunk is one body execution that advances the designated source past a record;
the final `stop` chunk sees blank at the next record boundary. -/
inductive RepeatTraceOn {M : MultitapeTM} (source : Fin M.k) (P : Controller M) :
    ℕ → P.machine.Cfg → (repeatMachineOn source P).Cfg → Prop where
  | stop {c : P.machine.Cfg} (hExit : c.state = P.exit)
      (hBlank : c.cells source (c.head source) = M.blank) :
      RepeatTraceOn source P 1 c (repeatHaltCfgOn source P c)
  | next {t m : ℕ} {c d : P.machine.Cfg} {final : (repeatMachineOn source P).Cfg}
      (hEntry : c.state = P.entry)
      (hRun : P.machine.step^[t] c = d)
      (hFirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
      (hExit : d.state = P.exit)
      (hNonblank : d.cells source (d.head source) ≠ M.blank)
      (hTail : RepeatTraceOn source P m (repeatBodyEntryCfgOn source P d) final) :
      RepeatTraceOn source P (t + 1 + m) c final

theorem repeatBodyOn_step {M : MultitapeTM} (source : Fin M.k) (P : Controller M)
    (c : P.machine.Cfg) (hstate : c.state ≠ P.exit) :
    (repeatMachineOn source P).step (repeatBodyCfgOn source c) =
      repeatBodyCfgOn source (P.machine.step c) := by
  cases c
  simp [repeatMachineOn, repeatUntilBlankOn, Controller.machine, MultitapeTM.step,
    repeatBodyCfgOn, hstate]

theorem repeatBodyOn_exit_step {M : IntMul.MultitapeTM} (P : Controller M)
    [DecidableEq M.Sym]
    (source : Fin M.k) (c : P.machine.Cfg) (hstate : c.state = P.exit) :
    (repeatMachineOn source P).step (repeatBodyCfgOn source c) =
      if c.cells source (c.head source) = M.blank then
        (⟨(Sum.inr () : (repeatUntilBlankOn source P).K), c.cells, c.head⟩ : (repeatMachineOn source P).Cfg)
      else (⟨(Sum.inl P.entry : (repeatUntilBlankOn source P).K), c.cells, c.head⟩ : (repeatMachineOn source P).Cfg) := by
  cases c with
  | mk state cells head =>
    change state = P.exit at hstate
    subst state
    by_cases hb : cells source (head source) = M.blank
    all_goals simp [repeatMachineOn, repeatUntilBlankOn, Controller.machine,
      MultitapeTM.step, repeatBodyCfgOn, hb]

end BitDFT.MachineSequence


