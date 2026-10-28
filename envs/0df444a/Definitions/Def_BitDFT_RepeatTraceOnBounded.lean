-- Prove2me | Definitions.Def_BitDFT_RepeatTraceOnBounded
-- name    : BitDFT_RepeatTraceOnBounded
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T20:29:07.581978+00:00
-- url     : https://prove2.me/theorems/59c8435e-7664-4961-908e-ee378d05f725
-- title:
--   Bounded body traces for repeated multitape controllers
-- statement:
--   A bounded repeat trace records each execution of a finite controller on a nonblank record, requires every body execution to use at most B transitions, and ends with a final blank check. Its round count includes that final check. Converting a bounded trace to an ordinary repeat trace forgets the cost annotations.
-- source:
--   New reusable runtime interface for repeated per-coordinate processing in the finite-precision DFT output-rescaling machine.

import Definitions.Def_BitDFT_RepeatUntilBlankOn

set_option autoImplicit false

namespace BitDFT.MachineSequence
open IntMul

/-- A repeat trace annotated with a uniform cost bound for each nonblank body run. -/
inductive RepeatTraceOnBounded {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) (B : ℕ) :
    ℕ → P.machine.Cfg → (repeatMachineOn source P).Cfg → Type where
  | stop {c : P.machine.Cfg} (hExit : c.state = P.exit)
      (hBlank : c.cells source (c.head source) = M.blank) :
      RepeatTraceOnBounded source P B 1 c (repeatHaltCfgOn source P c)
  | next {t m : ℕ} {c d : P.machine.Cfg}
      {final : (repeatMachineOn source P).Cfg}
      (hEntry : c.state = P.entry)
      (hRun : P.machine.step^[t] c = d)
      (hFirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
      (hExit : d.state = P.exit)
      (hNonblank : d.cells source (d.head source) ≠ M.blank)
      (hBodyBound : t ≤ B)
      (hTail : RepeatTraceOnBounded source P B m
        (repeatBodyEntryCfgOn source P d) final) :
      RepeatTraceOnBounded source P B (t + 1 + m) c final

def repeatTraceOnBoundedRounds {M : MultitapeTM} {source : Fin M.k}
    {P : Controller M} {B t : ℕ} {c : P.machine.Cfg}
    {final : (repeatMachineOn source P).Cfg} :
    RepeatTraceOnBounded source P B t c final → ℕ
  | .stop _ _ => 1
  | .next _ _ _ _ _ _ tail => repeatTraceOnBoundedRounds tail + 1

theorem RepeatTraceOnBounded.toTrace {M : MultitapeTM} {source : Fin M.k}
    {P : Controller M} {B : ℕ} :
    {t : ℕ} → {c : P.machine.Cfg} → {final : (repeatMachineOn source P).Cfg} →
    RepeatTraceOnBounded source P B t c final → RepeatTraceOn source P t c final
  | _, _, _, .stop hExit hBlank => .stop hExit hBlank
  | _, _, _, .next hEntry hRun hFirst hExit hNonblank _ hTail =>
      .next hEntry hRun hFirst hExit hNonblank hTail.toTrace


end BitDFT.MachineSequence


