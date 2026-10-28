-- Prove2me | Definitions.Def_BitDFT_RepeatTraceOnBoundedV2
-- name    : BitDFT_RepeatTraceOnBoundedV2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T22:59:13.255518+00:00
-- url     : https://prove2.me/theorems/343d8395-2e89-4018-97ff-66dbff1fc367
-- title:
--   Complete bounded trace for a repeated controller
-- statement:
--   A bounded trace for a controller repeated over a stream records every body execution and its loop test. The final record is handled explicitly: the last body run advances the source to a blank sentinel, and the next loop-control step halts. Earlier runs must leave the source nonblank and restart the body. This supports exact runtime proofs for complete stream-processing passes.
-- source:
--   Corrected trace interface for proving complete repeated-machine runs; includes the final body execution at the blank sentinel.

import Definitions.Def_BitDFT_RepeatUntilBlankOn

set_option autoImplicit false

namespace BitDFT.MachineSequence
open IntMul

/-- A complete bounded run of `repeatMachineOn`. Unlike the first trace
format, `last` records the final body execution that advances the source onto
the blank sentinel, followed by the loop's terminating test. -/
inductive RepeatTraceOnBoundedV2 {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) (B : ℕ) :
    ℕ → P.machine.Cfg → (repeatMachineOn source P).Cfg → Type where
  | last {t : ℕ} {c d : P.machine.Cfg}
      (hEntry : c.state = P.entry)
      (hRun : P.machine.step^[t] c = d)
      (hFirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
      (hExit : d.state = P.exit)
      (hBlank : d.cells source (d.head source) = M.blank)
      (hBodyBound : t ≤ B) :
      RepeatTraceOnBoundedV2 source P B (t + 1) c (repeatHaltCfgOn source P d)
  | next {t m : ℕ} {c d : P.machine.Cfg}
      {final : (repeatMachineOn source P).Cfg}
      (hEntry : c.state = P.entry)
      (hRun : P.machine.step^[t] c = d)
      (hFirst : ∀ s < t, (P.machine.step^[s] c).state ≠ P.exit)
      (hExit : d.state = P.exit)
      (hNonblank : d.cells source (d.head source) ≠ M.blank)
      (hBodyBound : t ≤ B)
      (hTail : RepeatTraceOnBoundedV2 source P B m
        (repeatBodyEntryCfgOn source P d) final) :
      RepeatTraceOnBoundedV2 source P B (t + 1 + m) c final

def repeatTraceOnBoundedV2Rounds {M : MultitapeTM} {source : Fin M.k}
    {P : Controller M} {B t : ℕ} {c : P.machine.Cfg}
    {final : (repeatMachineOn source P).Cfg} :
    RepeatTraceOnBoundedV2 source P B t c final → ℕ
  | .last .. => 1
  | .next _ _ _ _ _ _ tail => repeatTraceOnBoundedV2Rounds tail + 1

end BitDFT.MachineSequence


