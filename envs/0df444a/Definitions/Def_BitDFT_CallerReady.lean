-- Prove2me | Definitions.Def_BitDFT_CallerReady
-- name    : BitDFT_CallerReady
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T17:22:44.451991+00:00
-- url     : https://prove2.me/theorems/966faa2b-747e-4cc9-9e89-6a73e48a21ba
-- title:
--   Native request preparation with physically positioned child-bank heads
-- statement:
--   Sequence native precision rewriting and buffer preparation with the one-transition child-bank head setup. The resulting machine has 5+r tapes over any target alphabet and explicit complete final configurations. Both stage handoffs and all head movements are actual transitions.
-- source:
--   Final physical preparation stage before invoking the reusable tracked arbitrary Fourier-machine caller.

import Definitions.Def_BitDFT_PrepareCall
import Definitions.Def_BitDFT_BankHeadSetup

noncomputable section
namespace BitDFT.CallerReady
open IntMul MachineSequence

abbrev preparation (N : MultitapeTM) (r : ℕ) := PrepareCall.machine N r
abbrev headControl (N : MultitapeTM) (r : ℕ) := BankHeadSetup.control (preparation N r) r
abbrev machine (N : MultitapeTM) (r : ℕ) :=
  (sequence (native (preparation N r)) (headControl N r)).machine

def final (N : MultitapeTM) (r : ℕ) (c : RewriteInput.machine.Cfg) (w : List Bool) :
    (machine N r).Cfg :=
  rightCfg (native (preparation N r)) (headControl N r)
    (BankHeadSetup.finish (preparation N r) r (PrepareCall.final N r c w))

end BitDFT.CallerReady


