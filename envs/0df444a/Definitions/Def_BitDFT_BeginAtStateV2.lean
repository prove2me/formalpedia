-- Prove2me | Definitions.Def_BitDFT_BeginAtStateV2
-- name    : BitDFT_BeginAtStateV2
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T21:46:23.231013+00:00
-- url     : https://prove2.me/theorems/9f2c6ad9-ced0-4162-b571-fab85bddca08
-- title:
--   Begin a composed controller at a continuation state
-- statement:
--   Given compatible finite controllers P and Q, form the composite controller whose entry is any chosen state of P and whose exit is Q’s exit. Its configuration type is identified with the ordinary P-then-Q sequence configuration, allowing an already halted computation to continue through Q.
-- source:
--   A state-shifted controller wrapper used to compose extraction and postprocessing as one machine run.

import Definitions.Def_BitDFT_RecordSuffixCopy
import Definitions.Def_BitDFT_MachineSequence
open IntMul
open IntMul (MultitapeTM)
noncomputable def begin_at_state {M : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller M) (q : P.K) :
    BitDFT.MachineSequence.Controller M := by
  let S := BitDFT.MachineSequence.sequence P Q
  exact {
    K := P.K ⊕ Q.K
    entry := Sum.inl q
    exit := Sum.inr Q.exit
    distinct := by intro h; cases h
    transition := S.transition
    marker := S.marker
    noMarker := S.noMarker
    frozen := S.frozen
    readonly := S.readonly
  }

def to_begin_at_state_cfg {M : MultitapeTM}
    (P Q : BitDFT.MachineSequence.Controller M) (q : P.K)
    (c : (BitDFT.MachineSequence.sequence P Q).machine.Cfg) :
    (begin_at_state P Q q).machine.Cfg := ⟨c.state,c.cells,c.head⟩


