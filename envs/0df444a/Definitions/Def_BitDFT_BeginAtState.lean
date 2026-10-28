-- Prove2me | Definitions.Def_BitDFT_BeginAtState
-- name    : BitDFT_BeginAtState
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T20:12:33.768729+00:00
-- url     : https://prove2.me/theorems/dce34931-0d4c-449e-84f9-55a1a7c3e0b8
-- statement:
--   For compatible finite controllers P and Q, this definition starts their sequential composition at a chosen state of P and exits at Q’s exit. It lets a machine already at an internal continuation state proceed through the remaining controller while preserving the same tape configuration.
-- source:
--   Corrected the namespace import so the controller continuation definition compiles in the target Lean environment. Required by the first-coordinate output postprocessing proof.

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


