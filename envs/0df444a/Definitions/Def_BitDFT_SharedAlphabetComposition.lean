-- Prove2me | Definitions.Def_BitDFT_SharedAlphabetComposition
-- name    : BitDFT_SharedAlphabetComposition
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T22:23:35.521586+00:00
-- url     : https://prove2.me/theorems/8dbfa5cb-2f33-41bd-9c5d-a26b3d29ef5c
-- title:
--   Sequence the child and multiplier in a shared machine layout
-- statement:
--   Build one finite sequential controller whose first stage runs the child machine and whose second stage runs the integer multiplier. Both stages use the published common product alphabet and the same maximum tape width. The controller exposes exact initial, handoff, and final configurations for the two-stage execution.
-- source:
--   Finite controller composition over the previously published shared-alphabet, tape-extension, and tape-count-transport adapters. The additive runtime theorem for the complete sequence is supplied separately.

import Definitions.Def_BitDFT_SharedAlphabetStages
import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.SharedAlphabetComposition
open IntMul

abbrev leftStage (A M : MultitapeTM) := BitDFT.SharedAlphabetStages.left A M
abbrev rightStage (A M : MultitapeTM) := BitDFT.SharedAlphabetStages.right A M
abbrev first (A M : MultitapeTM) := BitDFT.MachineSequence.native (leftStage A M)
abbrev second (A M : MultitapeTM) := BitDFT.SharedAlphabetStages.rightController A M
abbrev program (A M : MultitapeTM) := BitDFT.MachineSequence.sequence (first A M) (second A M)

def start (A M : MultitapeTM) (c : (leftStage A M).Cfg) : (program A M).machine.Cfg :=
  BitDFT.MachineSequence.leftCfg (first A M) (second A M) c

def handoff (A M : MultitapeTM) (c : (leftStage A M).Cfg) : (second A M).machine.Cfg :=
  BitDFT.MachineSequence.handoff (first A M) (second A M) c

def finish (A M : MultitapeTM) (c : (second A M).machine.Cfg) : (program A M).machine.Cfg :=
  BitDFT.MachineSequence.rightCfg (first A M) (second A M) c

end BitDFT.SharedAlphabetComposition


