-- Prove2me | Definitions.Def_BitDFT_RewoundDescriptor
-- name    : BitDFT_RewoundDescriptor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:10:10.538989+00:00
-- url     : https://prove2.me/theorems/6a02ee3e-18a3-4657-a3bd-90f16b913291
-- title:
--   Prepare two descriptor tapes from a source head at the end of its binary word — machine
-- statement:
--   Given a binary descriptor y on the source tape, with its head immediately after the word and both destination tapes blank with heads at their markers, the combined machine prepares the two delimited descriptor tapes within 2|y|+6 transitions. Both target heads finish at the low-order end. The bound includes the rewind, the controller handoff, and the complete descriptor-copy routine. Source and parked native tape contents are preserved.
-- source:
--   Charged setup for the exact output scaler in the finite-precision DFT transfer mission.

import Definitions.Def_BitDFT_RewindTape
import Definitions.Def_BitDFT_DescriptorSetup

noncomputable section
namespace BitDFT.RewoundDescriptor
open IntMul MachineSequence
abbrev storage := DescriptorSetup.machine
abbrev rewind := RewindTape.control storage 1
abbrev copy := native storage
abbrev machine := (sequence rewind copy).machine

def initial (base : storage.Cfg) (y : List Bool) : machine.Cfg :=
  leftCfg rewind copy (RewindTape.frame storage 1 (DescriptorSetup.initial base y) false (y.length+1))
def final (base : storage.Cfg) (y : List Bool) : machine.Cfg :=
  rightCfg rewind copy (DescriptorSetup.final base y)
end BitDFT.RewoundDescriptor


