-- Prove2me | Definitions.Def_BitDFT_RewriteHeaders
-- name    : BitDFT_RewriteHeaders
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:34:49.482891+00:00
-- url     : https://prove2.me/theorems/213d5ceb-6637-449a-9a4a-48f39f2b3969
-- title:
--   Native-input machine rewriting the requested precision header
-- statement:
--   A fixed five-tape machine sequences native guard-precision computation and exact two-header serialization. It starts with the original request on native input and leaves the rewritten dimension and guard-precision headers on native output. The final configuration retains the input suffix position and canonical precision bits.
-- source:
--   Concrete composition of NativePrecision and HeaderSerialization, with all physical tape and head handoffs verified.

import Definitions.Def_BitDFT_NativePrecision
import Definitions.Def_BitDFT_HeaderSerialization

noncomputable section
namespace BitDFT.RewriteHeaders
open IntMul MachineSequence

def writerControl : Controller NativePrecision.machine where
  K := HeaderSerialization.machine.K
  entry := HeaderSerialization.machine.qStart
  exit := HeaderSerialization.machine.qHalt
  distinct := HeaderSerialization.machine.start_ne_halt
  transition := HeaderSerialization.machine.δ
  marker := HeaderSerialization.machine.start_preserved
  noMarker := HeaderSerialization.machine.start_only_at_start
  frozen := HeaderSerialization.machine.halt_fixed
  readonly := HeaderSerialization.machine.input_readonly

abbrev machine := (sequence (native NativePrecision.machine) writerControl).machine

def writerBase (x tail w v : List Bool) : HeaderSerialization.storage.Cfg where
  state := .start
  cells := (NativePrecision.final x tail w v).cells
  head := (NativePrecision.final x tail w v).head

def final (x tail w v : List Bool) : machine.Cfg :=
  rightCfg (native NativePrecision.machine) writerControl
    (HeaderSerialization.final (writerBase x tail w v) (true::tail) v [])

end BitDFT.RewriteHeaders


