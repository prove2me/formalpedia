-- Prove2me | Definitions.Def_BitDFT_NativePrecision
-- name    : BitDFT_NativePrecision
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:11:44.691008+00:00
-- url     : https://prove2.me/theorems/75281556-cd15-4000-b499-6e446265e151
-- title:
--   A fixed native-input machine parsing headers and computing guard precision
-- statement:
--   A five-tape machine reads two native input headers and then executes the verified setup-and-precision program. No prepared work tape is supplied. The caller configuration retains the native input and its suffix position; the final configuration specifies the computed precision word and retained dimension.
-- source:
--   Finite-controller composition of RequestHeaders and ParsedPrecision with a verified physical handoff.

import Definitions.Def_BitDFT_RequestHeaders
import Definitions.Def_BitDFT_ParsedPrecision

noncomputable section
namespace BitDFT.NativePrecision
open IntMul MachineSequence

def precisionControl : Controller RequestHeaders.machine where
  K := ParsedPrecision.machine.K
  entry := ParsedPrecision.machine.qStart
  exit := ParsedPrecision.machine.qHalt
  distinct := ParsedPrecision.machine.start_ne_halt
  transition := ParsedPrecision.machine.δ
  marker := ParsedPrecision.machine.start_preserved
  noMarker := ParsedPrecision.machine.start_only_at_start
  frozen := ParsedPrecision.machine.halt_fixed
  readonly := ParsedPrecision.machine.input_readonly

abbrev machine := (sequence (native RequestHeaders.machine) precisionControl).machine

def caller (x n w : List Bool) : PrecisionProgram.arithmetic.Cfg where
  state := .halt
  cells := (RequestHeaders.secondFinished x n w).cells
  head := (RequestHeaders.secondFinished x n w).head

def final (x tail w v : List Bool) : machine.Cfg :=
  rightCfg (native RequestHeaders.machine) precisionControl
    (ParsedPrecision.final (caller x (true::tail) w) tail v)

end BitDFT.NativePrecision


