-- Prove2me | Definitions.Def_BitDFT_ChildDescriptor
-- name    : BitDFT_ChildDescriptor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T18:32:04.300278+00:00
-- url     : https://prove2.me/theorems/1b65508e-cd67-4b83-9499-3e231197fe13
-- title:
--   Run an arbitrary child and prepare the saved-precision descriptor tapes
-- statement:
--   Extend the native child-output wrapper by two fresh tapes, transport its tape-count expression to the layout expected by descriptor setup, and sequence the routed rewind-and-copy controller. The added tapes are the counter and template banks. The original computed vector and other unused workspace remain parked during setup. This machine performs descriptor preparation, not yet coordinate multiplication.
-- source:
--   Intermediate execution phase of the exact output scaler in the integer multiplication to finite-precision DFT transfer.

import Definitions.Def_BitDFT_NativeChildOutput
import Definitions.Def_BitDFT_DescriptorPlacement
import Definitions.Def_BitDFT_TapeCountTransport

noncomputable section
namespace BitDFT.ChildDescriptor
open IntMul MachineSequence

abbrev extended (M : MultitapeTM) := TapeExtension.machine (NativeChildOutput.program M) 2

theorem tape_count (M : MultitapeTM) : (extended M).k = 4+(M.k+3) := by
  change (5+M.k)+2 = 4+(M.k+3)
  omega

abbrev preparation (M : MultitapeTM) :=
  TapeCountTransport.machine (extended M) (4+(M.k+3)) (tape_count M)
abbrev setup (M : MultitapeTM) := DescriptorPlacement.machine (NativeChildOutput.program M) M.k

def setupControl (M : MultitapeTM) : Controller (preparation M) where
  K := (setup M).K
  entry := (setup M).qStart
  exit := (setup M).qHalt
  distinct := (setup M).start_ne_halt
  transition := (setup M).δ
  marker := (setup M).start_preserved
  noMarker := (setup M).start_only_at_start
  frozen := (setup M).halt_fixed
  readonly := (setup M).input_readonly

abbrev machine (M : MultitapeTM) :=
  (sequence (native (preparation M)) (setupControl M)).machine

/-- Extending by two tapes allocates blank counter banks with heads at zero. -/
def prepared (M : MultitapeTM) (c : (NativeChildOutput.program M).Cfg) : (preparation M).Cfg :=
  TapeCountTransport.embed (extended M) (4+(M.k+3)) (tape_count M)
    (TapeExtension.embed (NativeChildOutput.program M) 2
      (fun _ => (NativeChildOutput.program M).tapeOf []) (fun _ => 0) c)

def setupStart (M : MultitapeTM) (c : (NativeChildOutput.program M).Cfg) :
    (setupControl M).machine.Cfg :=
  handoff (native (preparation M)) (setupControl M) (prepared M c)
def sourceBase (input : List Bool) (h0 : ℕ) : RewoundDescriptor.storage.Cfg where
  state := .start
  cells := (DescriptorSetup.machine.initCfg input []).cells
  head := fun i => if i = 0 then h0 else 0

def final (M : MultitapeTM) (input : List Bool) (c : (NativeChildOutput.program M).Cfg)
    (y : List Bool) : (machine M).Cfg :=
  rightCfg (native (preparation M)) (setupControl M)
    (DescriptorPlacement.embed (NativeChildOutput.program M) M.k (setupStart M c).cells (setupStart M c).head
      (RewoundDescriptor.final (sourceBase input (c.head (NativeChildOutput.program M).inTape)) y))

end BitDFT.ChildDescriptor


