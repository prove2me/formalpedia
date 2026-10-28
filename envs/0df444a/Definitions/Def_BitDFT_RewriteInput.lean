-- Prove2me | Definitions.Def_BitDFT_RewriteInput
-- name    : BitDFT_RewriteInput
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T16:39:28.761954+00:00
-- url     : https://prove2.me/theorems/b058736e-915e-4976-a821-2b356661500a
-- title:
--   Native-input preprocessor constructing the complete guarded Fourier request
-- statement:
--   A fixed five-tape machine sequences native header rewriting and suffix copying. It computes guard precision, writes the dimension and guard-precision headers, and then appends the original binary suffix. Its final configuration preserves the original native input and records the complete rewritten output.
-- source:
--   Explicit composition of RewriteHeaders and SuffixCopy; no abstract encoding oracle or free head movement is used.

import Definitions.Def_BitDFT_RewriteHeaders
import Definitions.Def_BitDFT_SuffixCopy
import Definitions.Def_BitDFT_Numerics

noncomputable section
namespace BitDFT.RewriteInput
open IntMul MachineSequence

def copyControl : Controller RewriteHeaders.machine where
  K := SuffixCopy.machine.K
  entry := SuffixCopy.machine.qStart
  exit := SuffixCopy.machine.qHalt
  distinct := SuffixCopy.machine.start_ne_halt
  transition := SuffixCopy.machine.δ
  marker := SuffixCopy.machine.start_preserved
  noMarker := SuffixCopy.machine.start_only_at_start
  frozen := SuffixCopy.machine.halt_fixed
  readonly := SuffixCopy.machine.input_readonly

abbrev machine := (sequence (native RewriteHeaders.machine) copyControl).machine

def copyBase (x tail w v : List Bool) : SuffixCopy.machine.Cfg where
  state := .copy
  cells := (RewriteHeaders.final x tail w v).cells
  head := (RewriteHeaders.final x tail w v).head

def final (n b : ℕ) (rest v : List Bool) : machine.Cfg :=
  let x := encNat n ++ encNat b ++ rest
  let out := encNat n ++ encNat (guardPrecision n b) ++ rest
  rightCfg (native RewriteHeaders.machine) copyControl
    (SuffixCopy.frame (copyBase x (bin n.size n).tail (bin b.size b) v) .halt x out (x.length+1))

end BitDFT.RewriteInput


