-- Prove2me | Definitions.Def_BitDFT_SharedAlphabetStages
-- name    : BitDFT_SharedAlphabetStages
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-24T22:18:36.728885+00:00
-- url     : https://prove2.me/theorems/e423c1bb-2b36-4b4c-95cd-79f2e895a61c
-- title:
--   Place two machine stages on one alphabet and tape width
-- statement:
--   Given a Fourier child machine A and an integer multiplier M, embed both symbol alphabets into one finite product alphabet, then extend the smaller tape layout to the larger tape count. This gives the two stages the same physical tape width for sequential composition while retaining a named configuration embedding for arbitrary caller data.
-- source:
--   Explicit construction using the published product alphabet, tape-extension, and tape-count transport adapters. The run-preservation theorem is supplied separately.

import Definitions.Def_BitDFT_SharedAlphabet
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapeCountTransport
import Definitions.Def_BitDFT_MachineSequence

noncomputable section
namespace BitDFT.SharedAlphabetStages
open IntMul BitDFT.AlphabetEmbedding BitDFT.SharedAlphabet

def width (A M : MultitapeTM) : ℕ := max A.k M.k

def left (A M : MultitapeTM) : MultitapeTM :=
  TapeCountTransport.machine
    (TapeExtension.machine (AlphabetEmbedding.machine (SharedAlphabet.left A M))
      (width A M - A.k))
    (width A M) (Nat.add_sub_of_le (Nat.le_max_left A.k M.k))

def right (A M : MultitapeTM) : MultitapeTM :=
  TapeCountTransport.machine
    (TapeExtension.machine (AlphabetEmbedding.machine (SharedAlphabet.right A M))
      (width A M - M.k))
    (width A M) (Nat.add_sub_of_le (Nat.le_max_right A.k M.k))

def rightConfig (A M : MultitapeTM)
    (extraCells : Fin (width A M) → ℕ → (SharedAlphabet.carrier A M).Sym)
    (extraHeads : Fin (width A M) → ℕ) (c : M.Cfg) : (right A M).Cfg := by
  let r := width A M - M.k
  have hwidth : M.k + r = width A M := Nat.add_sub_of_le (Nat.le_max_right A.k M.k)
  exact TapeCountTransport.embed
    (TapeExtension.machine (AlphabetEmbedding.machine (SharedAlphabet.right A M)) r)
    (width A M) hwidth
    (TapeExtension.embed
      (AlphabetEmbedding.machine (SharedAlphabet.right A M)) r
      (fun i => extraCells (Fin.cast hwidth i))
      (fun i => extraHeads (Fin.cast hwidth i))
      (AlphabetEmbedding.embed (SharedAlphabet.right A M) c))

def rightController (A M : MultitapeTM) : MachineSequence.Controller (left A M) where
  K := (right A M).K
  entry := (right A M).qStart
  exit := (right A M).qHalt
  distinct := (right A M).start_ne_halt
  transition := (right A M).δ
  marker := (right A M).start_preserved
  noMarker := (right A M).start_only_at_start
  frozen := (right A M).halt_fixed
  readonly := (right A M).input_readonly

end BitDFT.SharedAlphabetStages


