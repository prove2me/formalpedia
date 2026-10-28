-- Prove2me | Definitions.Def_BitDFT_TripleAlphabet
-- name    : BitDFT_TripleAlphabet
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:01:59.028302+00:00
-- url     : https://prove2.me/theorems/6dced96a-3d36-4917-ac47-b4fadfba4f20
-- title:
--   A common finite alphabet for three multitape computations
-- statement:
--   For three multitape machines, construct a finite product alphabet that embeds each component symbol while preserving blank, start, zero, one, and separator symbols. The three component encodings are injective, allowing their tapes to be simulated in one common symbol alphabet.
-- source:
--   Composes the published shared-alphabet embedding twice. This provides the symbol representation used by the banked Fourier/multiplier/header host.

import Definitions.Def_BitDFT_SharedAlphabet

noncomputable section
namespace BitDFT.TripleAlphabet
open IntMul BitDFT.AlphabetEmbedding BitDFT.SharedAlphabet

/-- Common symbol carrier for the Fourier child, multiplier, and request parser. -/
abbrev carrier (A M H : MultitapeTM) :=
  BitDFT.SharedAlphabet.carrier (BitDFT.SharedAlphabet.carrier A M) H

def compose {A M N : MultitapeTM} (e : AlphabetEmbedding.Map A M)
    (f : AlphabetEmbedding.Map M N) : AlphabetEmbedding.Map A N where
  encode := ⟨fun a => f.encode (e.encode a), by
    intro a b h
    exact e.encode.injective (f.encode.injective h)⟩
  blank := by change f.encode (e.encode A.blank) = N.blank; rw [e.blank, f.blank]
  marker := by change f.encode (e.encode A.startSym) = N.startSym; rw [e.marker, f.marker]
  zero := by change f.encode (e.encode A.zero) = N.zero; rw [e.zero, f.zero]
  one := by change f.encode (e.encode A.one) = N.one; rw [e.one, f.one]
  sep := by change f.encode (e.encode A.sep) = N.sep; rw [e.sep, f.sep]

def fourier (A M H : MultitapeTM) : AlphabetEmbedding.Map A (carrier A M H) :=
  compose (BitDFT.SharedAlphabet.left A M)
    (BitDFT.SharedAlphabet.left (BitDFT.SharedAlphabet.carrier A M) H)

def multiplier (A M H : MultitapeTM) : AlphabetEmbedding.Map M (carrier A M H) :=
  compose (BitDFT.SharedAlphabet.right A M)
    (BitDFT.SharedAlphabet.left (BitDFT.SharedAlphabet.carrier A M) H)

def header (A M H : MultitapeTM) : AlphabetEmbedding.Map H (carrier A M H) :=
  BitDFT.SharedAlphabet.right (BitDFT.SharedAlphabet.carrier A M) H

end BitDFT.TripleAlphabet


