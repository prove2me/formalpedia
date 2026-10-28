-- Prove2me | Definitions.Def_BitDFT_BankedTripleAlphabetHost
-- name    : BitDFT_BankedTripleAlphabetHost
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-10-25T15:02:44.176914+00:00
-- url     : https://prove2.me/theorems/91060788-b21e-4c09-b280-acd1a753ab12
-- title:
--   A shared-symbol multitape host with disjoint Fourier, multiplier, header, and parked-data banks
-- statement:
--   Given a Fourier machine, a multiplier machine, and a header reader, embed each in a common finite alphabet and a fixed-width host with disjoint tape banks. The host also reserves tapes for caller data. The routed embeddings preserve exact step counts and keep all nonactive tapes unchanged.
-- source:
--   Composes the previously verified triple alphabet, tape extension, tape-count transport, and tape permutation constructions. This is the reusable infrastructure for shared-host controller proofs.

import Definitions.Def_BitDFT_DedicatedTapeBanks
import Definitions.Def_BitDFT_TripleAlphabet
import Definitions.Def_BitDFT_TapeExtension
import Definitions.Def_BitDFT_TapeCountTransport

noncomputable section
namespace BitDFT.BankedTripleAlphabetHost
open IntMul BitDFT.AlphabetEmbedding

abbrev carrier (A M H : MultitapeTM) := BitDFT.TripleAlphabet.carrier A M H

def route (A M H : MultitapeTM) (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H) :=
  BitDFT.DedicatedTapeBanks.routing (BitDFT.DedicatedTapeBanks.tail A M H) offset hoff

def machine (A M H X : MultitapeTM) (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H) : MultitapeTM := by
  let r := BitDFT.DedicatedTapeBanks.width A M H - X.k
  let h : X.k + r = BitDFT.DedicatedTapeBanks.width A M H := Nat.add_sub_of_le hX
  let E := TapeCountTransport.machine
    (TapeExtension.machine (AlphabetEmbedding.machine e) r)
    (BitDFT.DedicatedTapeBanks.width A M H) h
  exact TapePermutation.machine E (route A M H offset hoff)
    (BitDFT.DedicatedTapeBanks.routing_input _ _ hoff)

def config (A M H X : MultitapeTM) (e : AlphabetEmbedding.Map X (carrier A M H))
    (offset : ℕ) (hoff : offset < 4 + BitDFT.DedicatedTapeBanks.tail A M H)
    (hX : X.k ≤ BitDFT.DedicatedTapeBanks.width A M H)
    (extraCells : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ → (carrier A M H).Sym)
    (extraHeads : Fin (BitDFT.DedicatedTapeBanks.width A M H) → ℕ) (c : X.Cfg) :
    (machine A M H X e offset hoff hX).Cfg := by
  let r := BitDFT.DedicatedTapeBanks.width A M H - X.k
  let h : X.k + r = BitDFT.DedicatedTapeBanks.width A M H := Nat.add_sub_of_le hX
  let E := TapeCountTransport.machine
    (TapeExtension.machine (AlphabetEmbedding.machine e) r)
    (BitDFT.DedicatedTapeBanks.width A M H) h
  exact TapePermutation.embed E (route A M H offset hoff)
    (BitDFT.DedicatedTapeBanks.routing_input _ _ hoff)
    (TapeCountTransport.embed (TapeExtension.machine (AlphabetEmbedding.machine e) r)
      (BitDFT.DedicatedTapeBanks.width A M H) h
      (TapeExtension.embed (AlphabetEmbedding.machine e) r
        (fun i => extraCells (route A M H offset hoff (Fin.cast h i)))
        (fun i => extraHeads (route A M H offset hoff (Fin.cast h i)))
        (AlphabetEmbedding.embed e c)))

abbrev fourierMachine (A M H : MultitapeTM) :=
  machine A M H A (BitDFT.TripleAlphabet.fourier A M H)
    (BitDFT.DedicatedTapeBanks.fourierOffset A M H)
    (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [BitDFT.DedicatedTapeBanks.tail, BitDFT.DedicatedTapeBanks.fourierOffset]; omega)
    (by dsimp [BitDFT.DedicatedTapeBanks.width]; have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [BitDFT.DedicatedTapeBanks.tail]; omega)

abbrev multiplierMachine (A M H : MultitapeTM) :=
  machine A M H M (BitDFT.TripleAlphabet.multiplier A M H)
    (BitDFT.DedicatedTapeBanks.multiplierOffset A M H)
    (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [BitDFT.DedicatedTapeBanks.tail, BitDFT.DedicatedTapeBanks.multiplierOffset]; omega)
    (by dsimp [BitDFT.DedicatedTapeBanks.width]; have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [BitDFT.DedicatedTapeBanks.tail]; omega)

abbrev headerMachine (A M H : MultitapeTM) :=
  machine A M H H (BitDFT.TripleAlphabet.header A M H)
    (BitDFT.DedicatedTapeBanks.headerOffset A M H)
    (by have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [BitDFT.DedicatedTapeBanks.tail, BitDFT.DedicatedTapeBanks.headerOffset]; omega)
    (by dsimp [BitDFT.DedicatedTapeBanks.width]; have hA := A.two_le_k; have hM := M.two_le_k; have hH := H.two_le_k; dsimp [BitDFT.DedicatedTapeBanks.tail]; omega)

end BitDFT.BankedTripleAlphabetHost
end


