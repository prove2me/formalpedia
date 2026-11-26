-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalWordCorrection
-- name    : CollatzEndpointTransport_Linear_FixedTotalWordCorrection
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:26:18.032806+00:00
-- url     : https://prove2.me/theorems/dc70dd9a-44ec-4f1d-827b-4c6a77dcbe1f
-- title:
--   Fixed Total Word Correction
-- statement:
--   Definitions and structural lemmas for Fixed Total Word Correction, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalWordCorrection.lean

import Definitions.Def_CollatzEndpointTransport_Common_TerrasIntegerAffine
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Data.List.OfFn
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
def wordCorrectionFrom : ℕ → ℕ → List Bool → ℕ
  | _, c, [] => c
  | i, c, b :: bs =>
      wordCorrectionFrom (i + 1)
        (if b then 3 * c + 2 ^ i else c) bs
def encodePart (k : ℕ) : List Bool :=
  true :: List.replicate (k - 1) false
def encodeBlocks : List ℕ → List Bool
  | [] => []
  | k :: ks => encodePart k ++ encodeBlocks ks
end FixedTotal
end CollatzEndpointTransport


