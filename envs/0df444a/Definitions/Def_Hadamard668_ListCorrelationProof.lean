-- Prove2me | Definitions.Def_Hadamard668_ListCorrelationProof
-- name    : Hadamard668_ListCorrelationProof
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T19:39:28.887418+00:00
-- url     : https://prove2.me/theorems/f895d6c7-081e-4180-bd82-c763c2fce090
-- title:
--   List Correlation Proof
-- statement:
--   Definitions and structural lemmas for List Correlation Proof, from Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz (Arthur742Ramos/hadamard-668-lean; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Certified Hadamard matrix of order 668 development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Arthur742Ramos/hadamard-668-lean/blob/78fbae8d69b6fdb66705b662469692d60e346ef0/Hadamard668/ListCorrelationProof.lean

import Definitions.Def_Hadamard668_CertificateData
import Definitions.Def_Hadamard668_CorrelationData
import Mathlib
set_option autoImplicit true
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Hadamard668
def hammingInt (xs ys : List ℤ) : Nat :=
  (xs.zipWith (fun x y => if x == y then 0 else 1) ys).sum
def shiftList (right : Bool) (k : Nat) (xs : List ℤ) : List ℤ :=
  if right then xs.rotate (xs.length - k) else xs.rotate k
def baseListTable (a b q : Nat) (right : Bool) : List Nat :=
  (List.range 166).map (fun k =>
    hammingInt ((bases668[a]!)[q]!)
      (shiftList right k ((bases668[b]!)[q]!)))
def baseExpectedTable (a b q : Nat) (right : Bool) : List Nat :=
  (((baseCorrelationExpected668[a]!)[b]!)[q]!)[if right then 1 else 0]!
def topChunkList (t q : Nat) : List ℤ :=
  ((top668[t]!).drop 4).drop (166 * q) |>.take 166
def topListTable (t a q : Nat) : List Nat :=
  (List.range 166).map (fun k =>
    hammingInt (topChunkList t q)
      (shiftList ((dirs668[a]!)[q]!) k ((bases668[a]!)[q]!)))
def topExpectedTable (t a q : Nat) : List Nat :=
  ((topCorrelationExpected668[t]!)[a]!)[q]!
end Hadamard668


