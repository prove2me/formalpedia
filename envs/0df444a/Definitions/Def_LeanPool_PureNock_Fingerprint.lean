-- Prove2me | Definitions.Def_LeanPool_PureNock_Fingerprint
-- name    : LeanPool_PureNock_Fingerprint
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:02:46.085118+00:00
-- url     : https://prove2.me/theorems/860661c2-b7fc-4cd9-9127-7cc285404c9f
-- title:
--   Fingerprint
-- statement:
--   Definitions and structural lemmas for Fingerprint, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/Fingerprint.lean

module
public import Definitions.Def_LeanPool_PureNock_NPR
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace NPR
open Polynomial
def hornerEval {K : Type*} [Semiring K] (r : K) : List K → K
  | []     => 0
  | a :: l => a + r * hornerEval r l
section Horner
variable {K : Type*} [Field K]
def fnHorner (r : K) (n : Noun) : K × K × K :=
  (r ^ n.leaves, hornerEval r (leafF n), hornerEval r (dyckBits n))
end Horner
end NPR
end Nock


