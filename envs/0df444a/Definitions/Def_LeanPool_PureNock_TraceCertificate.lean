-- Prove2me | Definitions.Def_LeanPool_PureNock_TraceCertificate
-- name    : LeanPool_PureNock_TraceCertificate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:00:05.885807+00:00
-- url     : https://prove2.me/theorems/68134ef5-65ca-49dd-a32b-2ba53dda1f99
-- title:
--   Trace Certificate
-- statement:
--   Definitions and structural lemmas for Trace Certificate, from Pure Nock formalization contributors; LeanPool contributors's pinned Pure Nock semantics, trace certificates, and polynomial fingerprints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PureNock/TraceCertificate.lean

module
public import Definitions.Def_LeanPool_PureNock_Trace
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace Nock
namespace Verb
def runTrace : Nat → Verb → Option (List Verb)
  | 0,        _ => none
  | fuel + 1, v =>
      match next v with
      | some v' => (runTrace fuel v').map (fun T => v :: T)
      | none    => some [v]
def runTraceProgram (fuel : Nat) (subject formula : Noun) : Option (List Verb) :=
  runTrace fuel (program subject formula)
def AdjNockCheck : List Verb → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => NockCheck a (some b) = true ∧ AdjNockCheck (b :: rest)
def adjNockCheckB : List Verb → Bool
  | []             => true
  | [_]            => true
  | a :: b :: rest => NockCheck a (some b) && adjNockCheckB (b :: rest)
end Verb
end Nock


