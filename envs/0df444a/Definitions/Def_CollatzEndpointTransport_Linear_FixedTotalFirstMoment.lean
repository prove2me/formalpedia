-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalFirstMoment
-- name    : CollatzEndpointTransport_Linear_FixedTotalFirstMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:22:11.687836+00:00
-- url     : https://prove2.me/theorems/1fe33198-2330-54f4-894d-b6b6b56fd556
-- title:
--   Fixed Total First Moment
-- statement:
--   Definitions and structural lemmas for Fixed Total First Moment, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalFirstMoment.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCompositionRecurrence
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
def lengthPowSum (N : ℕ) : ℕ :=
  ∑ c : Composition N, 3 ^ c.length
def numeratorSum (N : ℕ) : ℕ :=
  ∑ c : Composition N, syracuseNumerator c
end
end FixedTotal
end CollatzEndpointTransport


