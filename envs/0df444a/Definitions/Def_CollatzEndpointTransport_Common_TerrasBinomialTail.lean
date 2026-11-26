-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_TerrasBinomialTail
-- name    : CollatzEndpointTransport_Common_TerrasBinomialTail
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:16:12.694431+00:00
-- url     : https://prove2.me/theorems/9d2d83ab-c219-5531-b919-06bceece83b6
-- title:
--   Terras Binomial Tail
-- statement:
--   Definitions and structural lemmas for Terras Binomial Tail, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasBinomialTail.lean

import Definitions.Def_CollatzEndpointTransport_Common_TerrasParityBijection
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
open Nat Finset
def lowerBinomialSum (H K : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (K + 1), H.choose k
end Terras
end CollatzEndpointTransport


