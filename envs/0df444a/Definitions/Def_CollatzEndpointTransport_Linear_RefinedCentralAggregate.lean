-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
-- name    : CollatzEndpointTransport_Linear_RefinedCentralAggregate
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:51:46.169666+00:00
-- url     : https://prove2.me/theorems/5b32c4ed-ecbf-582a-94c6-6aaacf182f8e
-- title:
--   Refined Central Aggregate
-- statement:
--   Definitions and structural lemmas for Refined Central Aggregate, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralAggregate.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
end
end FixedTotal
end CollatzEndpointTransport


