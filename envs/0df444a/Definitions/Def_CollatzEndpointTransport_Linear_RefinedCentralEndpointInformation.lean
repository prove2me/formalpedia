-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
-- name    : CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:08:00.874902+00:00
-- url     : https://prove2.me/theorems/03d3ba32-24c6-4306-9c40-e001f85e4a7f
-- title:
--   Refined Central Endpoint Information
-- statement:
--   Definitions and structural lemmas for Refined Central Endpoint Information, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralEndpointInformation.lean

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralAggregate
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 600000
end
end FixedTotal
end CollatzEndpointTransport


