-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
-- name    : CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:10:17.927362+00:00
-- url     : https://prove2.me/theorems/4aae4008-ff5f-5986-a6df-74db7c407ba8
-- title:
--   Refined Central Renyi Moment Transport
-- statement:
--   Definitions and structural lemmas for Refined Central Renyi Moment Transport, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedCentralRenyiMomentTransport.lean

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiShellTransport
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralEndpointInformation
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open scoped Real
noncomputable section
def holderCentralMomentConstant (theta eta : ℝ) : ℝ :=
  (2 * (3 : ℝ) ^ theta *
      (fixedSizeCentralMomentConstant theta eta *
        fractionalBinomialMassConstant theta)) ^
    (1 / (1 + theta))
end
end FixedTotal
end CollatzEndpointTransport


