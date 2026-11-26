-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
-- name    : CollatzEndpointTransport_Linear_FixedSizeCentralRenyiMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:39:40.438566+00:00
-- url     : https://prove2.me/theorems/674d3e62-cc3b-4d95-8e9a-853f69dacb81
-- title:
--   Fixed Size Central Renyi Moment
-- statement:
--   Definitions and structural lemmas for Fixed Size Central Renyi Moment, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeCentralRenyiMoment.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorReverse
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
def fixedSizeCentralMomentConstant (theta eta : ℝ) : ℝ :=
  4 * (centralRenyiPiStar theta eta /
      ((2 : ℝ) ^ theta - 1 -
        centralRenyiPiStar theta eta * ((3 : ℝ) ^ theta - 1)) + 2)
end
end FixedTotal
end CollatzEndpointTransport


