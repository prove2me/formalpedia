-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMassBound
-- name    : CollatzEndpointTransport_Linear_FractionalBinomialMassBound
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:49:48.246593+00:00
-- url     : https://prove2.me/theorems/1abf98dc-f030-48b2-b7ba-36a2a8f28a44
-- title:
--   Fractional Binomial Mass Bound
-- statement:
--   Definitions and structural lemmas for Fractional Binomial Mass Bound, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FractionalBinomialMassBound.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FractionalBinomialMass
import Mathlib.Analysis.SpecificLimits.Basic
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
set_option maxHeartbeats 400000
def fractionalBinomialMassConstant (theta : ℝ) : ℝ :=
  (8 : ℝ) ^ theta * (2 : ℝ) ^ (1 - theta) *
    (1 - Real.exp (-2 * (1 - theta)))⁻¹
end
end FixedTotal
end CollatzEndpointTransport


