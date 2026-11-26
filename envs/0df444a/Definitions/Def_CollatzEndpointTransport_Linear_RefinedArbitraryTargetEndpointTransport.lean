-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
-- name    : CollatzEndpointTransport_Linear_RefinedArbitraryTargetEndpointTransport
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T09:11:17.520276+00:00
-- url     : https://prove2.me/theorems/e33ef99d-a98b-53b9-990a-80c1343e822c
-- title:
--   Refined Arbitrary Target Endpoint Transport
-- statement:
--   Definitions and structural lemmas for Refined Arbitrary Target Endpoint Transport, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/RefinedArbitraryTargetEndpointTransport.lean

import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiMomentTransport
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open scoped Real
noncomputable section
def holderTargetExponent (theta : ℝ) : ℝ :=
  theta / (1 + theta)
def holderScaleExponent (theta : ℝ) : ℝ :=
  theta / (2 * (1 + theta))
def refinedCentralRenyiInverseRateFactor
    (theta transport : ℝ) : ℝ :=
  let B := holderScaleExponent theta
  (((B / (1 - centralRenyiAbsorption theta transport)) *
      (centralRenyiAbsorption theta transport /
        (transport * Real.log 2))) ^ B)
def refinedCentralRenyiLargeShellConstant
    (theta eta transport : ℝ) : ℝ :=
  let B := holderScaleExponent theta
  4 * ((eta * Real.log 2 / 16)⁻¹) + 2 +
    holderCentralMomentConstant theta eta *
      ((2 : ℝ) ^ B *
        refinedCentralRenyiInverseRateFactor theta transport)
def refinedCentralRenyiShellConstant
    (theta eta transport : ℝ) : ℝ :=
  refinedCentralRenyiLargeShellConstant theta eta transport +
    Real.exp ((eta ^ 2 / 8) * centralRenyiStartupIndex theta eta)
end
end FixedTotal
end CollatzEndpointTransport


