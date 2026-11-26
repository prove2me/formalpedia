-- Prove2me | Definitions.Def_CollatzEndpointTransport_Common_TerrasOrbitEnvelope
-- name    : CollatzEndpointTransport_Common_TerrasOrbitEnvelope
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:18:01.058003+00:00
-- url     : https://prove2.me/theorems/dca6fe8d-269c-4823-ba52-4488793cbd55
-- title:
--   Terras Orbit Envelope
-- statement:
--   Definitions and structural lemmas for Terras Orbit Envelope, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Common/TerrasOrbitEnvelope.lean

import Definitions.Def_CollatzEndpointTransport_Common_QuantitativeDensityConstants
import Definitions.Def_CollatzEndpointTransport_Common_TerrasAffineIterate
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace Terras
open Nat Finset
open scoped Real
noncomputable def centralOrbitScale (k : ℕ) : ℝ :=
  (3 : ℝ) ^ ((k : ℝ) / 2) / (2 : ℝ) ^ k
end Terras
end CollatzEndpointTransport


