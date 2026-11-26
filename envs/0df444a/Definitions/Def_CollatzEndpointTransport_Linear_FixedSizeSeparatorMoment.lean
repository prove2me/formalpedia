-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
-- name    : CollatzEndpointTransport_Linear_FixedSizeSeparatorMoment
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:38:32.830791+00:00
-- url     : https://prove2.me/theorems/84617c1f-3194-4d38-a2f3-c2f833f6674e
-- title:
--   Fixed Size Separator Moment
-- statement:
--   Definitions and structural lemmas for Fixed Size Separator Moment, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedSizeSeparatorMoment.lean

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Factorial.BigOperators
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
open scoped Real
noncomputable section
variable {α : Type*} [DecidableEq α]
end
end FixedTotal
end CollatzEndpointTransport


