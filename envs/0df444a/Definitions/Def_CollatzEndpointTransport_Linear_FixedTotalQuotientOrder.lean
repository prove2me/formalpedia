-- Prove2me | Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
-- name    : CollatzEndpointTransport_Linear_FixedTotalQuotientOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:21:13.594942+00:00
-- url     : https://prove2.me/theorems/89152c1b-ac36-5e1a-aad7-5a368cd68170
-- title:
--   Fixed Total Quotient Order
-- statement:
--   Definitions and structural lemmas for Fixed Total Quotient Order, from Idris Ali Shaik (shaikidris/CollatzEndpointTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Refined arbitrary-target transport through Collatz endpoints development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/CollatzEndpointTransport-Palomar/blob/9505e8fd59f2b49a2dad269436766319c57b4012/CollatzEndpointTransport/Linear/FixedTotalQuotientOrder.lean

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalComposition
import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false
namespace CollatzEndpointTransport
namespace FixedTotal
open Nat Finset
noncomputable section
def residueFiber
    {α : Type*} [DecidableEq α]
    (W : Finset α) (A : α → ℕ) (m : ℕ) (a : Fin m) : Finset α :=
  W.filter fun x => A x % m = a
end
end FixedTotal
end CollatzEndpointTransport


