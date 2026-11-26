-- Prove2me | Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
-- name    : FirstPassageLinearTransport_FixedJointExceptionalOrder
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T12:30:58.2231+00:00
-- url     : https://prove2.me/theorems/d3592305-e03f-5381-bde1-6b45ab7330e7
-- title:
--   Fixed Joint Exceptional Order
-- statement:
--   Definitions and structural lemmas for Fixed Joint Exceptional Order, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FixedJointExceptionalOrder.lean

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
set_option autoImplicit true
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
def fixedJointPolylogTarget (C A : ℝ) (n : ℕ) : ℝ :=
  C * (Real.log n) ^ A
def fixedJointPolylogHeight (q : ℝ) (n : ℕ) : ℝ :=
  (((Nat.log 2 n : ℕ) : ℝ) + 2) ^ q
end
end FirstPassageLinearTransport


