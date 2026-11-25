-- Prove2me | Definitions.Def_DiracCycleLib_DiracCycle
-- name    : DiracCycleLib_DiracCycle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T21:45:51.106103+00:00
-- url     : https://prove2.me/theorems/7aa0f7b8-93cf-58ab-8a26-9d60e5fce057
-- title:
--   Dirac Cycle
-- statement:
--   Definitions and structural lemmas for Dirac Cycle, from Juan Pablo Traverso Gianini (jtraverso/dirac-common-cycle; see pinned Apache-2.0 LICENSE and source headers)'s pinned Dirac's theorem: k vertices of a k-connected graph lie on a common cycle development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/dirac-common-cycle/blob/3c9e9966662cb99c0e4f11d771011bc904dc627f/DiracCycleLib/DiracCycle.lean

module
public import Mathlib
public import Definitions.Def_MengerHamilton_ChvatalErdosAux
set_option autoImplicit true
@[expose] public section
@[expose] public section
open Finset SimpleGraph
namespace DiracCycle
section Aux
open Hamiltonicity
variable {V : Type*} {G : SimpleGraph V}
end Aux
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
end DiracCycle


