-- Prove2me | Definitions.Def_Yukon_639fdbc365c0d9346f33b12e
-- name    : Yukon_639fdbc365c0d9346f33b12e
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T17:58:44.079391+00:00
-- url     : https://prove2.me/theorems/663c2337-7a26-4441-a18e-9cd6719da723
-- title:
--   YukonModule.PolyFun.PFunctor.Dynamical.Safety.part0
-- statement:
--   Source module PolyFun.PFunctor.Dynamical.Safety.
-- source:
--   https://github.com/Verified-zkEVM/PolyFun/blob/dd77aa91dd425ebaec4388270f3a8e3dc7ace571/PolyFun/PFunctor/Dynamical/Safety.lean
--
--   yukon-proof-operation:34c5c005ecfdbb27e99db3841761a570082935e8bd5b06ebb62c299f2dd12d8c
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246MzRjNWMwMDVlY2ZkYmIyN2U5OWRiMzg0MTc2MWE1NzAwODI5MzVlOGJkNWIwNmViYjYyYzI5OWYyZGQxMmQ4YyIsImhhc2giOiJkNjM4N2RkODU2MDU0NTExMDkyYjA5MjJiMzQ2MDZiODNlMTRjZjBmN2JjMTNlYmFmYTQ3ZjJlZWJlNDdkMDJiIiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl82MzlmZGJjMzY1YzBkOTM0NmYzM2IxMmUiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Definitions.Def_Yukon_e50e3d739c9fe45e3e01afc1

import Batteries.Tactic.Lint


public import Mathlib.Data.PFunctor.Multivariate.Basic
public import Init
public import Mathlib.Data.FunLike.Basic
meta import Definitions.Def_Yukon_e50e3d739c9fe45e3e01afc1
set_option backward.isDefEq.respectTransparency.types false
/-!
# Labels, tickets, and verification predicates for dynamical systems

Comparison-oriented metadata attached to the transitions of a `p`-dynamical
system, kept out of `DynSystem` itself so the core dynamics stay minimal:

* `DynSystem.EventMap` / `DynSystem.Labeled` — a stable external label for each
  transition (state and direction), the observable step descriptions one wants
  to preserve under refinement or compare across runs.
* `DynSystem.Tickets` / `DynSystem.Ticketed` — a stable obligation identifier
  for each transition, the handles that fairness and liveness layers quantify
  over instead of the state-dependent direction types themselves.
* `DynSystem.SafetySpec` — a dynamical system together with an initial-state
  predicate, ambient assumptions, and a safety predicate.
Concrete steps and their relations live with the operational core in
`PFunctor.Dynamical.Basic` as `DynSystem.Step` and `DynSystem.StepRel`.

Instantiating `p` recovers the corresponding bundles for the concrete system
notions built on `DynSystem`, such as concurrent machines and processes.
-/

@[expose] public section

universe u uA uB w

namespace PFunctor

namespace DynSystem

variable {p : PFunctor.{uA, uB}}

/-- A stable external label for each transition of a dynamical system: at each
state, an assignment of an `Event` to every direction at the exposed position. -/
abbrev EventMap {S : Type u} (s : DynSystem S p) (Event : Type w) :=
  (st : S) → p.B (s.expose st) → Event

/-- A stable obligation identifier for each transition of a dynamical system.

Unlike the direction itself, a ticket is meant to persist across different
representations of the same scheduling obligation, so fairness and liveness
layers quantify over tickets rather than over the direction type of one
particular state. -/
abbrev Tickets {S : Type u} (s : DynSystem S p) (Ticket : Type w) :=
  (st : S) → p.B (s.expose st) → Ticket

set_option linter.checkUnivs false in
/-- A dynamical system equipped with a stable external event label for each
transition. This is the smallest bundle supporting statements about observable
event traces. -/
-- The system's state/interface universes and the event-label universe (`w`) are independent.
structure Labeled (p : PFunctor.{uA, uB}) extends Machine.{u} p where
  /-- The type of observable external event labels. -/
  Event : Type w
  /-- The assignment of an event label to each transition. -/
  event : toMachine.toDynSystem.EventMap Event

set_option linter.checkUnivs false in
/-- A dynamical system equipped with a stable ticket for each transition. This
is the entry point for fairness and liveness statements. -/
-- The system's state/interface universes and the ticket universe (`w`) are independent.
structure Ticketed (p : PFunctor.{uA, uB}) extends Machine.{u} p where
  /-- The type of stable scheduling-obligation identifiers. -/
  Ticket : Type w
  /-- The assignment of a ticket to each transition. -/
  ticket : toMachine.toDynSystem.Tickets Ticket

set_option linter.checkUnivs false in
/-- A safety-verification problem: dynamics together with initial states,
ambient assumptions, and the state predicate to be established.

These predicates are orthogonal to the dynamics themselves, so they are kept
out of `DynSystem` and bundled only for verification-oriented statements. -/
-- The system's state universe (`u`) and interface universes are independent.
structure SafetySpec (p : PFunctor.{uA, uB}) extends Machine.{u} p where
  /-- The predicate characterizing the system's initial states. -/
  init : State → Prop
  /-- The ambient assumptions imposed on states. -/
  assumptions : State → Prop := fun _ => True
  /-- The safety predicate that states are required to satisfy. -/
  safe : State → Prop := fun _ => True
end DynSystem

end PFunctor


