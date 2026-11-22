-- Prove2me | Definitions.Def_EventStructures_Family_Computation
-- name    : EventStructures_Family_Computation
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T20:52:34.026905+00:00
-- url     : https://prove2.me/theorems/5c11bb78-b08b-4d28-b0d6-9f11d814e944
-- title:
--   Computation
-- statement:
--   Definitions and structural lemmas for Computation, from Vikraman Choudhury's pinned Correct rollback in finite event structures development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Family/Computation.lean

import Definitions.Def_EventStructures_Family_Path
import Definitions.Def_EventStructures_Family_Trace
import Mathlib.Logic.Function.Basic
set_option autoImplicit true
variable {L : Type*} (F : ConfFamily L)
open ConfFamily Path Trace
def Computation (c : Conf F) : Type _ :=
  Path.Async F (ConfFamily.empty F) c
def Computations : Type _ := Σ c : Conf F, Computation F c
def isLinearisation (c : Conf F) (t : List F.Event) : Prop :=
  ∃ p : Path F (ConfFamily.empty F) c,
    ConfFamily.TraceEquivFrom F (ConfFamily.empty F).val (Path.trace F p) t
def ReachableConf : Type _ := {c : Conf F // Nonempty (Computation F c)}
def computation_to_reachable : Computations F → ReachableConf F :=
  fun p => ⟨p.1, ⟨p.2⟩⟩


