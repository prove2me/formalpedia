-- Prove2me | Definitions.Def_OpenMath_WOWII96
-- name    : OpenMath_WOWII96
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T19:37:07.670533+00:00
-- url     : https://prove2.me/theorems/c845e361-7ed5-59d0-b344-aeb36ee4c951
-- title:
--   WOWII96
-- statement:
--   Definitions and structural lemmas for WOWII96, from Rhett (v3ai/openmath; definitions reused under Apache-2.0 from google-deepmind/formal-conjectures; see pinned LICENSE and README.md)'s pinned Proof of WOWII Conjecture 96 (DeLaVina, Graffiti.pc) development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/v3ai/openmath/blob/a5525a12ad7c35c64ac14839f505ee2624016401/OpenMath/WOWII96.lean

module
public import Definitions.Def_OpenMath_Common
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace OpenMath.WOWII96
open SimpleGraph Finset OpenMath
variable {α : Type*} [Fintype α] [DecidableEq α]
variable [Nontrivial α]
end OpenMath.WOWII96


