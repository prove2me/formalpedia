-- Prove2me | Definitions.Def_FreeOrderEPTAS_IsLPSolver
-- name    : FreeOrderEPTAS_IsLPSolver
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:25:03.200808+00:00
-- url     : https://prove2.me/theorems/e016467c-a4b8-41c4-827c-d11be823b4fd
-- title:
--   The LP solver hypothesis
-- statement:
--   An LP solver takes an (LP) to a vector or to `none`. `IsLPSolver lp` says that a returned vector is feasible and that a feasible (LP) gets an answer. `callLP` is one counted call: it charges the writing of the instance, one LP unit, and records the size.
--
--   The paper uses an LP solver as a primitive at this step; the mission makes it a parameter, so that the running-time claim is relative to it.
--
--   **Formalization Note** The hypothesis is satisfiable: the sanity file gives a witness by choice.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.5, p.12, "We first compute a feasible solution y∗"

import Mathlib
import Definitions.Def_FreeOrderEPTAS_LPData
import Definitions.Def_FreeOrderEPTAS_Prog

namespace FreeOrderEPTAS

/-- An LP feasibility subroutine ("We first compute a feasible solution y* to the linear program",
§2.5, arXiv:2007.13121v3, p.12). -/
abbrev LPSolver : Type := (P : LPData) → Option P.Vars

/-- What the program may assume of the solver: an answer is feasible, and a feasible LP gets one. -/
structure IsLPSolver (lp : LPSolver) : Prop where
  /-- Every returned vector is feasible. -/
  sound : ∀ P y, lp P = some y → P.Feasible y
  /-- A feasible LP is solved. -/
  complete : ∀ P, (∃ y, P.Feasible y) → lp P ≠ none

/-- One counted LP solve. Writing the instance costs `P.size` operations; `maxSize` records it. -/
noncomputable def callLP (lp : LPSolver) (P : LPData) : Prog (Option P.Vars) := do
  modify fun c => { c with
    ops := c.ops + P.size, lpCalls := c.lpCalls + 1, maxSize := max c.maxSize P.size }
  pure (lp P)

end FreeOrderEPTAS


