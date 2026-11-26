-- Prove2me | Definitions.Def_Eden_PeriodicOrbits
-- name    : Eden_PeriodicOrbits
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:46:20.707618+00:00
-- url     : https://prove2.me/theorems/105f0e46-af2b-53c0-9c5c-ed7ccd6cc91c
-- title:
--   Periodic Orbits
-- statement:
--   Definitions and structural lemmas for Periodic Orbits, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicOrbits.lean

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def geometricPeriodicOrbits (c : ℝ) : Set (Set PhaseSpace) :=
  {O | ∃ p : PhaseSpace, p ∈ positiveReturnSet c ∧ p ∉ equilibriumSet c ∧ forwardOrbit c p = O}
end Eden


