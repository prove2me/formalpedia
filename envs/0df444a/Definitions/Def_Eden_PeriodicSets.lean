-- Prove2me | Definitions.Def_Eden_PeriodicSets
-- name    : Eden_PeriodicSets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T13:44:01.350054+00:00
-- url     : https://prove2.me/theorems/f4bfccd1-b93b-4cb1-adf3-ef09f0370a00
-- title:
--   Periodic Sets
-- statement:
--   Definitions and structural lemmas for Periodic Sets, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/PeriodicSets.lean

import Definitions.Def_Eden_RotationReturns
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def equilibriumSet (c : ℝ) : Set PhaseSpace := {p | vectorField c p = 0}
def positiveReturnSet (c : ℝ) : Set PhaseSpace :=
  {p | ∃ t : ℝ, 0 < t ∧ evolution c t p = p}
def periodicEquilibriumSet (c : ℝ) : Set PhaseSpace :=
  attractor ∩ (equilibriumSet c ∪ positiveReturnSet c)
def firstCircle (s : ℝ) : Set PhaseSpace :=
  {p | radiusSq₁ p = s ∧ radiusSq₂ p = 0 ∧ p 4 = 0}
def secondCircle (s : ℝ) : Set PhaseSpace :=
  {p | radiusSq₁ p = 0 ∧ radiusSq₂ p = s ∧ p 4 = 0}
end Eden


