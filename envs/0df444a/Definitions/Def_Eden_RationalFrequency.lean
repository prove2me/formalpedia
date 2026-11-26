-- Prove2me | Definitions.Def_Eden_RationalFrequency
-- name    : Eden_RationalFrequency
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T14:23:29.823831+00:00
-- url     : https://prove2.me/theorems/8e074a92-9e48-4432-b645-781c8d104024
-- title:
--   Rational Frequency
-- statement:
--   Definitions and structural lemmas for Rational Frequency, from Matthew J. Colbrook (MColbrook/Eden_conjecture; see pinned Apache-2.0 LICENSE, NOTICE.md, and formalization.yaml)'s pinned Counterexample to the unrestricted form of Eden's conjecture development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/RationalFrequency.lean

import Definitions.Def_Eden_FrequencyDimensions
import Definitions.Def_Eden_FrequencyAttractor
import Definitions.Def_Eden_FrequencyUniqueness
import Mathlib.Topology.Instances.Rat
set_option autoImplicit true
noncomputable section
open Set
namespace Eden
def frequencyPeriodicSet (c ν : ℝ) : Set PhaseSpace :=
  {p | p ∈ attractor ∧ frequencyVectorField c ν p ≠ 0 ∧
    ∃ t : ℝ, 0 < t ∧ frequencyEvolution c ν t p = p}
end Eden


