-- Prove2me | Definitions.Def_Kyprianou_Ch01_branchingCountOfSequences
-- name    : Kyprianou_Ch01_branchingCountOfSequences
-- status  : Definition
-- author  : @pageman
-- created : 2026-11-24T02:06:09.975307+00:00
-- url     : https://prove2.me/theorems/f845c7e8-e31c-4f5f-bf80-b64bd73ac8b2
-- title:
--   Branching count of a sequence pair
-- statement:
--   The branching count of an interarrival/mark sequence pair at height $z$ and time $s$ is the reverse Lamperti image of the lattice walk built from those frozen sequences.
-- source:
--   Kyprianou (2006), Section 1.3.4

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Branching count read from a deterministic interarrival/mark sequence pair. -/
noncomputable def Kyprianou.Ch01.branchingCountOfSequences
    (z : ℕ) (s : ℝ≥0) (seq : (ℕ → ℝ) × (ℕ → ℝ)) : ℤ :=
  compoundPoissonToBranching
    (integerCompoundPoisson z
      (fun n (_ : Unit) => seq.1 n)
      (fun n (_ : Unit) => seq.2 n))
    s ()


