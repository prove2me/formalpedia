-- Prove2me | Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
-- name    : BKAR_CubePartition_SimplexSector_Finite
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:59:27.320859+00:00
-- url     : https://prove2.me/theorems/f670e6e9-3a4d-4abb-aee8-5d1b8973a90b
-- title:
--   Finite
-- statement:
--   Definitions and structural lemmas for Finite, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Finite.lean

import Definitions.Def_BKAR_CubePartition_SimplexSector
set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
def orderedFinSimplexWithTop (top : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {ts | OrderedSimplexParams top (List.ofFn ts)}
def orderedFinSimplexHeadTail (top : ℝ) (n : ℕ) :
    Set (ℝ × (Fin n → ℝ)) :=
  {z | z.1 ∈ Set.Icc (0 : ℝ) top ∧
    z.2 ∈ orderedFinSimplexWithTop z.1 n}
end Forest
end BKAR


