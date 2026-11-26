-- Prove2me | Definitions.Def_BKAR_CubePartition_CubeIntegral
-- name    : BKAR_CubePartition_CubeIntegral
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:45:38.673799+00:00
-- url     : https://prove2.me/theorems/5f311ccf-82ba-4055-84eb-b8536d9e36b5
-- title:
--   Cube Integral
-- statement:
--   Definitions and structural lemmas for Cube Integral, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/CubeIntegral.lean

import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_BKAR_CubePartition_Orders
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
def unitCube (F : Forest V) : Set (F.EdgeParam → ℝ) :=
  Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
def orderedCubeSimplex (F : Forest V) (order : List (Edge V)) :
    Set (F.EdgeParam → ℝ) :=
  {u | u ∈ F.unitCube ∧
    OrderedSimplexParams 1 (order.map (F.paramValue u))}
def cubeContribution (F : Forest V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  ∫ u in F.unitCube, F.mixedPartial ρ (F.standardInterp u)
def orderedCubeSectorContribution
    (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  ∫ u in F.orderedCubeSimplex order,
    mixedPartialList order.reverse ρ (F.standardInterp u)
end Forest
end BKAR


