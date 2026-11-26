-- Prove2me | Definitions.Def_BKAR_CubePartition_SimplexSector_Singleton
-- name    : BKAR_CubePartition_SimplexSector_Singleton
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T08:50:57.901865+00:00
-- url     : https://prove2.me/theorems/fc79c5c0-67a7-4d9b-a599-4b734ec7e93f
-- title:
--   Singleton
-- statement:
--   Definitions and structural lemmas for Singleton, from Scott Armstrong (scottnarmstrong/BKARForestFormula; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned BKAR forest interpolation formula development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/SimplexSector/Singleton.lean

import Mathlib.Data.List.NodupEquivFin
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_BKAR_CubePartition_MeasureSmoothness
import Theorems.Thm_BKAR_ForestIndex_ext

set_option autoImplicit false
noncomputable section
namespace BKAR
namespace Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
set_option warn.classDefReducibility false in
def uniqueEdgeParamOfEdgesSingleton
    (F : Forest V) {e : Edge V} (hedges : F.edges = {e}) :
    Unique F.EdgeParam where
  default := ⟨e, by rw [hedges]; exact Finset.mem_singleton_self e⟩
  uniq := by
    intro p
    apply Subtype.ext
    have hp : p.val ∈ ({e} : Finset (Edge V)) := by
      rw [← hedges]
      exact p.property
    exact Finset.mem_singleton.mp hp
end Forest
end BKAR


