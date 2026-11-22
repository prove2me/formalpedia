-- Prove2me | Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryHaar
-- name    : BornVolumeLean_LinearAlgebra_Matrix_UnitaryHaar
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:33.425255+00:00
-- url     : https://prove2.me/theorems/318662fc-5387-487d-a689-de9fed467094
-- title:
--   Unitary Haar
-- statement:
--   Definitions and structural lemmas for Unitary Haar, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Matrix/UnitaryHaar.lean

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryCompact
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory
namespace Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
noncomputable def unitaryHaarProb : Measure (Matrix.unitaryGroup ι ℂ) :=
  Measure.haarMeasure ⊤
instance instIsProbabilityMeasureUnitaryHaarProb :
    IsProbabilityMeasure (unitaryHaarProb : Measure (Matrix.unitaryGroup ι ℂ)) where
  measure_univ := by
    rw [unitaryHaarProb, ← TopologicalSpace.PositiveCompacts.coe_top]
    exact Measure.haarMeasure_self
instance unitaryHaarProb_isHaarMeasure :
    Measure.IsHaarMeasure (unitaryHaarProb : Measure (Matrix.unitaryGroup ι ℂ)) :=
  inferInstanceAs (Measure.IsHaarMeasure (Measure.haarMeasure ⊤))
end Matrix.UnitaryGroup


