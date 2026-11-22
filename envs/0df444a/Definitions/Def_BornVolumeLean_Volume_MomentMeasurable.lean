-- Prove2me | Definitions.Def_BornVolumeLean_Volume_MomentMeasurable
-- name    : BornVolumeLean_Volume_MomentMeasurable
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:58:33.663357+00:00
-- url     : https://prove2.me/theorems/324522d2-3330-4784-81bc-4ef7fbefe071
-- title:
--   Moment Measurable
-- statement:
--   Definitions and structural lemmas for Moment Measurable, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/MomentMeasurable.lean

module
public import Definitions.Def_BornVolumeLean_Volume_MomentMap
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Matrix Matrix.UnitaryGroup
open scoped LinearAlgebra.Projectivization
namespace BornVolume
variable {N : ℕ}
end BornVolume


