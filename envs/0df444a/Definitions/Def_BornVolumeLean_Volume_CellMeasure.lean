-- Prove2me | Definitions.Def_BornVolumeLean_Volume_CellMeasure
-- name    : BornVolumeLean_Volume_CellMeasure
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:04:42.896546+00:00
-- url     : https://prove2.me/theorems/75298800-3a5d-493e-bd85-00590cf2eb47
-- title:
--   Cell Measure
-- statement:
--   Definitions and structural lemmas for Cell Measure, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasure.lean

module
public import Definitions.Def_BornVolumeLean_Volume_CellOpen
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
namespace BornVolume
variable {M : ℕ}
end BornVolume


