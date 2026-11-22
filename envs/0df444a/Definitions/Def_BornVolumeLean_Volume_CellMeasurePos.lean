-- Prove2me | Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
-- name    : BornVolumeLean_Volume_CellMeasurePos
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:03:21.950893+00:00
-- url     : https://prove2.me/theorems/2f0369c7-3e87-4383-9fba-5f3b89c0007f
-- title:
--   Cell Measure Pos
-- statement:
--   Definitions and structural lemmas for Cell Measure Pos, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellMeasurePos.lean

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_VertexReplacement
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
namespace BornVolume
variable {M : ℕ}
end BornVolume


