-- Prove2me | Definitions.Def_BornVolumeLean_Volume_CellOpen
-- name    : BornVolumeLean_Volume_CellOpen
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:03:44.818014+00:00
-- url     : https://prove2.me/theorems/ac2267ab-b8d4-4ea0-9126-704884c8e58a
-- title:
--   Cell Open
-- statement:
--   Definitions and structural lemmas for Cell Open, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/CellOpen.lean

module
public import Definitions.Def_BornVolumeLean_Volume_CellMeasurePos
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup
open scoped ENNReal LinearAlgebra.Projectivization
namespace BornVolume
variable {M : ℕ}
end BornVolume


