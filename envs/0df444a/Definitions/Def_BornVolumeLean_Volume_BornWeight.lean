-- Prove2me | Definitions.Def_BornVolumeLean_Volume_BornWeight
-- name    : BornVolumeLean_Volume_BornWeight
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:05:44.394632+00:00
-- url     : https://prove2.me/theorems/9d1098d2-7046-43c0-9015-396fdd85dee7
-- title:
--   Born Weight
-- statement:
--   Definitions and structural lemmas for Born Weight, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/Volume/BornWeight.lean

module
public import Definitions.Def_BornVolumeLean_Volume_MomentDirichletN
public import Definitions.Def_BornVolumeLean_Volume_CellMeasure
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Set Matrix Matrix.UnitaryGroup Projectivization
open scoped ENNReal
namespace BornVolume
variable {M : ℕ}
end BornVolume


