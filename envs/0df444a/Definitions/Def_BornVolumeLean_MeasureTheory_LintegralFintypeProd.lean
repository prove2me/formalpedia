-- Prove2me | Definitions.Def_BornVolumeLean_MeasureTheory_LintegralFintypeProd
-- name    : BornVolumeLean_MeasureTheory_LintegralFintypeProd
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:11.213474+00:00
-- url     : https://prove2.me/theorems/d9baeed8-52c9-474c-8156-d7624c421f66
-- title:
--   Lintegral Fintype Prod
-- statement:
--   Definitions and structural lemmas for Lintegral Fintype Prod, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/LintegralFintypeProd.lean

module
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace MeasureTheory
variable {ι : Type*} [Fintype ι]
end MeasureTheory


