-- Prove2me | Definitions.Def_BornVolumeLean_MeasureTheory_PiCurry
-- name    : BornVolumeLean_MeasureTheory_PiCurry
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:51:12.2672+00:00
-- url     : https://prove2.me/theorems/13058248-bf67-4495-9d9a-132f8fd038cd
-- title:
--   Pi Curry
-- statement:
--   Definitions and structural lemmas for Pi Curry, from zblore's pinned Born weights as Fubini–Study volumes development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/MeasureTheory/PiCurry.lean

module
public import Mathlib.MeasureTheory.Constructions.Pi
set_option autoImplicit false
@[expose] public section
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace MeasureTheory
variable {ιp κp : Type*} [Fintype ιp] [Fintype κp] {α : ιp × κp → Type*}
  [∀ p, MeasurableSpace (α p)] (ν : (p : ιp × κp) → Measure (α p)) [∀ p, SigmaFinite (ν p)]
end MeasureTheory


