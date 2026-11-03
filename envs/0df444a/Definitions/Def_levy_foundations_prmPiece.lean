-- Prove2me | Definitions.Def_levy_foundations_prmPiece
-- name    : levy_foundations_prmPiece
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T21:22:20.406752+00:00
-- url     : https://prove2.me/theorems/ee322e5a-fc06-4a1b-bba5-1228caa0c0a5
-- title:
--   Finite-mass partition piece of a sigma-finite measure
-- statement:
--   Define the k-th measurable, pairwise-disjoint piece of the standard countable finite-mass partition of a sigma-finite measure by disjointing its spanning sets.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L102-L103. Countable sigma-finite partition. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed

open MeasureTheory Set
namespace LevyFoundations
noncomputable def prmPiece {E : Type*} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] (k : ℕ) : Set E :=
  disjointed (spanningSets m) k
end LevyFoundations


