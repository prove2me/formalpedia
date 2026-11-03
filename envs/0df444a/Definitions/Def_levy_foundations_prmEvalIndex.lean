-- Prove2me | Definitions.Def_levy_foundations_prmEvalIndex
-- name    : levy_foundations_prmEvalIndex
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:07:16.730449+00:00
-- url     : https://prove2.me/theorems/c544e7b2-6685-4a42-9a96-88c189210ef7
-- title:
--   Measurable finite-intensity evaluation sets in a region
-- statement:
--   Define the measurable subsets B contained in a region R with finite intensity m(B). These index the count evaluations generating the local information σ-algebra.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently formulated Prove2Me draft; remote elaboration and proof pending. PoissonFiltration.lean lines 66–67.

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite

open MeasureTheory
namespace LevyFoundations
def prmEvalIndex {E : Type*} [MeasurableSpace E]
    (m : Measure E) (R : Set E) : Type _ :=
  {B : Set E // MeasurableSet B ∧ B ⊆ R ∧ m B < ⊤}
end LevyFoundations


