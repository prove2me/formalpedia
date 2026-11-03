-- Prove2me | Definitions.Def_levy_foundations_prmEvalPiSystem
-- name    : levy_foundations_prmEvalPiSystem
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:14:36.460409+00:00
-- url     : https://prove2.me/theorems/cf5cde40-6e15-4847-8d65-df9d3c8f9e3b
-- title:
--   Generating pi-system of regional Poisson count events
-- statement:
--   A π-system of finite intersections of preimages of measurable count events for all finite-intensity measurable subsets of a region R.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), commit 7e73fd9b23ad52956ec2756a815889a783131ce4. Independently authored Prove2Me draft pending remote Lean verification. RandomMeasure/PoissonFiltration.lean, definition prmEvalPiSystem.

import Mathlib.MeasureTheory.PiSystem
import Definitions.Def_levy_foundations_prmEvalIndex
import Definitions.Def_levy_foundations_poissonRandomMeasure

open MeasureTheory
namespace LevyFoundations
def prmEvalPiSystem {Ω E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) (R : Set E) : Set (Set Ω) :=
  piiUnionInter (fun B : prmEvalIndex m R =>
    {A | MeasurableSet[MeasurableSpace.comap
      (fun ω => poissonRandomMeasure K X ω B.1) inferInstance] A}) Set.univ
end LevyFoundations


