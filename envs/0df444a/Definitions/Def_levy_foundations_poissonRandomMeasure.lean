-- Prove2me | Definitions.Def_levy_foundations_poissonRandomMeasure
-- name    : levy_foundations_poissonRandomMeasure
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T22:55:51.027294+00:00
-- url     : https://prove2.me/theorems/ca4f5045-3306-4f29-90a0-50fac1e08207
-- title:
--   Random counting measure from a countable point family
-- statement:
--   Given counts K(k) and marks X(k,n) for each countable piece k, place a unit Dirac mass at every mark with index n below K(k). Summing across marks and pieces defines a measure-valued random object.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonRandomMeasure.lean#L68-L70. Point-family construction of the counting measure. Independently authored Prove2Me draft pending statement audit and remote compilation.

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Dirac

open MeasureTheory
namespace LevyFoundations
noncomputable def poissonRandomMeasure {Ω E : Type*} [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E) (ω : Ω) : Measure E :=
  Measure.sum fun k => Measure.sum fun n =>
    if n < K k ω then Measure.dirac (X k n ω) else 0
end LevyFoundations


