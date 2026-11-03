-- Prove2me | Definitions.Def_levy_foundations_isPoissonPointFamily
-- name    : levy_foundations_isPoissonPointFamily
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:10:25.977535+00:00
-- url     : https://prove2.me/theorems/428bf21f-f421-46f0-a4ac-3144444adb98
-- title:
--   Independent Poisson counts and marks on every finite-mass piece
-- statement:
--   A Poisson point family consists of measurable count variables and measurable marks, all mutually independent across one combined index, with Poisson counts of the correct mean and mark laws equal to normalised restrictions of the intensity.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L230-L247. Canonical point-family predicate. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPiece
import Definitions.Def_levy_foundations_prmPieceLaw
import Definitions.Def_levy_foundations_pointFamilyIndex

open MeasureTheory ProbabilityTheory
namespace LevyFoundations
structure IsPoissonPointFamily {Ω E : Type}
    [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (m : Measure E) [SigmaFinite m] [Nonempty E]
    (μ : Measure Ω) : Prop where
  measurable_count : ∀ k, Measurable (K k)
  measurable_point : ∀ k n, Measurable (X k n)
  indep : iIndepFun (pointFamilyCombined K X) μ
  law_count : ∀ k, HasLaw (K k)
    (poissonMeasure (m (prmPiece m k)).toNNReal) μ
  law_point : ∀ k n, HasLaw (X k n) (prmPieceLaw m k) μ
end LevyFoundations


