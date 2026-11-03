-- Prove2me | Definitions.Def_levy_foundations_pointFamilyLaw
-- name    : levy_foundations_pointFamilyLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T23:10:28.908193+00:00
-- url     : https://prove2.me/theorems/12849112-c0da-4c24-8a18-ccd9953aa409
-- title:
--   Marginal laws for Poisson piece counts and independent marks
-- statement:
--   Each count coordinate follows a Poisson distribution with parameter equal to its piece intensity. Each mark coordinate follows the normalised law on that piece.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L210-L218. Coordinate probability laws. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Definitions.Def_levy_foundations_prmPiece
import Definitions.Def_levy_foundations_prmPieceLaw
import Definitions.Def_levy_foundations_pointFamilyIndex

open MeasureTheory ProbabilityTheory
namespace LevyFoundations
noncomputable def pointFamilyLaw {E : Type} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] [Nonempty E] :
    ∀ i, Measure (pointFamilyIndexType E i)
  | Sum.inl k => ((poissonMeasure (m (prmPiece m k)).toNNReal : Measure ℕ) :
      Measure (pointFamilyIndexType E (Sum.inl k)))
  | Sum.inr p => ((prmPieceLaw m p.1 : Measure E) :
      Measure (pointFamilyIndexType E (Sum.inr p)))
end LevyFoundations


