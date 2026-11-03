-- Prove2me | Definitions.Def_levy_foundations_prmPieceLaw
-- name    : levy_foundations_prmPieceLaw
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T22:52:21.871345+00:00
-- url     : https://prove2.me/theorems/0011bdf9-470c-4be7-b137-67c7a5b624ba
-- title:
--   Normalised point law on a sigma-finite partition piece
-- statement:
--   On a positive-mass piece, take the restricted intensity and normalise it to unit mass. On a zero-mass piece, use an arbitrary Dirac probability law; that piece later has Poisson count zero.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonPointFamily.lean#L105-L110. Normalised piece law and zero-mass convention. Independently authored Prove2Me draft; statement and imports require remote compiler verification.

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Mathlib.Order.Disjointed
import Mathlib.MeasureTheory.Measure.Dirac
import Definitions.Def_levy_foundations_prmPiece

open MeasureTheory
namespace LevyFoundations
noncomputable def prmPieceLaw {E : Type*} [MeasurableSpace E]
    (m : Measure E) [SigmaFinite m] [Nonempty E] (k : ℕ) : Measure E :=
  if m (prmPiece m k) = 0 then Measure.dirac (Classical.arbitrary E)
  else (m (prmPiece m k))⁻¹ • m.restrict (prmPiece m k)
end LevyFoundations


