-- Prove2me | Definitions.Def_levy_foundations_compensatedPieceSum
-- name    : levy_foundations_compensatedPieceSum
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T10:31:36.963263+00:00
-- url     : https://prove2.me/theorems/763cbe29-0c5c-4653-981e-a2879b52cc2f
-- title:
--   Centred finite Poisson sum on one intensity piece
-- statement:
--   The compensated random sum in piece k is the realised point sum less its intensity integral.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/PoissonCompensated.lean#L72-L75. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_levy_foundations_prmPiece
import Definitions.Def_levy_foundations_pieceSum

open MeasureTheory
namespace LevyFoundations
/-- Subtract the deterministic intensity integral from the random finite sum. -/
noncomputable def compensatedPieceSum {Ω E : Type}
    [MeasurableSpace E] (m : Measure E) [SigmaFinite m]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (f : E → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  pieceSum K X f k ω - ∫ x in prmPiece m k, f x ∂m
end LevyFoundations


