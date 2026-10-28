-- Prove2me | Definitions.Def_FeynmanKac_PathDiscount
-- name    : FeynmanKac_PathDiscount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-26T20:31:24.371619+00:00
-- url     : https://prove2.me/theorems/4bc1369f-5c96-43a3-9607-6b1792be103a
-- title:
--   Feynman–Kac pathwise exponential discount
-- statement:
--   Pathwise exponential discount along a real diffusion path.
-- source:
--   https://en.wikipedia.org/wiki/Feynman%E2%80%93Kac_formula

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable def FeynmanKac.pathDiscount {Ω : Type*}
    (X : ℝ → Ω → ℝ) (V : ℝ → ℝ → ℝ)
    (t s : ℝ) (ω : Ω) : ℝ :=
  Real.exp (-(∫ r in t..s, V (X r ω) r))


