-- Prove2me | Definitions.Def_Helfgott_KernelPolynomialMoments
-- name    : Helfgott_KernelPolynomialMoments
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-06T02:02:23.019496+00:00
-- url     : https://prove2.me/theorems/4e9a5c21-2e10-4661-b752-78bd8160573b
-- title:
--   Complete polynomial mass and variation moments of the Goldbach logarithmic kernel
-- statement:
--   The compact logarithmic kernel used for the actual three-prime Goldbach smoothing satisfies the two explicit polynomial moment bounds
--   $$\int_0^2|t(2-t)^3|e^{t-1/2}\,dt\le\frac52,$$
--   $$\int_0^2|t(2-t)(16-26t-3t^2+7t^3+t^4)|e^{t-1/2}\,dt\le15.$$
--   These are the complete mass and second-derivative variation integrals underlying a quantitative Fourier bound for the actual major-arc smoothing kernel.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Exact antiderivative and complete rational polynomial bounds. Written by Codex.

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open MeasureTheory

namespace Helfgott
def KernelPolynomialMoments : Prop :=
  (∫ t in (0 : ℝ)..2,|t*(2-t)^3| * Real.exp (t-1/2))≤5/2 ∧
  (∫ t in (0 : ℝ)..2,|t*(2-t)*(16-26*t-3*t^2+7*t^3+t^4)| * Real.exp (t-1/2))≤15
end Helfgott


