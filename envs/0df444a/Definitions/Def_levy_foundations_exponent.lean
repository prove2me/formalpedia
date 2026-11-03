-- Prove2me | Definitions.Def_levy_foundations_exponent
-- name    : levy_foundations_exponent
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T10:30:49.792195+00:00
-- url     : https://prove2.me/theorems/01c6ccf0-07f4-40bd-a5fc-dfd1abb36cbb
-- title:
--   Lévy–Khintchine characteristic exponent
-- statement:
--   The characteristic exponent combines the imaginary linear drift term, the negative quadratic Gaussian term and the compensated jump integral.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchineProof.lean#L5183-L5191. Central analytic exponent associated with a triple. The Prove2Me statement and namespace are independently authored and require verification.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_compensatedIntegrand

open MeasureTheory
namespace LevyFoundations
noncomputable def exponent (T : LevyKhintchineTriple) (ξ : ℝ) : ℂ :=
  ↑T.drift * ↑ξ * Complex.I
    - ↑(T.gaussianVariance : ℝ) * ↑ξ ^ 2 / 2
    + ∫ x, compensatedIntegrand ξ x ∂T.levyMeasure
end LevyFoundations


