-- Prove2me | Definitions.Def_levy_foundations_levyKhintchineTriple
-- name    : levy_foundations_levyKhintchineTriple
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-27T07:57:27.414193+00:00
-- url     : https://prove2.me/theorems/841233a5-604f-49b4-8f68-d62869cffb61
-- title:
--   Drift, Gaussian variance and Lévy jump measure
-- statement:
--   A Lévy–Khintchine triple consists of real drift, nonnegative Gaussian variance and a Lévy measure satisfying the integrability and no-atom-at-zero conditions.
-- source:
--   Inspired by Shmuel Link, LeanLevy v0.2.0 (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/LevyKhintchine.lean#L42-L52. The core parameter structure. The Prove2Me statement and namespace are independently authored and require verification.

import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory
open scoped NNReal
namespace LevyFoundations
structure LevyKhintchineTriple where
  drift : ℝ
  gaussianVariance : ℝ≥0
  levyMeasure : Measure ℝ
  levyMeasure_condition : isLevyMeasure levyMeasure
end LevyFoundations


