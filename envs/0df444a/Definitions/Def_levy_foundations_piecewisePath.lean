-- Prove2me | Definitions.Def_levy_foundations_piecewisePath
-- name    : levy_foundations_piecewisePath
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:37:12.100985+00:00
-- url     : https://prove2.me/theorems/c34d7ab4-eabd-416b-b2c7-552d4de92938
-- title:
--   A real affine-drift path with finitely many jumps before each observation time
-- statement:
--   A real affine-drift path with finitely many jumps before each observation time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean#L120

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_levy_foundations_jumpCount
namespace LevyFoundations
/-- Affine drift plus the marks at all elapsed arrival indices. -/
noncomputable def piecewisePath (x₀ b : ℝ) (T Y : ℕ → ℝ) (t : ℝ) : ℝ :=
  x₀ + b * t + ∑ n ∈ Finset.range (jumpCount T t), Y n
end LevyFoundations


