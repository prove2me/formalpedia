-- Prove2me | Definitions.Def_levy_foundations_jumpCount
-- name    : levy_foundations_jumpCount
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:36:54.245023+00:00
-- url     : https://prove2.me/theorems/747d3999-49cb-4f51-8127-89cbca963c38
-- title:
--   Count jump times no later than the observation time
-- statement:
--   Count jump times no later than the observation time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PiecewisePath.lean#L64

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Lattice.Nat
namespace LevyFoundations
/-- The least index of an arrival strictly after t. -/
noncomputable def jumpCount (T : ℕ → ℝ) (t : ℝ) : ℕ :=
  sInf {n | t < T n}
end LevyFoundations


