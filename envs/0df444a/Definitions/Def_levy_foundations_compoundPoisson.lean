-- Prove2me | Definitions.Def_levy_foundations_compoundPoisson
-- name    : levy_foundations_compoundPoisson
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:40:05.701316+00:00
-- url     : https://prove2.me/theorems/6c2fb5d2-3d2f-4365-9551-b107b01f0701
-- title:
--   Compound-Poisson-with-drift sample path
-- statement:
--   Compound-Poisson-with-drift sample path.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L270

import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_piecewisePath
namespace LevyFoundations
/-- Drift plus the marks arriving before the observation time. -/
noncomputable def compoundPoisson {Ω : Type*}
    (b : ℝ) (τ Y : ℕ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  piecewisePath 0 b (fun n => arrival τ n ω) (fun n => Y n ω) t
end LevyFoundations


