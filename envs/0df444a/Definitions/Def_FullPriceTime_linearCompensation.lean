-- Prove2me | Definitions.Def_FullPriceTime_linearCompensation
-- name    : FullPriceTime_linearCompensation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:46:07.845083+00:00
-- url     : https://prove2.me/theorems/24bbc46b-958e-4b6e-b2f2-0383564847e1
-- title:
--   Linear compensation $\Pi_\theta(t_w)=\theta t_w$ (gig workers), eq. (1)
-- statement:
--   The **linear compensation structure** pays a constant wage $\theta$ per unit of working time:
--   $$\Pi_\theta(t_w)=\theta\,t_w .$$
--   It models gig workers, who can freely choose how long to work. It is the compensation function under which Proposition 1 is stated.
-- source:
--   Li, Lariviere, Bassamboo, Is Full Price the Full Story When Consumers Have Time and Budget Constraints?, SSRN 4223388, §3.1, eq. (1), pp.7–8

import Mathlib

namespace FullPriceTime

/-- **The linear compensation structure (1): `Π_θ(t_w) = θ t_w`.**
Li, Lariviere, Bassamboo, *Is Full Price the Full Story When Consumers Have Time and Budget
Constraints?*, SSRN 4223388, §3.1, eq. (1), pp.7–8 (PDF pp.7–8): "Πθ(tw) = θtw, where θ is the
wage per time unit and tw is the number of time units the consumer chooses to work."

This models gig workers, who are paid a constant wage `θ` per unit of time and choose freely how
long to work. -/
def linearCompensation (θ : ℝ) : ℝ → ℝ := fun tw => θ * tw

end FullPriceTime


