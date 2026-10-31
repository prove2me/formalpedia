-- Prove2me | Definitions.Def_SharedControl_rbar
-- name    : SharedControl_rbar
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:05:51.421677+00:00
-- url     : https://prove2.me/theorems/cc18f5f0-f6a0-4588-a290-8bb86171f45f
-- title:
--   The mean redistribution $\bar r = E[r]$
-- statement:
--   The **mean redistribution** is
--
--   $$
--   \bar r \;=\; E[r] \;=\; \int_\Omega r \, dP .
--   $$
--
--   The quantity $\bar r - r_l$, the expected uncertain part of the redistribution, decides in Proposition 1 whether good proposals are always approved under shared control.
--
--   **Formalization Note** Under the standing assumptions $r$ is almost surely in $[r_l, r_h]$, hence integrable, so the Bochner integral is the true mean.
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §2.1, p.4

import Mathlib
import Definitions.Def_SharedControl_Model

open MeasureTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §2.1, p.4 (PDF p.5): "let ¯r denote the mean of r".

**Formalization Note.** `r̄ = ∫ r dP` (Bochner integral). Under `SharedControl.Standing`, `r` is
almost surely in `[rl, rh]`, hence integrable, so this is the true mean. -/
noncomputable def rbar {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) : ℝ :=
  ∫ ω, M.r ω ∂M.P

end SharedControl


