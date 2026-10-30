-- Prove2me | Definitions.Def_RideHailingAV_PureHV_util
-- name    : RideHailingAV_PureHV_util
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:54:29.291113+00:00
-- url     : https://prove2.me/theorems/27545b75-58e4-41ed-81a6-59e6e958b05e
-- title:
--   Maximum on-trip utilization $\bar u(d)=d t_2/\underline n(d)$
-- statement:
--   When the demand rate $d$ is served with the minimal fleet $\underline n(d)$, the fraction of fleet time spent on trips is
--   $$\bar u(d)=\frac{d\,t_2}{\underline n(d)}.$$
--   This is the maximum utilization of the fleet at demand $d$ (Lemma 1, Item 3), and the equilibrium utilization rate is $u^*_{HV,i}=\bar u(d^*_{HV,i})$ (eq. (16)).
--
--   **Formalization Note** Lean's division gives $\bar u(0)=0/0=0$, which is the paper's $\bar u(0)=0$. The mission uses $\bar u$ at $d>0$.
-- source:
--   Lian, van Ryzin, Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of Market Configuration, SSRN 3716491 (version of 23 August 2023), Lemma 1, Item 3, eq. (22), p. 38; eq. (16), p. 14

import Mathlib
import Definitions.Def_RideHailingAV_PureHV_Market
import Definitions.Def_RideHailingAV_PureHV_minSupply

namespace RideHailingAV.PureHV

/-- **Maximum on-trip utilization `ū(d)`.** Lian, van Ryzin, *Capturing the Benefits of Autonomous Vehicles in Ride-Hailing: The Role of
Market Configuration*, SSRN 3716491 (version of 23 August 2023), Lemma 1, Item 3, eq. (22), p. 38 and
eq. (16), p. 14: `ū(d) = d t₂ / n(d)`.

**Formalization Note.** Lean's division gives `util M 0 = 0 / 0 = 0`, the paper's `ū(0) = 0`
(Lemma 2, p. 39). The mission uses `util` at `d > 0`. -/
noncomputable def util (M : Market) (d : ℝ) : ℝ :=
  d * M.t2 / minSupply M d

end RideHailingAV.PureHV


