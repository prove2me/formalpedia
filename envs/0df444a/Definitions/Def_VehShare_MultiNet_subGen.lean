-- Prove2me | Definitions.Def_VehShare_MultiNet_subGen
-- name    : VehShare_MultiNet_subGen
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:33:40.561033+00:00
-- url     : https://prove2.me/theorems/27ad6c89-9ecd-4ec8-97e2-4fae72fbf46e
-- title:
--   Sub-generator $T$ of a phase-type travel time
-- statement:
--   For the pair $(i,j)$, the **sub-generator** of its travel-time law is the matrix $T$ indexed by the stages with
--
--   $$
--   T_{ss'}=r_{ij}(s,s')\quad(s\neq s'),\qquad T_{ss}=-\Big(e_{ij}(s)+\sum_{s'\neq s}r_{ij}(s,s')\Big).
--   $$
--
--   It is the generator of the stage process restricted to the transient stages; the trip ends when the process leaves at an exit rate.
-- source:
--   Benjaafar, Shen, Pricing in On-Demand (and One-Way) Vehicle Sharing Networks, SSRN 3998297 (version of 2023-01-10), https://ssrn.com/abstract=3998297, p. 4 (unnumbered)

import Mathlib
import Definitions.Def_VehShare_MultiNet_Instance

namespace VehShare.MultiNet

/-- **Sub-generator of the travel-time law of `i → j`.**
Benjaafar, Shen, *Pricing in On-Demand (and One-Way) Vehicle Sharing Networks*, SSRN 3998297
(version of 2023-01-10), p. 4 (unnumbered: "a network of stages (or phases) each exponentially distributed").

`T s s' = r i j s s'` for `s ≠ s'` and `T s s = −(e i j s + ∑_{s' ≠ s} r i j s s')`: the generator of
the stage process restricted to the transient stages. -/
def subGen (P : Instance) (i j : P.L) : Matrix (P.Ph i j) (P.Ph i j) ℝ :=
  Matrix.of fun s s' =>
    if s = s' then -(P.e i j s + ∑ s'' ∈ Finset.univ.erase s, P.r i j s s'') else P.r i j s s'

end VehShare.MultiNet


