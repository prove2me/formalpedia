-- Prove2me | Definitions.Def_SampleCRS_AlmostGreedy_h
-- name    : SampleCRS_AlmostGreedy_h
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:40.666097+00:00
-- url     : https://prove2.me/theorems/063c9163-3429-4530-8ea0-f06e138af6c2
-- title:
--   The auxiliary acceptance function h
-- statement:
--   For an integer capacity $k\ge1$ and count $s\ge0$, use the published acceptance-rate function $\mathrm{AR}_k(s)=\min\{1,k/(s+1)\}$ and define
--   $$h_k(s)=\frac{(k+1)\mathrm{AR}_k(s)+\min\{k,s\}}{2k+1}.$$
--
--   This is the function in the exact acceptance identity (5) and the Bernoulli-to-Poisson comparison. Counts and capacities are natural numbers, the arithmetic is real, and the displayed minimum is literal. For positive $k$, $0\le h_k(s)\le1$; its Poisson expectation is consequently a convergent series.
-- source:
--   Shaddin Dughmi, Vasilis Livanos, Pranav Nuti, STOC 2027 submission #686 (October 2026), §4.1, p.16 definition preceding (5)

import Mathlib
import Definitions.Def_StaticProphetSec_AR

namespace SampleCRS.AlmostGreedy

/-- The auxiliary h from §4.1, p.16. Literal min{k,s} avoids a normalization convention. -/
noncomputable def h (k s : ℕ) : ℝ :=
  (((k : ℝ) + 1) * StaticProphetSec.AR k s + min (k : ℝ) (s : ℝ)) /
    (2 * (k : ℝ) + 1)

end SampleCRS.AlmostGreedy


