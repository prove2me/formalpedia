-- Prove2me | Definitions.Def_AdBlocking_Surplus_TZero
-- name    : AdBlocking_Surplus_TZero
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:15.287739+00:00
-- url     : https://prove2.me/theorems/142abbe4-95aa-416b-a053-9268c4d5d572
-- title:
--   Closed forms at t = 0: F(r,0), C_Δ(r,0) and G(r,0)
-- statement:
--   Three explicit functions of the ad-sensitivity lower bound $r\in(0,1]$ that the paper evaluates at quality-sensitivity lower bound $t=0$.
--
--   1. Branch i) of (7), the adblocker's optimal ad limit per unit of quality:
--   $$F_0(r)=\frac{1+r}{1+r+r^2}-\frac{\sqrt{1+5r+9r^2+5r^3+r^4}}{\sqrt3\,(1+r)(1+r+r^2)}.$$
--   2. The additional-surplus coefficient from the proof of Proposition 3:
--   $$C_\Delta(r,0)=\frac{\bigl(2(r+1)-F_0(r)(1+r^2)\bigr)\bigl(1-F_0(r)(1+r)\bigr)^2}{24(1+r)}.$$
--   3. The first branch of (10), the coefficient by which the adblocker's presence lowers optimal quality:
--   $$G(r,0)=\frac{2(r^2+4r+1)\bigl(1-(1+r)F_0(r)\bigr)}{3(1+r)^2}.$$
--
--   These are plain real functions; their meaning in the model (optimal limit, surplus decomposition, profit) is asserted by the theorem that uses them.
--
--   **Formalization Note** The page writes $F(r,t)$ inside $C_\Delta(r,0)$; at $t=0$ it means $F(r,0)$, which is branch i) of (7) for every $r\in(0,1]$ (the branch condition $0\le t\le r\cdot(\dots)$ has a positive right side).
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 42 (PDF 43), equation (7) branch i); p. 43 (PDF 44), equation (10) first branch; p. 44 (PDF 45), C_Δ(r,0) display

import Mathlib

namespace AdBlocking.Surplus

/-- Branch i) of (7) at `t = 0`: the adblocker's optimal limit per unit of quality. -/
noncomputable def F0 (r : ℝ) : ℝ :=
  (1 + r) / (1 + r + r ^ 2) -
    Real.sqrt (1 + 5 * r + 9 * r ^ 2 + 5 * r ^ 3 + r ^ 4) /
      (Real.sqrt 3 * (1 + r) * (1 + r + r ^ 2))

/-- The additional-surplus coefficient `C_Δ(r, 0)` from the proof of Proposition 3. -/
noncomputable def CDelta0 (r : ℝ) : ℝ :=
  (2 * (r + 1) - F0 r * (1 + r ^ 2)) * (1 - F0 r * (1 + r)) ^ 2 / (24 * (1 + r))

/-- The first branch of (10) at `t = 0`: the quality-reduction coefficient `G(r, 0)`. -/
noncomputable def G0 (r : ℝ) : ℝ :=
  2 * (r ^ 2 + 4 * r + 1) * (1 - (1 + r) * F0 r) / (3 * (1 + r) ^ 2)

end AdBlocking.Surplus


