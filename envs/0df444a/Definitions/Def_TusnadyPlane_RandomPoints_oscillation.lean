-- Prove2me | Definitions.Def_TusnadyPlane_RandomPoints_oscillation
-- name    : TusnadyPlane_RandomPoints_oscillation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:27:11.084814+00:00
-- url     : https://prove2.me/theorems/96de52aa-d5bc-48e8-aaa2-e67b565f9fa9
-- title:
--   Half-open blocks, oscillation, and midpoint
-- statement:
--   Let $J=[\ell,u)$ be a nonempty interval and let $b\ge3$ be an integer. Its ordered blocks, indexed by $k=0,\ldots,b-1$, are
--   $$B_k=[\ell+k(u-\ell)/b,\ell+(k+1)(u-\ell)/b).$$
--   For a real function $f$ taking finitely many values on a nonempty set $B$, put
--   $$\operatorname{osc}_B f=\sup f(B)-\inf f(B),\qquad \operatorname{mid}_B f=\frac{\sup f(B)+\inf f(B)}2.$$
--   These are the source's maximum-minus-minimum and midpoint because the image is finite and nonempty. They supply the vertical comparison and potential. These total definitions are only used on such images; arbitrary empty or unbounded images are outside the extrema convention of the source.
-- source:
--   Zhewei Wei, Tight Bounds for Tusnády’s Problem in the Plane, STOC 2027 submission #313 (October 2026), printed p. 4–5 (PDF p. 5–6), §§2.1–2.2, (3)

import Mathlib

noncomputable section

namespace TusnadyPlane.RandomPoints

/-- Half-open interval and its b equal blocks, indexed from zero. §2.2. -/
def block (lo hi : ℝ) (b k : ℕ) : Set ℝ :=
  Set.Ico (lo + (k : ℝ) * (hi - lo) / b)
    (lo + ((k : ℝ) + 1) * (hi - lo) / b)

/-- Extrema are genuine on the nonempty finite images used below. (3). -/
def oscillation (B : Set ℝ) (f : ℝ → ℝ) : ℝ := sSup (f '' B) - sInf (f '' B)

def midpoint (B : Set ℝ) (f : ℝ → ℝ) : ℝ := (sSup (f '' B) + sInf (f '' B)) / 2

end TusnadyPlane.RandomPoints


