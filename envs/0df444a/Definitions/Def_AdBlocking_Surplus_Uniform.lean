-- Prove2me | Definitions.Def_AdBlocking_Surplus_Uniform
-- name    : AdBlocking_Surplus_Uniform
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:14.18296+00:00
-- url     : https://prove2.me/theorems/6d3a5d63-f0cc-452d-af39-9a17fc0f4e9b
-- title:
--   Uniform law on an interval, including a point interval
-- statement:
--   For real endpoints $a\le b$, let $U[a,b]$ be normalized Lebesgue measure on $[a,b]$ if $a<b$, and the point mass at $b$ if $a=b$.
--
--   $$U[a,b]=\begin{cases}\mathrm{Leb}|_{[a,b]}/(b-a),&a<b,\\ \delta_b,&a=b.\end{cases}$$
--
--   This law represents each independent consumer characteristic, including the cases where all consumers have the same quality or advertising sensitivity.
--
--   **Formalization Note** Outside the source's domain $a\le b$, the definition returns the point mass at $b$; every use in this mission has ordered endpoints.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 11 (PDF 12), §3 consumer distributions

import Mathlib

open MeasureTheory

namespace AdBlocking.Surplus

/-- The uniform probability law on a real interval, including a point interval. -/
noncomputable def unifIcc (a b : ℝ) : Measure ℝ :=
  if a < b then (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Set.Icc a b)
  else Measure.dirac b

end AdBlocking.Surplus


