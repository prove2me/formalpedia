-- Prove2me | Definitions.Def_AdBlocking_Surplus_ClosedForms
-- name    : AdBlocking_Surplus_ClosedForms
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:20:17.060355+00:00
-- url     : https://prove2.me/theorems/0ae01573-883c-42ff-bb6d-e6b3e275631c
-- title:
--   Benchmark and adblocker quality formulas
-- statement:
--   The benchmark's optimal ad volume $A^*(q)$ and quality $q^*_{NA}$ have two branches separated by $t=r/(1+r)$. For a positive coefficient $G(r,t)$ and download-cost support $\bar\kappa$, the adblocker-world candidate quality is
--
--   $$q^*_{AB}=\begin{cases}\left(4c(1+r)(1-t)/p_a+G(r,t)/\bar\kappa\right)^{-1},&t\le r/(1+r),\\ \left(4c/[p_a(1-r(1-t)+t)]+G(r,t)/\bar\kappa\right)^{-1},&t>r/(1+r).\end{cases}$$
--
--   These functions name the quantities characterized by Lemma 1 and Proposition 2; the definitions alone assert no optimality.
--
--   **Formalization Note** The first branch is chosen at the common boundary. Positivity assumptions needed for the quotients are imposed in the theorems that use these functions.
-- source:
--   Gritckevich, Katona & Sarvary, Ad Blocking, SSRN 3100524 (version of March 7, 2021), p. 14 (PDF 15), equation (2) and Lemma 1; p. 18 (PDF 19), Proposition 2

import Mathlib

namespace AdBlocking.Surplus

noncomputable def benchAdStar (r t q : ℝ) : ℝ :=
  if t ≤ r / (1 + r) then q / (1 + r)
  else q * (1 - r * (1 - t))

noncomputable def benchQualityStar (pa c r t : ℝ) : ℝ :=
  if t ≤ r / (1 + r) then pa / (4 * c * (1 + r) * (1 - t))
  else pa * (1 - r * (1 - t) + t) / (4 * c)

noncomputable def benchEqAdStar (pa c r t : ℝ) : ℝ :=
  benchAdStar r t (benchQualityStar pa c r t)

noncomputable def abQualityStar (pa c r t κbar G : ℝ) : ℝ :=
  if t ≤ r / (1 + r) then
    (4 * c * (1 + r) * (1 - t) / pa + G / κbar)⁻¹
  else
    (4 * c / (pa * (1 - r * (1 - t) + t)) + G / κbar)⁻¹

end AdBlocking.Surplus


