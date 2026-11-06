-- Prove2me | Definitions.Def_OmniMix_FinDist
-- name    : OmniMix_FinDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:21.331192+00:00
-- url     : https://prove2.me/theorems/1db42a25-0325-4a38-b1d5-49bc98aa1074
-- title:
--   Finitely supported forecast distribution
-- statement:
--   A **forecast distribution** is a finitely supported probability distribution $D$ on $[0,1]$: finitely many points $p$ with weights $D(p)>0$ summing to $1$.
--
--   **Formalization Note** The paper allows any distribution over $[0,1]$. Restricting forecasts to finite support only restricts the forecaster, so existence statements over these distributions are at least as strong; Lemma 2.2 produces distributions with at most three support points.
-- source:
--   Liu–Luo–Ratliff, Omniprediction for All Mixable Proper Losses and Beyond, arXiv:2610.41023, §1, p.1

import Mathlib

namespace OmniMix

/-- **Finitely supported forecast distribution on `[0,1]`.** Liu–Luo–Ratliff, *Omniprediction for All Mixable Proper Losses and Beyond*, arXiv:2610.41023, §1, p.1: "we let `D_t` be the
distribution over `[0, 1]` from which `P_t` is drawn".

A `FinDist` is a finitely supported weight function `wt` on `[0,1]` with nonnegative weights summing
to `1`; its support is `wt.support` (the points of positive weight).

**Formalization Note.** Forecasts are restricted to finitely supported distributions. This only
restricts the forecaster, so existence statements over `FinDist` are at least as strong as over all
distributions; Lemma 2.2 (p.10) produces distributions with at most three support points. -/
structure FinDist where
  /-- the weight of each point -/
  wt : unitInterval →₀ ℝ
  /-- weights are nonnegative -/
  nonneg : ∀ p, 0 ≤ wt p
  /-- weights sum to one -/
  sum_one : (wt.sum fun _ a => a) = 1

end OmniMix


