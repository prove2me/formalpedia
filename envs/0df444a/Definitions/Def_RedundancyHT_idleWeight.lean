-- Prove2me | Definitions.Def_RedundancyHT_idleWeight
-- name    : RedundancyHT_idleWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:27:44.324145+00:00
-- url     : https://prove2.me/theorems/6f93c18f-61b4-46a6-be17-04cbe9b41967
-- title:
--   The idle-server weight $\prod_l\mu_{u_l}/\lambda_{\mathcal C(u_1,\dots,u_l)}$ of (5)
-- statement:
--   For a sequence $u=(u_1,\dots,u_L)$ of idle servers, $u_1$ having been idle longest,
--   $$\prod_{l=1}^{L}\frac{\mu_{u_l}}{\lambda_{\mathcal C(u_1,\dots,u_l)}}.$$
--   The empty sequence has weight one.
-- source:
--   Cardinaels, Borst & van Leeuwaarden, Heavy-Traffic Universality of Redundancy Systems with Assignment Constraints, arXiv:2005.14566v5, display (5), p.8

import Definitions.Def_RedundancyHT_lamC

set_option autoImplicit false

open MeasureTheory Filter Topology BipartiteMatchingHT.Delay
open scoped BigOperators ENNReal BoundedContinuousFunction

noncomputable section

namespace RedundancyHT

/-- **The second product of (5)**: `∏_{l=1}^{L} µ_{u_l} / λ_{𝒞(u₁,…,u_l)}` for `u = (u₁,…,u_L)`, with
`u₁` the longest idle server (arXiv:2005.14566v5, p.8). -/
def idleWeight {n m : ℕ} (D : Model n m) (lam : ℝ) (u : List (Fin m)) : ℝ :=
  ∏ l : Fin u.length, D.service (u.get l) / lamC D lam (u.take (l.val + 1)).toFinset

end RedundancyHT


