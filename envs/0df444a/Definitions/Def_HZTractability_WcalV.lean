-- Prove2me | Definitions.Def_HZTractability_WcalV
-- name    : HZTractability_WcalV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:13:44.485127+00:00
-- url     : https://prove2.me/theorems/760388e7-0b54-4980-9865-375be29bb51d
-- title:
--   Local unapproved expenditure $\mathcal W_v$
-- statement:
--   Let $G_v$ be the union of the five groups at vertex $v$ of $M(G;a,\tau,K)$. The **local unapproved expenditure** is
--   $$
--   \mathcal W_v=\sum_i\sum_{j\in G_v:\,u_{ij}=0}p_jx_{ij},
--   $$
--   so $\sum_v\mathcal W_v\le\mathcal W$. The local price estimates of Appendix B assume $\mathcal W_u\le\zeta$ near $v$.
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), §4.5, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_HZTractability_Market

namespace HZTractability

/-- **Local unapproved expenditure** `𝒲_v` (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848,
held version, sha256 74b7bf9f…, §4.5, p.17 (PDF 19): "𝒲_v = ∑_i ∑_{j∈G_v : u_ij = 0} p_j x_ij",
where `G_v` is the union of the five groups at `v`).

The expenditure of all buyers of `M(G; a, τ, K)` on goods of the five groups at `v` that they value
at zero.

**Formalization Note** Script `𝒲_v` is distinct from the floor buyers' target expenditure `W_v`
(`floorTargetExp`). -/
noncomputable def WcalV {a τ : ℚ} {K : ℕ} {G : ThrGraph} (x : Buyer a τ K G → Good a τ K G → ℝ)
    (p : Good a τ K G → ℝ) (v : Fin G.n) : ℝ :=
  ∑ i, ∑ j, if (goodInfo j).map Prod.fst = some v ∧ mkt a τ K G i j = 0 then p j * x i j else 0

end HZTractability


