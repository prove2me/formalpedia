-- Prove2me | Definitions.Def_GradedReserve_revAnc
-- name    : GradedReserve_revAnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:42.777473+00:00
-- url     : https://prove2.me/theorems/422b3558-9a36-4ac3-b2b3-2c8f581c37c6
-- title:
--   Anchored revenue $\mathrm{Rev}_{\mathrm{anc}}(G_\pi)$
-- statement:
--   An **anchored** bidder bids its value, $X_i=V_i$. The anchored revenue $\mathrm{Rev}_{\mathrm{anc}}(G_\pi)$ is the expected revenue of $G_\pi$ when every bidder is anchored. It equals
--   $$\mathrm{Rev}_{\mathrm{anc}}(G_\pi)=\mathbb E\big[V_{(1)}\,\pi(V_{(1)})\big],$$
--   where $V_{(1)}$ is the highest value.
--
--   **Formalization Note** Defined as the revenue of the truthful profile $\sigma(v)=\delta_v$; it does not depend on any equilibrium.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, pp.4–5 (PDF 5–6)

import Mathlib
import Definitions.Def_GradedReserve_revRat
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The anchored revenue `Rev_anc(G_π)` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, pp.4–5, PDF 5–6): the expected revenue of
`G_π` when every bidder is anchored and bids its value, `X_i = V_i`; it equals
`E[V₍₁₎ π(V₍₁₎)]` (p.5).

**Formalization Note.** Defined as `revRat` of the truthful profile `σ v = δ_v`; it involves no
equilibrium. -/
noncomputable def revAnc (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) : ℝ :=
  revRat f n π (Kernel.deterministic id measurable_id)

end GradedReserve


