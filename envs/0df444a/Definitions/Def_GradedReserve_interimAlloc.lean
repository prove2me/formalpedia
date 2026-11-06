-- Prove2me | Definitions.Def_GradedReserve_interimAlloc
-- name    : GradedReserve_interimAlloc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:32:30.626514+00:00
-- url     : https://prove2.me/theorems/0cd1320d-65a9-491c-a128-21de24c6d058
-- title:
--   Interim allocation $q(v)$
-- statement:
--   The interim allocation of type $v$ under the symmetric strategy $\sigma$ is its probability of receiving the item,
--   $$q(v)=\int W(a)\,\mathbf 1\{a\in[0,1]\}\,\sigma(v)(da).$$
--   In a pure equilibrium with bid $\beta$ this is $Q(v)\,\pi(\beta(v))$.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 3.2, p.5 (PDF 6); Lemma 3.3, p.7 (PDF 8)

import Mathlib
import Definitions.Def_GradedReserve_winProb
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The interim allocation `q(v)` of type `v` under the symmetric strategy `σ`: the probability that
type `v` receives the item (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 3.2, p.5, PDF 6, "type v wins with probability
Q(v)s(v)"; Lemma 3.3, p.7, PDF 8). -/
noncomputable def interimAlloc (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) (v : ℝ) : ℝ :=
  ∫ a, (if a ∈ Icc (0:ℝ) 1 then winProb f n π σ a else 0) ∂(σ v)

end GradedReserve


