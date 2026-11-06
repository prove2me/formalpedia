-- Prove2me | Definitions.Def_GradedReserve_interimUtility
-- name    : GradedReserve_interimUtility
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:51.859875+00:00
-- url     : https://prove2.me/theorems/6d5911bb-4e6e-4b13-8b1a-30d8dfd70732
-- title:
--   Interim utility $U(v)$
-- statement:
--   The interim utility of type $v$ against the symmetric strategy $\sigma$ is the best expected payoff it can obtain,
--   $$U(v)=\sup_{a}u(v,a).$$
--
--   **Formalization Note** The supremum is over all actions, for every $v$; it is at least $0$ (exit) and bounded. In a symmetric equilibrium it equals the equilibrium utility of almost every type.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 3.2, p.5 (PDF 6); Lemma 3.3, p.7 (PDF 8)

import Mathlib
import Definitions.Def_GradedReserve_payoff
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The interim utility `U(v)` of type `v` against the symmetric strategy `σ` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 3.2,
p.5, PDF 6; Lemma 3.3, p.7, PDF 8): the best payoff available to type `v`.

**Formalization Note.** Defined as the supremum of `payoff` over all actions, for every `v`; the
set of payoffs is bounded above for each `v` and contains `0` (exit). In a symmetric BNE it is
the equilibrium utility of almost every type. -/
noncomputable def interimUtility (f : ℝ → ℝ) (n : ℕ) (π : ℝ → ℝ) (σ : Kernel ℝ ℝ) (v : ℝ) : ℝ :=
  ⨆ a : ℝ, payoff f n π σ v a

end GradedReserve


