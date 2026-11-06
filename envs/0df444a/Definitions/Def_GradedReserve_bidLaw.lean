-- Prove2me | Definitions.Def_GradedReserve_bidLaw
-- name    : GradedReserve_bidLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:29:39.534278+00:00
-- url     : https://prove2.me/theorems/b46b48b4-01ca-4e93-8032-1413f9a897df
-- title:
--   Law of an opponent's action under a symmetric strategy
-- statement:
--   Let every bidder use the same mixed strategy $\sigma$, which assigns to each value $v$ a probability distribution $\sigma(v)$ over actions. The law of one opponent's action is the mixture
--   $$\mu_\sigma=\int\sigma(v)\,dF(v).$$
--
--   **Formalization Note** A mixed strategy is a Markov kernel from values to actions in $\mathbb R$. Actions in $[0,1]$ are bids; every negative action stands for the exit action (stay out, never win, pay nothing). Actions above $1$ are excluded in the equilibrium definition.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- The law of one opponent's action in a symmetric strategy profile `σ` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4,
PDF 5): the value is drawn from `typeMeasure f` and the action from the mixed strategy `σ v`.

**Formalization Note.** A symmetric mixed strategy is a Markov kernel `σ` from values to actions
in `ℝ`. Actions in `[0, 1]` are bids; every negative action is the exit action ("every bidder may
stay out and pay nothing", p.4), which never wins and pays nothing. Actions above `1` are
excluded in `IsSymBNE`. -/
noncomputable def bidLaw (f : ℝ → ℝ) (σ : Kernel ℝ ℝ) : Measure ℝ := (typeMeasure f).bind σ

end GradedReserve


