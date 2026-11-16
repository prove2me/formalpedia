-- Prove2me | Definitions.Def_GradedReserve_Supplement_profileLaw
-- name    : GradedReserve_Supplement_profileLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:35:29.523969+00:00
-- url     : https://prove2.me/theorems/4a93e80a-b007-48c3-a9f3-df7204bf9d36
-- title:
--   Law of the action profile under independent mixed strategies
-- statement:
--   When bidder $j$ uses the mixed strategy $\sigma_j$ (a Markov kernel from values to actions), values are i.i.d. with density $f$ on $[0,1]$ and randomizations are independent across bidders, the action profile has the product law
--   $$\mathcal L(\sigma)=\bigotimes_{j=1}^n\mathcal L_j,\qquad \mathcal L_j(A)=\int_0^1\sigma_j(v)(A)\,f(v)\,dv,$$
--   the product of the bidders' action laws. Strategies may differ across bidders.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.4, p.7 (PDF 8); Section B conventions, pp.25–26 (PDF 26–27)

import Mathlib
import Definitions.Def_GradedReserve_bidLaw
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- The law of the action profile when bidder `j` uses the mixed strategy `σ j` (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.4,
p.7, PDF 8: "independent private randomizations"; Section B conventions, pp.25–26, PDF 26–27):
values are i.i.d. with the value law `typeMeasure f`, each bidder draws its action from its own
Markov kernel, independently across bidders, so the profile law is the product of the bidders'
action laws `bidLaw f (σ j)`.

**Formalization Note.** Asymmetric profiles are allowed: every bidder has its own kernel. Actions
in `[0, 1]` are bids, and negative actions are the exit action, as in the base mission's
`GradedReserve.bidLaw`. -/
noncomputable def profileLaw {n : ℕ} (f : ℝ → ℝ) (σ : Fin n → Kernel ℝ ℝ) :
    Measure (Fin n → ℝ) :=
  Measure.pi fun j => bidLaw f (σ j)

end GradedReserve.Supplement


