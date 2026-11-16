-- Prove2me | Definitions.Def_GradedReserve_Supplement_IsBNE
-- name    : GradedReserve_Supplement_IsBNE
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:36:03.999014+00:00
-- url     : https://prove2.me/theorems/f03f844a-6305-4c45-9a8f-dd474617232a
-- title:
--   Bayes–Nash equilibrium (asymmetric and mixed allowed)
-- statement:
--   A **Bayes–Nash equilibrium** of a mechanism $M$ is a profile $(\sigma_1,\dots,\sigma_n)$ of mixed strategies, one per bidder, such that
--
--   1. for every value $v\in[0,1]$ and every bidder $i$, $\sigma_i(v)$ is a probability distribution over actions with no mass above $1$;
--   2. for every bidder $i$ and almost every type $v$, $\sigma_i(v)$ is a best response against the others: for every action $a$,
--   $$u_i(v,a)\le\int u_i(v,a')\,\sigma_i(v)(da').$$
--
--   Values are i.i.d. with law $F$ and randomizations are independent. With all $\sigma_i$ equal and $M=G_\pi$ this is the symmetric BNE of the base mission.
--
--   **Formalization Note** Best responses are required for almost every type, the paper's convention ("statements about types are understood up to F-null sets").
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, p.4 (PDF 5); Theorem 3.4, p.7 (PDF 8); Section B conventions, pp.25–26 (PDF 26–27)

import Mathlib
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_Supplement_profileLaw
import Definitions.Def_GradedReserve_Supplement_payoffAgainst
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- A Bayes–Nash equilibrium of the mechanism `M`, asymmetric and mixed strategies allowed
(Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, p.4, PDF 5: "Rational bidders are risk neutral and play a Bayes–Nash equilibrium";
Theorem 3.4, p.7, PDF 8: "each BNE …, including asymmetric and mixed ones"; Section B conventions,
pp.25–26, PDF 26–27). Bidder `i` uses the Markov kernel `σ i` from values to actions; for every
value in `[0, 1]`, `σ i v` is a probability measure with no mass above `1` (bids lie in `[0, 1]`,
negative actions are exit); values are i.i.d. with law `typeMeasure f`, randomizations are
independent; and for every bidder, almost every type best-responds: no action gives it a higher
expected utility than the expected utility of its own mixed action.

**Formalization Note.** Best responses are required for almost every type, as in the paper
("Statements about types are understood up to F-null sets", p.26). With all `σ i` equal and
`M = gradedMech n π`, this is the base mission's `GradedReserve.IsSymBNE f n π`: both use the same
action law, the same exit convention, and the same win probability with uniform ties. -/
def IsBNE {n : ℕ} (M : Mechanism n) (f : ℝ → ℝ) (σ : Fin n → Kernel ℝ ℝ) : Prop :=
  (∀ i, ∀ v ∈ Icc (0:ℝ) 1, IsProbabilityMeasure (σ i v) ∧ σ i v (Ioi 1) = 0) ∧
  ∀ i, ∀ᵐ v ∂(typeMeasure f), ∀ a : ℝ,
    payoffAgainst M (profileLaw f σ) i v a ≤ ∫ a', payoffAgainst M (profileLaw f σ) i v a' ∂(σ i v)

end GradedReserve.Supplement


