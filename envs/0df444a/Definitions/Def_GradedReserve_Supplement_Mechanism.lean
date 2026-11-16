-- Prove2me | Definitions.Def_GradedReserve_Supplement_Mechanism
-- name    : GradedReserve_Supplement_Mechanism
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:32:49.187064+00:00
-- url     : https://prove2.me/theorems/c6056048-7aa0-474e-9f72-dd3ecd46e106
-- title:
--   Sealed-bid single-item mechanism (expected allocation and payment)
-- statement:
--   A **sealed-bid single-item mechanism** for $n$ bidders is described by two functions of the action profile $x=(x_1,\dots,x_n)$: the probability $\mathrm{alloc}(x)_i$ that bidder $i$ receives the item and its expected payment $\mathrm{pay}(x)_i$, both after the mechanism's own randomization (an acceptance lottery, a uniform tie-break). Risk-neutral bidders care only about these two quantities.
--
--   An action in $[0,1]$ is a bid; every action outside $[0,1]$ is the **exit** action, which never wins and pays nothing in each mechanism of this mission.
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Section 2, "Mechanisms", p.4 (PDF 5)

import Mathlib
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- A sealed-bid single-item mechanism for `n` bidders, described by its expected outcome at each
action profile (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Section 2, "Mechanisms", p.4, PDF 5: "A mechanism collects sealed bids in
`[0, 1]`, allocates the item and charges payments; every bidder may stay out and pay nothing").
`alloc x i` is the probability that bidder `i` receives the item and `pay x i` its expected payment
when the action profile is `x`, after the mechanism's own randomization (an acceptance lottery,
uniform tie-breaking).

**Formalization Note.** Actions are real numbers: an action in `[0, 1]` is a bid, and every
action outside `[0, 1]` is treated as the exit action by the concrete mechanisms of this mission
(it never wins and pays nothing). Risk-neutral bidders care only about these expected quantities,
so a mechanism's internal lotteries need not be modelled further. -/
structure Mechanism (n : ℕ) where
  /-- probability that bidder `i` receives the item at the action profile `x` -/
  alloc : (Fin n → ℝ) → Fin n → ℝ
  /-- expected payment of bidder `i` at the action profile `x` -/
  pay : (Fin n → ℝ) → Fin n → ℝ

end GradedReserve.Supplement


