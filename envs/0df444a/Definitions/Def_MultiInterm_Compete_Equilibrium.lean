-- Prove2me | Definitions.Def_MultiInterm_Compete_Equilibrium
-- name    : MultiInterm_Compete_Equilibrium
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:41:47.891193+00:00
-- url     : https://prove2.me/theorems/b12552a2-f452-4b18-80eb-d27c2dc759e0
-- title:
--   Symmetric continuation equilibria and deterministic-reserve perfect Bayesian equilibrium
-- statement:
--   At any fixed reserve pair, all bidders use the same measurable strategy. Their bid functions are four strictly increasing functions of value: $b_A,b_B$ for single-homing and $b_A^M,b_B^M$ for multi-homing. The strategy may mix, with arbitrary value-dependent probabilities, between abstention, single-homing on either side, and multi-homing. A single-homer's other bid is zero or absent. No condition is imposed on attachments by this monotonicity hypothesis.
--
--   A continuation equilibrium is a Bayes–Nash equilibrium in which each bidder's action distribution at every type is weakly undominated against all opponent strategy profiles, and which satisfies this four-function hypothesis. No reserve best-response condition is imposed on a continuation equilibrium.
--
--   A symmetric perfect Bayesian equilibrium consists of deterministic reserves $r$ and a continuation strategy $\sigma$ after every reserve pair. It requires a continuation equilibrium for every pair, including off-path pairs, and intermediary best responses:
--   $$\Pi_\theta(r[\theta\leftarrow t];\sigma)\le\Pi_\theta(r;\sigma)\qquad(t\ge0).$$
--   Revenues after a deviation are computed using the strategy at the deviated reserves.
--
--   **Formalization Note** Since beliefs remain equal to the prior, the paper's PBE reduces to these continuation and reserve optimality conditions. Reserve deviations are pure; a mixed deviation cannot improve on all pure deviations. Strict increase is required on the value support. The mode-mixture reading places no monotonicity restriction on participation. Truthful attachments, at-most-value bids, efficiency and reserve zero are not built into equilibrium.
-- source:
--   Ganesh, Moallemi, Weinberg, On the Power and Limitations of Multiple Intermediaries for Single-Item Auctions, STOC 2027 submission (sha256 bdc0557e98c014301646135a34b1532361d0f6133aa7832c59b68394fa2a81dc), pp. 7–10 (PDF 8–11), §2 and §3.1; p. 15 (PDF 16), §6.2 standing assumptions; Appendix A, pp. 27–28 (PDF 28–29)

import Definitions.Def_MultiInterm_Compete_CompositeGame

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiInterm.Compete

/-- The four bid functions describe bids, not participation or upstream attachments. -/
structure BidFunctions where
  singleA : ℝ≥0 → ℝ≥0
  singleB : ℝ≥0 → ℝ≥0
  multiA : ℝ≥0 → ℝ≥0
  multiB : ℝ≥0 → ℝ≥0

def BidFunctions.Increasing (b : BidFunctions) (D : ValueDistribution) : Prop :=
  StrictMonoOn b.singleA D.Types ∧ StrictMonoOn b.singleB D.Types ∧
  StrictMonoOn b.multiA D.Types ∧ StrictMonoOn b.multiB D.Types

/-- An inactive auction may receive no bid or a zero bid. Attachments remain unrestricted. -/
def ZeroOrAbsent (a : Option (ℝ≥0 × Option ℝ≥0)) : Prop :=
  a = none ∨ ∃ q, a = some (0, q)

def HasBid (a : Option (ℝ≥0 × Option ℝ≥0)) (x : ℝ≥0) : Prop :=
  ∃ q, a = some (x, q)

def BidFunctions.Mode (b : BidFunctions) (v : ℝ≥0) (a : Action) : Prop :=
  (a false = none ∧ a true = none) ∨
  (HasBid (a false) (b.singleA v) ∧ ZeroOrAbsent (a true)) ∨
  (ZeroOrAbsent (a false) ∧ HasBid (a true) (b.singleB v)) ∨
  (HasBid (a false) (b.multiA v) ∧ HasBid (a true) (b.multiB v))

/-- Arbitrary measurable, value-dependent mixtures over the four modes. -/
def BiddingAssumptions (D : ValueDistribution) (s : BidderStrategy) : Prop :=
  ∃ b : BidFunctions, b.Increasing D ∧
    ∀ v ∈ D.Types, ∀ᵐ a ∂s.kernel v, b.Mode v a

/-- Continuation BNE and typewise weak undominance; no reserve-player optimality here. -/
def BidderEquilibrium (D : ValueDistribution) (n : ℕ) (r : Reserves)
    (s : BidderStrategy) : Prop :=
  (CompositeGame D n r).IsBNE (fun _ => s) ∧
    ∀ i v, v ∈ D.Types → (CompositeGame D n r).Undominated i v (s.at v)

def Continuation (D : ValueDistribution) (n : ℕ) (r : Reserves)
    (s : BidderStrategy) : Prop :=
  BidderEquilibrium D n r s ∧ BiddingAssumptions D s

/-- Deterministic-reserve symmetric PBE. The prior does not change with reserves.
Both BNE and the four-function monotonicity requirement hold after every reserve pair. -/
def Equilibrium (D : ValueDistribution) (n : ℕ) (σ : SymmetricStrategy)
    (r : Reserves) : Prop :=
  (∀ q : Reserves, Continuation D n q (σ q)) ∧
    ∀ θ (s : ℝ≥0),
      revenue D n (σ (Function.update r θ s)) (Function.update r θ s) θ ≤
        revenue D n (σ r) r θ

end MultiInterm.Compete


