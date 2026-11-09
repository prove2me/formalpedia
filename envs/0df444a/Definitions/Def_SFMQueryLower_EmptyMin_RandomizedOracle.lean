-- Prove2me | Definitions.Def_SFMQueryLower_EmptyMin_RandomizedOracle
-- name    : SFMQueryLower_EmptyMin_RandomizedOracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:21:47.519541+00:00
-- url     : https://prove2.me/theorems/3d4a6c11-25b8-4249-ba42-120b3cdcc386
-- title:
--   General randomized oracle strategies and extended query expectations
-- statement:
--   A randomized oracle strategy consists of an arbitrary probability space $(\Omega,\mathcal F,\mu)$ and a causal strategy $B_\omega$ for each seed $\omega$. The seed law is chosen independently of the oracle. For each fixed oracle, individual issued-query events and returned-output events are measurable. No topology on real replies and no measurability jointly over all oracles is required.
--
--   For a predicate $p$ on the finite query set,
--   $$\mathbb E_\mu Q_p(B_\omega,f)=\sum_{t\ge0}\mu\{\omega:\exists S,\ \operatorname{issued}(B_\omega,f,t)=S\text{ and }p(S)\}.$$
--   This nonnegative series preserves infinite expectation. The probability of ever querying a fixed set is also defined from actual issues. This layer separates reusable randomness and expectation from the paper's input class.
--
--   **Formalization Note** Arbitrary measurable seed laws, infinite random tapes, unbounded stopping, and infinite costs are allowed. The series equals the extended integral of the issue count by Tonelli for the finite query sets used here.
-- source:
--   James Fox, Randomized Query Lower Bounds for Submodular Function Minimization, STOC 2027 submission #292 (October 2026), Definition 1.1, printed p. 2 / PDF p. 3; Corollary 2.4, printed p. 8 / PDF p. 9

import Definitions.Def_SFMQueryLower_EmptyMin_OracleStrategy

set_option autoImplicit false
open scoped ENNReal

namespace SFMQueryLower.EmptyMin

open MeasureTheory

/-- An arbitrary probability seed chooses a causal strategy independently of the input.
Only observable query and output events must be measurable; no regularity of real replies
or joint measurability in the oracle is imposed. No halting or finite-cost assumption is made. -/
structure RandomizedOracle (Query Reply Output : Type) where
  Seed : Type
  seedMeasurable : MeasurableSpace Seed
  law : @Measure Seed seedMeasurable
  probability : @IsProbabilityMeasure Seed seedMeasurable law
  choose : Seed → OracleStrategy Query Reply Output
  measurable_issue : ∀ (f : Query → Reply) (t : ℕ) (S : Query),
    @MeasurableSet Seed seedMeasurable {ω | issuedQuery (choose ω) f t = some S}
  measurable_return : ∀ (f : Query → Reply) (a : Output),
    @MeasurableSet Seed seedMeasurable {ω | Returns (choose ω) f a}

/-- Expectation of the actual issue count as a nonnegative series. For finite query types,
the events are measurable; Tonelli gives the extended expectation of `queryCount`.
This formula retains `∞` and does not use a Bochner integral or `toReal`. -/
noncomputable def expectedCount {Query Reply Output : Type}
    (A : RandomizedOracle Query Reply Output) (f : Query → Reply)
    (p : Query → Prop) : ℝ≥0∞ :=
  ∑' t : ℕ, A.law {ω | ∃ S, issuedQuery (A.choose ω) f t = some S ∧ p S}

noncomputable def queryProbability {Query Reply Output : Type}
    (A : RandomizedOracle Query Reply Output) (f : Query → Reply) (S : Query) : ℝ≥0∞ :=
  A.law {ω | Queries (A.choose ω) f S}

end SFMQueryLower.EmptyMin


