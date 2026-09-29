-- Prove2me | Definitions.Def_MarkovDriftMinorization
-- name    : MarkovDriftMinorization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-15T14:36:21.876502+00:00
-- url     : https://prove2.me/theorems/fa5eebef-de99-445f-a99d-6064b13be29f
-- title:
--   Small sets (minorization) and the geometric / polynomial drift conditions
-- statement:
--   The constructive tools of the source's Section 2, for a transition kernel $P$ on a state space $\mathsf{X}$.
--
--   **Small set (minorization condition, eq. (4))**: a set $C$ is small for $P$ if there exist an integer $n_0 \ge 1$, a real $\varepsilon > 0$ and a probability measure $Q$ such that
--
--   $$
--   P^{n_0}(x, A) \;\ge\; \varepsilon\, Q(A) \qquad \text{for all } x \in C \text{ and all measurable } A.
--   $$
--
--   **Geometric drift condition (eq. (5))** towards $C$, with constants $d, b$: the function $V$ is integrable under every $P(x, \cdot)$ and
--
--   $$
--   PV(x) - V(x) \;\le\; -d\, V(x) + b\, \mathbb{1}_C(x) \qquad \text{for all } x, \quad \text{where } PV(x) = \int V(y)\, P(x, dy).
--   $$
--
--   **Polynomial drift condition (eq. (6))**, with exponent $0 \le \tau < 1$: likewise with $-d\, V(x)^{\tau}$ in place of $-d\, V(x)$.
--
--   Drift and minorization are the standard constructive route to geometric and polynomial ergodicity in Markov chain Monte Carlo, and the hypotheses of the mission's Theorem 1.
--
--   **Formalization Note** The integrability of $V$ under each $P(x, \cdot)$ is part of each drift condition, so that $PV$ is genuinely defined rather than a vacuous convention.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Section 2 (arXiv v2 p. 4), eqs. (4), (5), (6)

import Definitions.Def_MarkovIterKernel
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Minorization (small sets) and the geometric / polynomial drift conditions.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §2:
eq. (4) (minorization), eq. (5) (geometric drift), eq. (6) (polynomial drift).
-/

open MeasureTheory ProbabilityTheory

namespace MarkovChainCLT

/-- **Minorization / small set** (Jones 2004 eq. (4)): `C` is small for `P` if there
are `n₀ ≥ 1`, `ε > 0` and a probability measure `Q` with
`P^{n₀}(x, A) ≥ ε Q(A)` for all `x ∈ C` and all measurable `A`. -/
def IsSmallSet {X : Type*} [MeasurableSpace X] (P : Kernel X X) (C : Set X) : Prop :=
  ∃ n₀ : ℕ, 1 ≤ n₀ ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Q : Measure X, IsProbabilityMeasure Q ∧
    ∀ x ∈ C, ∀ A : Set X, MeasurableSet A →
      ENNReal.ofReal ε * Q A ≤ (iterKernel P n₀) x A

/-- **Geometric drift condition** (Jones 2004 eq. (5)): `V` is integrable under every
`P(x, ·)` and `PV(x) - V(x) ≤ -d V(x) + b 1_C(x)` for all `x`.  (The integrability
conjunct is part of the condition: it rules out the vacuous reading where the
integral of a non-integrable `V` is junk.) -/
def GeoDriftCondition {X : Type*} [MeasurableSpace X] (P : Kernel X X) (V : X → ℝ)
    (d b : ℝ) (C : Set X) : Prop :=
  (∀ x, Integrable V (P x)) ∧
    ∀ x, (∫ y, V y ∂(P x)) - V x ≤ -d * V x + b * C.indicator (fun _ => (1 : ℝ)) x

/-- **Polynomial drift condition** (Jones 2004 eq. (6)):
`PV(x) - V(x) ≤ -d V(x)^τ + b 1_C(x)` for all `x`, with `V` integrable under every
`P(x, ·)`. -/
def PolyDriftCondition {X : Type*} [MeasurableSpace X] (P : Kernel X X) (V : X → ℝ)
    (d b τ : ℝ) (C : Set X) : Prop :=
  (∀ x, Integrable V (P x)) ∧
    ∀ x, (∫ y, V y ∂(P x)) - V x ≤ -d * V x ^ τ + b * C.indicator (fun _ => (1 : ℝ)) x

end MarkovChainCLT


