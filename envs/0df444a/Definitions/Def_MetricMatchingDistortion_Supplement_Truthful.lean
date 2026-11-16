-- Prove2me | Definitions.Def_MetricMatchingDistortion_Supplement_Truthful
-- name    : MetricMatchingDistortion_Supplement_Truthful
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:03:28.734514+00:00
-- url     : https://prove2.me/theorems/b09d0b6e-dffd-4400-a09e-288e6b17d0b6
-- title:
--   Truthful-in-expectation mechanisms; deterministic truthful and Pareto-optimal mechanisms
-- statement:
--   1. A randomized mechanism $M$ is **truthful-in-expectation** (Definition 2.1) if for every instance $\sigma$, agent $a$, metric $d\in\rho(\sigma)$ and instance $\sigma'$ that differs from $\sigma$ only in $a$'s ranking,
--   $$\mathbb E_{M\sim M(\sigma)}[d(a,M(a))]\le\mathbb E_{M\sim M(\sigma')}[d(a,M(a))].$$
--   2. A **deterministic mechanism** maps every ranking profile on $n$ agents and $n$ items to one perfect integral matching. It is **truthful** if no agent can obtain an item she strictly prefers (under her true ranking) by misreporting her ranking.
--   3. A perfect integral matching $M$ is **Pareto optimal** if there is no perfect integral matching $M'$ with $M'(a)=M(a)$ or $M'(a)\succ_a M(a)$ for every agent $a$ and $M'(a)\succ_a M(a)$ for at least one agent. A deterministic mechanism is Pareto optimal if all its outputs are.
--
--   These are the classes of mechanisms of Theorems 6 and 7.
--
--   **Formalization Note** Mechanisms see only the rankings. The metric $d$ in item 1 is consistent with the true profile $\sigma$. All conditions are required for every $n$.
-- source:
--   Charikar, Haqi, Hastings, Huang, Ramakrishnan, Sublinear Metric Distortion for Matching, arXiv:2611.05777 (held version, sha256 fdf3452b105082d6ff680c8a762ec950298417efdebeb216b721705a9802e0da), §2, Definition 2.1, p.10 (PDF p.12); Pareto optimality, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_MetricMatchingDistortion_Ranking
import Definitions.Def_MetricMatchingDistortion_IsConsistentPseudometric
import Definitions.Def_MetricMatchingDistortion_Mechanism

namespace MetricMatchingDistortion.Supplement

open MetricMatchingDistortion

/-- `E_{M∼A(σ)}[d(a, M(a))]`: agent `a`'s expected distance to her item under the mechanism `A`
on the ranking profile `rk` (§2, p.10, Definition 2.1). -/
noncomputable def agentExpectedCost (A : Mechanism) (n : ℕ) (rk : Ranking n)
    (d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ) (a : Fin n) : ℝ :=
  ∑ π : Equiv.Perm (Fin n), (A n rk π).toReal * d (Sum.inl a) (Sum.inr (π a))

/-- **Truthful-in-expectation (Definition 2.1).** Charikar et al., *Sublinear Metric Distortion for
Matching*, arXiv:2611.05777 (held version, sha256 fdf3452b…), Definition 2.1, p.10 (PDF p.12):
"A mechanism M is truthful-in-expectation if for every instance σ, agent a ∈ A, metric d ∈ ρ(σ),
and instance σ′ that differs from σ only in a's ranking,
E_{M∼M(σ)}[d(a, M(a))] ≤ E_{M∼M(σ′)}[d(a, M(a))]." (1)

For every `n`, every pair of ranking profiles `rk, rk'` on `n` agents that agree on every agent
other than `a`, and every pseudometric `d` consistent with the true profile `rk`, agent `a`'s
expected distance under `rk` is at most her expected distance under `rk'`.

**Formalization Note.** `rk'` may also equal `rk` (then (1) is trivial); "differs only in a's
ranking" is "agrees with `rk` on every other agent". -/
def IsTruthfulInExpectation (A : Mechanism) : Prop :=
  ∀ (n : ℕ) (rk rk' : Ranking n) (a : Fin n), (∀ a', a' ≠ a → rk' a' = rk a') →
    ∀ d : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ, IsConsistentPseudometric rk d →
      agentExpectedCost A n rk d a ≤ agentExpectedCost A n rk' d a

/-- A **deterministic matching mechanism** (§2, p.10 = PDF p.12): it maps the number `n` of agents
and a ranking profile on `n` agents and `n` items to one perfect integral matching.

**Formalization Note.** The input holds the rankings only (ordinal by its type). A deterministic
mechanism is the same as a randomized `Mechanism` whose outputs are point masses. -/
abbrev DetMechanism := ∀ n : ℕ, Ranking n → Equiv.Perm (Fin n)

/-- **Truthful deterministic mechanism** (§2, p.10 = PDF p.12): "A deterministic mechanism is
truthful if no agent can ever get a better outcome by misreporting her preferences."

For every `n`, every agent `a` and every pair of profiles `rk, rk'` that agree on every agent other
than `a`, agent `a` does not strictly prefer, under her true ranking `rk a`, the item she gets at
`rk'` to the item she gets at `rk`. -/
def IsDetTruthful (M : DetMechanism) : Prop :=
  ∀ (n : ℕ) (rk rk' : Ranking n) (a : Fin n), (∀ a', a' ≠ a → rk' a' = rk a') →
    ¬ Prefers rk a (M n rk' a) (M n rk a)

/-- **Pareto optimal perfect matching** (§2, p.11 = PDF p.13): "A perfect integral matching M is
Pareto optimal if there is no perfect integral matching M′ such that, for every agent a, either
M′(a) = M(a) or M′(a) ≻a M(a), with M′(a) ≻a M(a) for at least one agent." -/
def IsParetoOptimal {n : ℕ} (rk : Ranking n) (π : Equiv.Perm (Fin n)) : Prop :=
  ¬ ∃ π' : Equiv.Perm (Fin n), (∀ a, π' a = π a ∨ Prefers rk a (π' a) (π a)) ∧
      ∃ a, Prefers rk a (π' a) (π a)

/-- A deterministic mechanism is **Pareto optimal** when its output on every instance is a Pareto
optimal perfect matching (§2, p.11, and Theorem 7, p.67). -/
def IsParetoOptimalDet (M : DetMechanism) : Prop :=
  ∀ (n : ℕ) (rk : Ranking n), IsParetoOptimal rk (M n rk)

end MetricMatchingDistortion.Supplement


