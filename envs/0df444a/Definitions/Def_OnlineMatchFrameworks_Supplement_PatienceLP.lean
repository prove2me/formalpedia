-- Prove2me | Definitions.Def_OnlineMatchFrameworks_Supplement_PatienceLP
-- name    : OnlineMatchFrameworks_Supplement_PatienceLP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:20:37.510829+00:00
-- url     : https://prove2.me/theorems/30df26d1-33ae-5dd6-bf4c-8af02eeb1f1f
-- title:
--   Linear program (5) for an arbitrary patience distribution
-- statement:
--   A star has one customer and $m$ items with weights $w_j$ and probabilities $p_j$. Let $q_\theta$ be the probability that the patience is at least $\theta$. Linear program (5) is
--
--   $$
--   \max\ \sum_{j=1}^mw_jp_j\sum_{\theta=1}^mx_{j\theta}
--   $$
--
--   subject to, for all $j,\theta\in\{1,\dots,m\}$,
--
--   1. $\sum_{\theta'=\theta}^mx_{j\theta'}\le s_\theta$ (5a);
--   2. $\sum_jx_{j\theta}\le s_\theta$ (5b);
--   3. $x_{j\theta}\ge0$,
--
--   where $s_1=1$ and $s_\theta=\frac{q_\theta}{q_{\theta-1}}\bigl(s_{\theta-1}-\sum_jp_jx_{j,\theta-1}\bigr)$ for $\theta\ge2$, the quotient being $0$ when both tails are $0$. An **optimal solution** is a feasible point of largest objective. The program relaxes the single-customer problem with unknown patience.
--
--   **Formalization Note** Attempts are natural numbers starting at $1$. Values of $x$ outside $\{1,\dots,m\}$ are never read.
-- source:
--   Brubach, Grammel, Ma & Srinivasan, Online Matching Frameworks under Stochastic Rewards, Product Ranking, and Unknown Patience, arXiv:1907.03963v6, §5.2, LP (5), pp.23–24

import Definitions.Def_OnlineMatchFrameworks_StarPolicy

open scoped BigOperators

namespace OnlineMatchFrameworks.Supplement

variable {U : Type*} [Fintype U]

/-- **`s_θ` of LP (5).** arXiv:1907.03963v6, (5c)–(5d), p.24: `s_1 = 1` and
`s_θ = (q_θ/q_{θ-1}) (s_{θ-1} - ∑_j p_j x_{j,θ-1})` for `θ ≥ 2`. Here `q θ = Pr[patience ≥ θ]` and the
single customer is `() : Unit`.

**Formalization Note.** Attempts are counted from 1, and the value at `θ = 0` is not used. The paper
reads `q_θ/q_{θ-1}` as `0` when both are `0`, which is Lean's `x/0 = 0`. -/
noncomputable def attemptProb (G : OnlineMatchFrameworks.Instance U Unit) (q : ℕ → ℝ)
    (x : U → ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | n + 2 => q (n + 2) / q (n + 1) *
      (attemptProb G q x (n + 1) - ∑ j, G.p j () * x j (n + 1))

/-- **The objective of LP (5).** arXiv:1907.03963v6, (5), p.23: `∑_j w_j p_j ∑_{θ=1}^m x_{jθ}`, `m = |U|`. -/
def patienceObjective (G : OnlineMatchFrameworks.Instance U Unit) (x : U → ℕ → ℝ) : ℝ :=
  ∑ j, G.w j * G.p j () * ∑ θ ∈ Finset.Icc 1 (Fintype.card U), x j θ

/-- **The feasible set of LP (5).** arXiv:1907.03963v6, (5a), (5b) and `x ≥ 0`, pp.23–24, with
`j ∈ U` and `θ ∈ {1,…,m}`, `m = |U|`. Values `x j θ` outside that range are never read. -/
structure IsPatienceFeasible (G : OnlineMatchFrameworks.Instance U Unit) (q : ℕ → ℝ)
    (x : U → ℕ → ℝ) : Prop where
  /-- (5a) -/
  suffix_le : ∀ j, ∀ θ ∈ Finset.Icc 1 (Fintype.card U),
    ∑ θ' ∈ Finset.Icc θ (Fintype.card U), x j θ' ≤ attemptProb G q x θ
  /-- (5b) -/
  attempt_le : ∀ θ ∈ Finset.Icc 1 (Fintype.card U), ∑ j, x j θ ≤ attemptProb G q x θ
  /-- `x ≥ 0` -/
  nonneg : ∀ j, ∀ θ ∈ Finset.Icc 1 (Fintype.card U), 0 ≤ x j θ

/-- **An optimal solution of LP (5).** arXiv:1907.03963v6, p.25: "we solve LP (5) to get an optimal
solution x*, along with the values s*". -/
def IsPatienceOptimal (G : OnlineMatchFrameworks.Instance U Unit) (q : ℕ → ℝ)
    (x : U → ℕ → ℝ) : Prop :=
  IsPatienceFeasible G q x ∧
    ∀ y, IsPatienceFeasible G q y → patienceObjective G y ≤ patienceObjective G x

end OnlineMatchFrameworks.Supplement


