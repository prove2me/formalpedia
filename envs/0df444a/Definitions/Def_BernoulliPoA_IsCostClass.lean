-- Prove2me | Definitions.Def_BernoulliPoA_IsCostClass
-- name    : BernoulliPoA_IsCostClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:10.880451+00:00
-- url     : https://prove2.me/theorems/7fa63603-a21b-486e-ace7-f8dbff354cbb
-- title:
--   Family of nonnegative nondecreasing cost functions
-- statement:
--   A family $\mathcal C$ of functions $c:\mathbb N\to\mathbb R$ is a **family of cost functions** when every $c\in\mathcal C$ is nonnegative and nondecreasing on the positive loads:
--   $$
--   c(k)\ge 0\quad\text{and}\quad c(k)\le c(l)\qquad\text{for all } 1\le k\le l.
--   $$
--
--   This is the standing assumption on the costs of the paper, and every worst-case statement of the mission is uniform over such a family.
--
--   **Formalization Note** The value $c(0)$ is left free: no quantity of the mission reads it. A resource in a played strategy has load at least $1$, the binomial expectation reads $c(1+j)$ only, and $k\,c(k)$ vanishes at $k=0$.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, §2.1, p.10, and Definition 2, p.17

import Mathlib

namespace BernoulliPoA

/-- **Family of cost functions.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §2.1, p.10 (`c_e : ℕ → [0,∞)` nondecreasing) and Definition 2, p.17
("a family `C` of nonnegative and nondecreasing costs"): every `c ∈ C` is nonnegative and nondecreasing on the loads `k ≥ 1`.

**Formalization Note** The value `c 0` is unconstrained: no cost in this mission is ever read at load `0`. A resource in
a played strategy has load at least `1`, `binomExp` reads `c (1 + j)` only, and `k * c k` vanishes at `k = 0`. -/
def IsCostClass (C : Set (ℕ → ℝ)) : Prop :=
  ∀ c ∈ C, (∀ k, 1 ≤ k → 0 ≤ c k) ∧ ∀ k l, 1 ≤ k → k ≤ l → c k ≤ c l

end BernoulliPoA


