-- Prove2me | Definitions.Def_BernoulliPoA_triples
-- name    : BernoulliPoA_triples
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:42:15.730022+00:00
-- url     : https://prove2.me/theorems/88dfab7b-75e2-4dfc-ba1e-292d60be2e2f
-- title:
--   The index set $\mathcal T$
-- statement:
--   The set of triples
--   $$
--   \mathcal T=\{(c,k,m):c\in\mathcal C\setminus\{c_0\},\ k\in\mathbb N_+,\ m\in\mathbb N\},
--   $$
--   to which condition (28) can be restricted, as it is trivial for the zero function $c_0$ and for $k=0$.
--
--   **Formalization Note** "$c\ne c_0$" is read as "$c$ is nonzero at some load $k\ge1$", because $c(0)$ is free in the mission's cost families.
-- source:
--   Cominetti et al., Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games, arXiv:1903.03309v8, display (30), p.19

import Mathlib

namespace BernoulliPoA

/-- **The index set `T`.** Cominetti et al., *Ordinary and Prophet Planning under Uncertainty in Bernoulli Congestion Games*, arXiv:1903.03309v8, §3.2, display (30), p.19: `T = {(c, k, m) : c ∈ C \ {c₀}, k ∈ ℕ₊, m ∈ ℕ}`.

**Formalization Note** "`c ≠ c₀`" is read as "`c` is nonzero at some load `≥ 1`", because `c 0` is free in `IsCostClass`. A triple is
`(c, k, m)` as an element of `(ℕ → ℝ) × ℕ × ℕ`. -/
def triples (C : Set (ℕ → ℝ)) : Set ((ℕ → ℝ) × ℕ × ℕ) :=
  {t | t.1 ∈ C ∧ (∃ j, 1 ≤ j ∧ t.1 j ≠ 0) ∧ 1 ≤ t.2.1}

end BernoulliPoA


