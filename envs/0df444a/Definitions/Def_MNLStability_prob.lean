-- Prove2me | Definitions.Def_MNLStability_prob
-- name    : MNLStability_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:46.767103+00:00
-- url     : https://prove2.me/theorems/d2d1d8e5-0271-44cb-a796-0f4314ca3f20
-- title:
--   Probabilities of events of the demand process, and unit consumption probabilities
-- statement:
--   For a set $A$ of outcomes $(X,X_0)$:
--
--   1. $\Pr\bigl[(X^U(m),X^U_0(m))\in A\bigr]$ is the probability for a fixed number $m$ of customers;
--   2. for a random number of customers with law $p_M$, independent of the choices, $\Pr[(X^U,X^U_0)\in A]=\sum_{m}p_M(m)\Pr[(X^U(m),X^U_0(m))\in A]$.
--
--   The units of product $i$ are offered in the order $(i,1),(i,2),\dots$, so **unit $(i,u)$ is consumed** exactly when at least $u$ units of $i$ are consumed. Hence
--
--   $$\Pr\bigl[I^U_{(i,u)}=1\bigr]=\Pr\bigl[X_i^U\ge u\bigr].$$
--
--   These are the consumption probabilities of §2.2 and the events of Lemma 12.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §2.2, p.11 (unit indexing); §5.1–5.2, pp.25–27

import Mathlib
import Definitions.Def_MNLStability_demand

namespace MNLStability

variable {n : ℕ}

/-- The probability that the outcome `(X, X₀)` of the demand process with `m` customers, started
from `U` under the weights `wts`, lies in the set `A` (SSRN:3498325, §5.1–5.2, pp.25–27, where `m`
is deterministic). -/
noncomputable def prob (wts : Weights n) (U : Fin n → ℕ) (m : ℕ)
    (A : Set ((Fin n → ℕ) × ℕ)) : ℝ :=
  ((demand wts U m).toOuterMeasure A).toReal

/-- The same probability when the number of customers `M` is random with law `pM`:
`Pr[(X, X₀) ∈ A] = Σ_{m ∈ supp M} Pr[M = m] · Pr[(X(m), X₀(m)) ∈ A]` (M independent of the choices,
§1.1, p.3). -/
noncomputable def probM (wts : Weights n) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ)
    (A : Set ((Fin n → ℕ) × ℕ)) : ℝ :=
  ∑ m ∈ pM.support, pM m * prob wts U m A

/-- `Pr[I^U_{(i,u)} = 1]`, the probability that unit `(i, u)` of product `i` is consumed when the
initial inventory vector is `U` (SSRN:3498325, §2.2, p.11): units of a product are allocated in the
order `(i,1), (i,2), …`, so unit `(i, u)` is consumed exactly when at least `u` units of `i` are. -/
noncomputable def unitProb (wts : Weights n) (pM : ℕ →₀ ℝ) (U : Fin n → ℕ) (i : Fin n) (u : ℕ) :
    ℝ :=
  probM wts pM U {x | u ≤ x.1 i}

end MNLStability


