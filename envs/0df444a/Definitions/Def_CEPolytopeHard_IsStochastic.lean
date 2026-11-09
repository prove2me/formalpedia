-- Prove2me | Definitions.Def_CEPolytopeHard_IsStochastic
-- name    : CEPolytopeHard_IsStochastic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:26.124206+00:00
-- url     : https://prove2.me/theorems/39db0031-441a-45cf-8029-06928151e6e6
-- title:
--   Stochastic matrix and stationary distribution
-- statement:
--   A square matrix $P$ indexed by a finite set is **stochastic** (a Markov chain transition function $P : [k] \to \Delta([k])$) when $P_{ij} \ge 0$ and $\sum_j P_{ij} = 1$ for every $i$. A vector $\mu$ is a **stationary distribution** of $P$ when $\mu_i \ge 0$, $\sum_i \mu_i = 1$ and
--   $$
--   \mu P = \mu, \qquad \text{i.e. } \sum_i \mu_i P_{ij} = \mu_j \text{ for every } j.
--   $$
--   These notions enter Definition 3.2 and all of Section 3.2.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Definition 3.2, p.13 and Section 3.2, p.15

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- A **stochastic matrix** (Markov chain transition function `P : [k] → ∆([k])`,
Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria
Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256
6aec500a…7820, Definition 3.2, p.13, and Section 3.2, p.15): nonnegative entries and rows summing
to `1`. -/
def IsStochastic {κ : Type*} [Fintype κ] (P : Matrix κ κ ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ ∀ i, ∑ j, P i j = 1

/-- A **stationary distribution** `μ` of `P` (Definition 3.2, p.13): a probability vector with
`μ P = μ`. -/
def IsStationary {κ : Type*} [Fintype κ] (P : Matrix κ κ ℝ) (μ : κ → ℝ) : Prop :=
  (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1 ∧ ∀ j, ∑ i, μ i * P i j = μ j

end CEPolytopeHard


