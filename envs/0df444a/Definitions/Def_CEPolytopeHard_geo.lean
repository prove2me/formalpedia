-- Prove2me | Definitions.Def_CEPolytopeHard_geo
-- name    : CEPolytopeHard_geo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:28.18878+00:00
-- url     : https://prove2.me/theorems/53507947-4470-4671-a24b-dc8d3a85695c
-- title:
--   Geometric mixture $P(t) = t(I - (1-t)P)^{-1}$
-- statement:
--   For a stochastic matrix $P$ and $0 < t \le 1$,
--   $$
--   P(t) := \mathbb E_{a \sim \mathrm{Geo}(t)} P^a = t \sum_{a=0}^\infty (1-t)^a P^a = t\big(I - (1-t)P\big)^{-1},
--   $$
--   the transition matrix of running $P$ for a geometric number of steps; $P(1) = I$. It is the basic object of the support-amplification argument of Section 3.2.
--
--   **Formalization Note** The printed closed form is used. For stochastic $P$ and $0 < t \le 1$ the matrix $I - (1-t)P$ is invertible (Lean's matrix inverse would return $0$ only for a singular matrix).
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 3.2, p.15

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **geometric mixture `P(t)`** of the powers of a transition matrix
(Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria
Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256
6aec500a…7820, Section 3.2, p.15: "For a parameter 0 < t ≤ 1, we define
P(t) := E_{a∼Geo(t)} P^a = t ∑_{a=0}^∞ (1 − t)^a P^a = t(I − (1 − t)P)^{−1}"), in the printed closed
form `P(t) = t (I − (1 − t) P)⁻¹`; `P(1) = I`.

**Formalization Note** For a stochastic `P` and `0 < t ≤ 1` the matrix `I − (1 − t)P` is
invertible; Lean's `Matrix.inv` returns `0` for a singular matrix, which does not occur in that
range. -/
noncomputable def geo {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) (t : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  t • (1 - (1 - t) • P)⁻¹

end CEPolytopeHard


